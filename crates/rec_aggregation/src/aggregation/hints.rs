//! Hint streams and the raw signatures' witnesses.

use super::cells::{cell_bytes, count, exponent_bytes, pack_16_bytes};
use super::error::AggregationError;
use leanvm_core::cpu::Program;
use primitives::field::F192;
use signatures::lean_sphincs::{LeanSphincsPublicKey, LeanSphincsSignature};
use signatures::lean_xmss::{LeanXmssPublicKey, LeanXmssSignature};
use signatures::{lean_sphincs, lean_xmss};

// Both schemes' one-time keys go through the guest's one WOTS+C walk: the same chain
// length, digits dispatched a group at a time, and the same address types
// (`signatures`' shared tweak). leanSPHINCS groups DIGIT_GROUP digits, the last chain
// alone; leanXMSS LX_DIGIT_GROUP, then the rest. A chain step's address leaves out the
// chain index in leanXMSS, where it follows the value.
pub(super) const DIGIT_GROUP: usize = 3;
/// The guest's `LX_DIGIT_GROUP`.
pub(super) const LX_DIGIT_GROUP: usize = 4;
/// The guest's `LX_WINDOW`: index bits a path dispatch covers.
pub(super) const LX_WINDOW: usize = 8;
const _: () = assert!(lean_sphincs::W * lean_sphincs::V == 128 && lean_sphincs::V % DIGIT_GROUP == 1);
const _: () = assert!(lean_xmss::W == lean_sphincs::W && !lean_xmss::V.is_multiple_of(LX_DIGIT_GROUP));
// A leaf index is the two layers' indices, which the guest dispatches on a window at a time.
const _: () = assert!(lean_xmss::LOG_LIFETIME == 32 && lean_xmss::LAYER_HEIGHT.is_multiple_of(LX_WINDOW));
// The guest reads the leanSPHINCS digest's fields as one bit string: its first call's
// two cells, then the low lane of its second call's first cell, where the bits past the
// fields are unused. It rebuilds the bottom tree's index from three layers' leaves.
const _: () = assert!(lean_sphincs::DIGEST_CALLS == 2 && lean_sphincs::DIGEST_BITS > 256);
const _: () = assert!(LEAN_SPHINCS_TAIL_BITS < 64 && lean_sphincs::LAYERS == 3);
const _: () = assert!(lean_sphincs::FORS_HEIGHT <= 64 && lean_sphincs::H <= 64);
// It places a FORS leaf at bit 6 of its address's `hi` field and a node index at bit
// 10, past the tree and the level (`SP_FLEAF_SHIFT`, `SP_FNODE_SHIFT`).
const _: () = assert!(lean_sphincs::fors_hi(0, 1) == 1 << 6 && lean_sphincs::fors_hi(0, 1 << 4) == 1 << 10);

/// The leanSPHINCS digest's field bits in its second call's output, the low bits of
/// its first lane.
const LEAN_SPHINCS_TAIL_BITS: usize = lean_sphincs::DIGEST_BITS - 256;

/// Named hint entries for a single sub-proof, ordered within each stream.
pub(super) type SubHints = Vec<(&'static str, Vec<F192>)>;

/// An edit to a node's hints: how a test hands the guest a witness the honest host
/// would not.
#[cfg(test)]
pub(super) type Forgery = Box<dyn FnOnce(&mut Hints)>;

#[cfg(test)]
thread_local! {
    /// The forgery the next node this thread aggregates gets.
    pub(super) static FORGE: std::cell::RefCell<Option<Forgery>> = const { std::cell::RefCell::new(None) };
}

/// One `hint_witness` stream: a name and its entries, in the order the guest
/// pops them.
#[derive(Default)]
pub(super) struct Hints(Vec<(String, Vec<Vec<F192>>)>);

impl Hints {
    pub(super) fn push(&mut self, name: &str, entry: Vec<F192>) {
        match self.0.iter_mut().find(|(n, _)| n == name) {
            Some((_, entries)) => entries.push(entry),
            None => self.0.push((name.to_string(), vec![entry])),
        }
    }

    /// Entry `i` of stream `name`, for a test to forge.
    #[cfg(test)]
    pub(super) fn entry_mut(&mut self, name: &str, i: usize) -> &mut Vec<F192> {
        let (_, entries) = self.0.iter_mut().find(|(n, _)| n == name).expect("a hinted stream");
        &mut entries[i]
    }

    pub(super) fn install(self, guest: &mut Program) {
        for (name, entries) in self.0 {
            guest.set_witness(name, entries);
        }
    }
}

/// The digits of a WOTS+C codeword as the guest dispatches on them: `group` at a
/// time, then the rest, each group's index little endian in base `CHAIN_LEN`, in the
/// exponent.
fn digit_hints(codeword: &[u8], size: usize) -> impl Iterator<Item = Vec<F192>> + '_ {
    codeword.chunks(size).map(|group| {
        let index = group
            .iter()
            .rev()
            .fold(0, |index, &digit| index * lean_xmss::CHAIN_LEN + digit as usize);
        vec![count(index)]
    })
}

/// The guest's `lx_constants` with the bottom digest's randomizer `rho`: `GEN ** s` for
/// every digit sum of a group, the chain indices neither zero nor a power of two, the
/// message, leaf and top-layer address cells, a chain step's at each position, the target
/// sum and the bounds of the digit groups, the last group and the path windows in the
/// exponent, then from `LXC_RHO` (the next cell whose place in a hashed block is not in
/// its tail) the rest of that digest's block after its 64 bytes: `rho`, its padding's
/// first byte and zeros, the last byte and the zero capacity. Then zeros to whole 8-cell
/// blocks of the cells but `rho`. Returns the cells and `LXC_RHO`.
pub(super) fn lean_xmss_constants(rho: F192) -> (Vec<F192>, usize) {
    let address = |tw| pack_16_bytes(&lean_xmss::address(&tw));
    let mut cells: Vec<F192> = (0..=LX_DIGIT_GROUP * (lean_xmss::CHAIN_LEN - 1)).map(count).collect();
    cells.extend(
        (1..lean_xmss::V)
            .filter(|i| !i.is_power_of_two())
            .map(|i| F192::new(i as u64, 0, 0)),
    );
    cells.push(address(lean_xmss::tweak(lean_xmss::TWEAK_MSG, 0, 0)));
    cells.push(address(lean_xmss::tweak(lean_xmss::TWEAK_LEAF, 0, 0)));
    cells.push(address(lean_xmss::tweak(0, lean_xmss::TOP, 0)));
    cells
        .extend((0..lean_xmss::CHAIN_LEN - 1).map(|s| address(lean_xmss::tweak(lean_xmss::TWEAK_CHAIN, 0, 0).step(s))));
    cells.push(count(lean_xmss::TARGET_SUM));
    cells.push(count(lean_xmss::CHAIN_LEN.pow(LX_DIGIT_GROUP as u32) - 1));
    cells.push(count(
        lean_xmss::CHAIN_LEN.pow((lean_xmss::V % LX_DIGIT_GROUP) as u32) - 1,
    ));
    cells.push(count((1 << LX_WINDOW) - 1));
    if cells.len() % 8 >= 5 {
        cells.resize(cells.len().next_multiple_of(8), F192::ZERO);
    }
    let at = cells.len();
    let pad_first = F192::new(u64::from(primitives::hash::PAD_FIRST), 0, 0);
    let pad_last = F192::new(u64::from(primitives::hash::PAD_LAST) << 56, 0, 0);
    cells.extend([rho, pad_first, F192::ZERO, F192::ZERO, pad_last]);
    cells.extend([F192::ZERO; 4]);
    cells.resize((cells.len() - 1).next_multiple_of(8) + 1, F192::ZERO);
    (cells, at)
}

/// The digest `pin_lx_constants` checks [`lean_xmss_constants`] against: Keccak-256 of
/// the first eight cells but the randomizer, then an overwrite duplex step for each eight
/// after, the first two cells of the last output.
pub(super) fn lean_xmss_constants_digest() -> [F192; 2] {
    let (mut cells, rho) = lean_xmss_constants(F192::ZERO);
    cells.remove(rho);
    let mut state = [0u64; 25];
    for (b, block) in cells.chunks(8).enumerate() {
        for (c, cell) in block.iter().enumerate() {
            [state[2 * c], state[2 * c + 1]] = [cell.c0, cell.c1];
        }
        if b == 0 {
            state[16] = u64::from(primitives::hash::PAD_FIRST) | u64::from(primitives::hash::PAD_LAST) << 56;
        }
        primitives::hash::keccak_f(&mut state);
    }
    [F192::new(state[0], state[1], 0), F192::new(state[2], state[3], 0)]
}

/// The cells the `KECCAK` blocks of a hash of `words` read, nine a block, block `k`'s at
/// `9k`: the previous output's cell XOR the message cell (the cell itself in the first
/// block), zero past the words. The guest's `lx_leaf` but its first two.
fn absorbed_reads(words: &[F192]) -> Vec<F192> {
    use leanvm_core::keccak::{RATE_CELLS, STATE_CELLS, cell_lanes};
    let blocks = 16 * words.len() / primitives::hash::RATE + 1;
    let mut bytes = cell_bytes(words.iter().copied());
    bytes.resize(blocks * primitives::hash::RATE + 16, 0);
    bytes[16 * words.len()] ^= primitives::hash::PAD_FIRST;
    bytes[blocks * primitives::hash::RATE - 1] ^= primitives::hash::PAD_LAST;
    let mut reads = vec![F192::ZERO; RATE_CELLS * blocks];
    let mut state = [F192::ZERO; STATE_CELLS];
    for k in 0..blocks {
        let (odd, first) = (k % 2 == 1, 17 * k / 2);
        let mut lanes = [0u64; 25];
        for (c, (lo, hi)) in cell_lanes(odd).into_iter().enumerate() {
            let mut cell = state[c];
            if c < RATE_CELLS {
                cell += pack_16_bytes(&bytes[16 * (first + c)..]);
                if first + c < words.len() {
                    reads[RATE_CELLS * k + c] = cell;
                }
            }
            if let Some(l) = lo {
                lanes[l] = cell.c0;
            }
            if let Some(h) = hi {
                lanes[h] = cell.c1;
            }
        }
        primitives::hash::keccak_f(&mut lanes);
        state = std::array::from_fn(|c| {
            let (lo, hi) = cell_lanes(k % 2 == 0)[c];
            F192::new(lo.map_or(0, |l| lanes[l]), hi.map_or(0, |h| lanes[h]), 0)
        });
    }
    reads
}

/// One leanXMSS signature's witness: its leaf index shifted by each multiple of
/// `LX_WINDOW` and those windows in the exponent, then per layer, bottom first, the
/// randomizer, the codeword's digits, the chain values they start from, and the
/// sibling of every node on the path.
pub(super) fn lean_xmss_hints(
    pk: &LeanXmssPublicKey,
    sig: &LeanXmssSignature,
    message: &lean_xmss::Message,
) -> Result<SubHints, AggregationError> {
    let pp = pk.public_param();
    let index = u64::from(sig.leaf_index());
    let windows = (0..lean_xmss::LOG_LIFETIME).step_by(LX_WINDOW).map(|s| index >> s);
    let mut hints: SubHints = vec![
        ("lx_index", windows.clone().map(|x| F192::new(x, 0, 0)).collect()),
        (
            "lx_windows",
            windows.map(|x| count((x % (1 << LX_WINDOW)) as usize)).collect(),
        ),
        (
            "lx_constants",
            lean_xmss_constants(pack_16_bytes(sig.bottom().randomizer())).0,
        ),
    ];
    let mut root: Vec<u8> = message.to_vec();
    let mut level = 0;
    for (layer, layer_sig) in [sig.bottom(), sig.top()].into_iter().enumerate() {
        let e = lean_xmss::layer_index(sig.leaf_index(), layer);
        let (codeword, reached) = lean_xmss::layer_root(pp, layer, e, &root, layer_sig, |pair| {
            hints.push((
                "lx_path",
                vec![pack_16_bytes(&pair[usize::from(index >> level & 1 == 0)])],
            ));
            level += 1;
        })
        .ok_or(AggregationError::MalformedRawSignature)?;
        if layer == 1 {
            hints.push(("randomizer", vec![pack_16_bytes(layer_sig.randomizer())]));
        }
        // The one-time leaf's words, whose blocks' reads the guest takes as advice. A chain
        // the codeword leaves no step of needs no start: its tip is that value.
        let mut words = vec![
            pack_16_bytes(pp),
            pack_16_bytes(&lean_xmss::address(&lean_xmss::tweak(
                lean_xmss::TWEAK_LEAF,
                lean_xmss::layer_hi(layer, 0),
                e,
            ))),
        ];
        for (i, (&x, value)) in codeword.iter().zip(layer_sig.chain_values()).enumerate() {
            let steps = lean_xmss::CHAIN_LEN - 1 - usize::from(x);
            words.push(pack_16_bytes(&lean_xmss::chain(
                pp,
                layer,
                e,
                i,
                x.into(),
                steps,
                *value,
            )));
        }
        hints.push(("lx_leaf", absorbed_reads(&words)[2..].to_vec()));
        hints.push(("lx_digits", digit_hints(&codeword, LX_DIGIT_GROUP).flatten().collect()));
        for (&x, value) in codeword.iter().zip(layer_sig.chain_values()) {
            if usize::from(x) < lean_xmss::CHAIN_LEN - 1 {
                hints.push(("chain_starts", vec![pack_16_bytes(value)]));
            }
        }
        root = reached.to_vec();
    }
    Ok(hints)
}

/// One leanSPHINCS signature's witness: the randomizer, the digest's bits past its
/// fields, each FORS tree's secret and the ordered children of every node on its
/// climb, its two top nodes last, then per layer, bottom first, the encoding counter,
/// the codeword digits (three at a time, in the exponent), the chain values they start
/// from, and the ordered children of every node on the key's path.
///
/// The guest derives the index and every FORS leaf from the digest itself, so
/// nothing here carries them. The signer's own message is not hinted either: it
/// rides its slot in the coverage table.
pub(super) fn lean_sphincs_hints(
    pk: &LeanSphincsPublicKey,
    sig: &LeanSphincsSignature,
    message: &lean_sphincs::Message,
) -> Result<SubHints, AggregationError> {
    let pp = pk.public_param();
    let mut hints: SubHints = vec![("sp_rand", vec![pack_16_bytes(sig.randomizer())])];
    let digest = lean_sphincs::message_digest_bytes(pp, sig.randomizer(), message);
    let (idx, leaves) = lean_sphincs::digest_fields(&digest);
    let lane = u64::from_le_bytes(digest[32..40].try_into().unwrap());
    hints.push((
        "sp_unused",
        exponent_bytes(lane >> LEAN_SPHINCS_TAIL_BITS, 64 - LEAN_SPHINCS_TAIL_BITS),
    ));
    for tree in sig.fors() {
        hints.push(("sp_fors_secrets", vec![pack_16_bytes(tree.secret())]));
    }
    // On every path the guest does not order a node and its sibling: it is handed the
    // two children in order and checks that the node it holds is the one its bit names.
    let ordered = |pair: &[lean_sphincs::Digest; 2]| vec![pack_16_bytes(&pair[0]), pack_16_bytes(&pair[1])];
    let fors_key = lean_sphincs::fors_recover(pp, idx, &leaves, sig.fors(), |pair| {
        hints.push(("sp_fors_nodes", ordered(pair)));
    });
    let mut signed = lean_sphincs::fors_key_bytes(&fors_key).to_vec();
    for (layer, layer_sig) in sig.layers().iter().enumerate() {
        let key = lean_sphincs::OtsKey::of_index(layer, idx);
        let (codeword, leaf) = lean_sphincs::wots_leaf(pp, &key, &signed, layer_sig.counter(), layer_sig.wots())
            .ok_or(AggregationError::MalformedRawSignature)?;
        hints.push(("sp_counter", exponent_bytes(u64::from(layer_sig.counter()), 32)));
        hints.extend(digit_hints(&codeword, DIGIT_GROUP).map(|entry| ("digits", entry)));
        for value in layer_sig.wots() {
            hints.push(("chain_starts", vec![pack_16_bytes(value)]));
        }
        let root = lean_sphincs::tree_fold(pp, &key, leaf, sig.path(layer), |pair| {
            hints.push(("siblings", ordered(pair)));
        });
        signed = root.to_vec();
    }
    Ok(hints)
}
