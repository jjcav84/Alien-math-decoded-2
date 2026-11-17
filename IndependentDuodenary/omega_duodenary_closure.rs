use std::convert::TryFrom;

const RING_ORDER: usize = 144;
const HARMONIC_PAIRS: usize = 12;
const MAX_ADDRESS_DIMENSIONS: usize = 256;
const MIN_ADDRESS_DIMENSIONS: usize = 2;
const MAX_WITNESS_DEPTH: usize = 4;
const FIXED_FOLD_DEPTH: usize = 1;
const RAW_MAX_TRANSIENT: usize = 3;
const RAW_MAX_CYCLE: usize = 2;

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum Error {
    NoncanonicalResidue12,
    NoncanonicalResidue144,
    InvalidAxis,
    InvalidAddressDimensions,
    WitnessDepthExceeded,
    OrbitBoundExceeded,
    UnexpectedAttractor,
    RawInvariantViolation,
    ProjectionInvariantViolation,
    FoldInvariantViolation,
    InverseViewViolation,
}

#[derive(Clone, Copy, Debug, Eq, PartialEq, Hash)]
pub struct Z12(u8);

impl TryFrom<u8> for Z12 {
    type Error = Error;
    fn try_from(value: u8) -> Result<Self, Error> {
        if value < 12 {
            Ok(Self(value))
        } else {
            Err(Error::NoncanonicalResidue12)
        }
    }
}

impl Z12 {
    pub const ZERO: Self = Self(0);
    pub fn value(self) -> u8 { self.0 }
    pub fn add(self, other: Self) -> Self {
        Self((u16::from(self.0) + u16::from(other.0)).rem_euclid(12) as u8)
    }
}

#[derive(Clone, Copy, Debug, Eq, PartialEq, Hash)]
pub struct Z144(u8);

impl TryFrom<u16> for Z144 {
    type Error = Error;
    fn try_from(value: u16) -> Result<Self, Error> {
        if value < 144 {
            Ok(Self(value as u8))
        } else {
            Err(Error::NoncanonicalResidue144)
        }
    }
}

impl Z144 {
    pub const ZERO: Self = Self(0);
    pub fn value(self) -> u8 { self.0 }
    fn reduce(value: u32) -> Self { Self((value % 144) as u8) }
    pub fn residue12(self) -> Z12 { Z12(self.0 % 12) }
    pub fn register_pair(self) -> (Z12, Z12) {
        (Z12(self.0 % 12), Z12(self.0 / 12))
    }
    pub fn from_register_pair(source: Z12, target: Z12) -> Self {
        Self(source.0 + 12 * target.0)
    }
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct Axis(u8);

impl TryFrom<u8> for Axis {
    type Error = Error;
    fn try_from(value: u8) -> Result<Self, Error> {
        if value < 12 { Ok(Self(value)) } else { Err(Error::InvalidAxis) }
    }
}

impl Axis {
    fn mirror(self) -> Self { Self(11 - self.0) }
}

// The exact operators in the recovered 24-axis execution sandbox:
// alpha_k(x) = (k+1)x mod 144; beta_k(x) = (12-k)x mod 144.
fn alpha(k: Axis, x: Z144) -> Z144 {
    Z144::reduce(u32::from(k.0 + 1) * u32::from(x.0))
}
fn beta(k: Axis, x: Z144) -> Z144 {
    Z144::reduce(u32::from(12 - k.0) * u32::from(x.0))
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct HarmonicPair {
    pub alpha_axis: u8,
    pub beta_axis: u8,
    pub alpha_value: Z144,
    pub beta_value: Z144,
    pub product: Z144,
}

fn harmonic_pair(k: Axis, x: Z144) -> HarmonicPair {
    let reflected = k.mirror();
    let a = alpha(k, x);
    let b = beta(reflected, x);
    HarmonicPair {
        alpha_axis: k.0,
        beta_axis: reflected.0,
        alpha_value: a,
        beta_value: b,
        product: Z144::reduce(u32::from(a.0) * u32::from(b.0)),
    }
}

pub fn harmonic_decomposition(x: Z144) -> [HarmonicPair; HARMONIC_PAIRS] {
    std::array::from_fn(|k| harmonic_pair(Axis(k as u8), x))
}

// The executable, unprojected direct-sum reduction.
pub fn direct_sum_kernel(x: Z144) -> Z144 {
    let mut sum: u32 = 0;
    for k in 0..HARMONIC_PAIRS {
        let term = harmonic_pair(Axis(k as u8), x);
        sum += u32::from(term.product.0);
    }
    Z144::reduce(sum)
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum Attractor {
    Zero,
    ThirtyTwo,
    Eighty,
}

impl Attractor {
    pub fn representative(self) -> Z144 {
        match self {
            Self::Zero => Z144(0),
            Self::ThirtyTwo => Z144(32),
            Self::Eighty => Z144(80),
        }
    }
    fn from_cycle_minimum(minimum: Z144) -> Result<Self, Error> {
        match minimum.0 {
            0 => Ok(Self::Zero),
            32 => Ok(Self::ThirtyTwo),
            80 => Ok(Self::Eighty),
            _ => Err(Error::UnexpectedAttractor),
        }
    }
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct OrbitCertificate {
    pub attractor: Attractor,
    pub transient: usize,
    pub period: usize,
}

// Finite-state orbit decomposition is exact; the loop limit is |Z/144Z|,
// not a heuristic iteration budget. Cycles are collapsed to their least residue.
pub fn fix(value: Z144) -> Result<OrbitCertificate, Error> {
    let mut first_seen = [None::<usize>; RING_ORDER];
    let mut orbit: Vec<Z144> = Vec::with_capacity(RING_ORDER);
    let mut current = value;
    for _ in 0..=RING_ORDER {
        if let Some(start) = first_seen[current.0 as usize] {
            let cycle = &orbit[start..];
            let minimum = cycle.iter().copied().min_by_key(|x| x.0)
                .ok_or(Error::OrbitBoundExceeded)?;
            let result = OrbitCertificate {
                attractor: Attractor::from_cycle_minimum(minimum)?,
                transient: start,
                period: cycle.len(),
            };
            if result.transient > RAW_MAX_TRANSIENT || result.period > RAW_MAX_CYCLE {
                return Err(Error::OrbitBoundExceeded);
            }
            return Ok(result);
        }
        if orbit.len() == RING_ORDER {
            return Err(Error::OrbitBoundExceeded);
        }
        first_seen[current.0 as usize] = Some(orbit.len());
        orbit.push(current);
        current = direct_sum_kernel(current);
    }
    Err(Error::OrbitBoundExceeded)
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct Transition {
    pub input: Z144,
    pub raw: Z144,
    pub output: Z144,
    pub certificate: OrbitCertificate,
}

// f(x) = fix(sum_k alpha_k(x) * beta_(11-k)(x) mod 144).
pub fn kernel_step(input: Z144) -> Result<Transition, Error> {
    let raw = direct_sum_kernel(input);
    let certificate = fix(raw)?;
    Ok(Transition {
        input,
        raw,
        output: certificate.attractor.representative(),
        certificate,
    })
}

// Independent arithmetic oracle. No call into alpha, beta, direct_sum_kernel,
// fix, or kernel_step: sum_{j=1}^{12} j^2 = 650 = 74 (mod 144).
fn independent_raw_oracle(input: Z144) -> Z144 {
    let x = u32::from(input.0);
    Z144::reduce(74 * x * x)
}

// Independent CRT basin classification: modulo 9 the dynamics is
// r -> 2r^2; the terminal recurrent classes are {0}, {5}, and {2,8}.
fn independent_projection_oracle(input: Z144) -> Attractor {
    match input.0 % 9 {
        0 | 3 | 6 => Attractor::Zero,
        4 | 5 => Attractor::ThirtyTwo,
        1 | 2 | 7 | 8 => Attractor::Eighty,
        _ => unreachable!(),
    }
}

pub fn verification_gate(t: &Transition) -> Result<(), Error> {
    if t.raw != independent_raw_oracle(t.input) {
        return Err(Error::RawInvariantViolation);
    }
    let expected = independent_projection_oracle(t.input);
    if t.output != expected.representative()
        || t.certificate.attractor != expected
    {
        return Err(Error::ProjectionInvariantViolation);
    }
    let expected_next = independent_projection_oracle(t.output);
    if expected_next.representative() != t.output {
        return Err(Error::FoldInvariantViolation);
    }
    let (transient, period) = independent_orbit_properties(t.raw)?;
    if t.certificate.transient != transient || t.certificate.period != period {
        return Err(Error::FoldInvariantViolation);
    }
    Ok(())
}

// Independent orbit analysis uses the algebraic polynomial, not the kernel.
fn independent_orbit_properties(input: Z144) -> Result<(usize, usize), Error> {
    let mut current = input;
    let mut transient = 0;
    while !matches!(current.0, 0 | 32 | 80 | 128) {
        if transient >= RAW_MAX_TRANSIENT {
            return Err(Error::OrbitBoundExceeded);
        }
        current = independent_raw_oracle(current);
        transient += 1;
    }
    let period = if matches!(current.0, 80 | 128) { 2 } else { 1 };
    Ok((transient, period))
}

// G-01: the complete address and its witness trajectory share one tree.
// No terminal coordinate is mistaken for an invertible path encoding.
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum G01 {
    Origin { coordinates: Box<[Z12]>, anchor: Z12 },
    Step { predecessor: Box<G01>, increment: Z12 },
}

impl G01 {
    pub fn origin(coordinates: Vec<Z12>, anchor: Z12) -> Result<Self, Error> {
        if !(MIN_ADDRESS_DIMENSIONS..=MAX_ADDRESS_DIMENSIONS).contains(&coordinates.len()) {
            return Err(Error::InvalidAddressDimensions);
        }
        Ok(Self::Origin { coordinates: coordinates.into_boxed_slice(), anchor })
    }

    pub fn append(self, increment: Z12) -> Result<Self, Error> {
        if self.depth() >= MAX_WITNESS_DEPTH {
            return Err(Error::WitnessDepthExceeded);
        }
        Ok(Self::Step { predecessor: Box::new(self), increment })
    }

    pub fn validate(&self) -> Result<(), Error> {
        match self {
            Self::Origin { coordinates, .. } => {
                if !(MIN_ADDRESS_DIMENSIONS..=MAX_ADDRESS_DIMENSIONS).contains(&coordinates.len()) {
                    Err(Error::InvalidAddressDimensions)
                } else {
                    Ok(())
                }
            }
            Self::Step { predecessor, .. } => {
                if self.depth() > MAX_WITNESS_DEPTH {
                    return Err(Error::WitnessDepthExceeded);
                }
                predecessor.validate()
            }
        }
    }

    pub fn depth(&self) -> usize {
        match self {
            Self::Origin { .. } => 0,
            Self::Step { predecessor, .. } => 1 + predecessor.depth(),
        }
    }

    fn origin_node(&self) -> &Self {
        match self {
            Self::Origin { .. } => self,
            Self::Step { predecessor, .. } => predecessor.origin_node(),
        }
    }

    fn increment_at(&self, index: usize) -> Option<Z12> {
        let depth = self.depth();
        if index >= depth {
            return None;
        }
        let mut remaining = depth - index - 1;
        let mut node = self;
        while remaining > 0 {
            node = match node {
                Self::Step { predecessor, .. } => predecessor,
                Self::Origin { .. } => return None,
            };
            remaining -= 1;
        }
        match node {
            Self::Step { increment, .. } => Some(*increment),
            Self::Origin { .. } => None,
        }
    }

    pub fn address(&self) -> Address<'_> { Address(self) }
    pub fn witness_path(&self) -> WitnessPath<'_> { WitnessPath(self) }
}

#[derive(Clone, Copy, Debug)]
pub struct Address<'a>(&'a G01);

#[derive(Clone, Copy, Debug)]
pub struct WitnessPath<'a>(&'a G01);

impl<'a> Address<'a> {
    pub fn coordinates(self) -> &'a [Z12] {
        match self.0.origin_node() {
            G01::Origin { coordinates, .. } => coordinates,
            G01::Step { .. } => unreachable!(),
        }
    }
    pub fn structure(self) -> &'a G01 { self.0 }
    pub fn witness_path(self) -> WitnessPath<'a> { WitnessPath(self.0) }
}

impl<'a> WitnessPath<'a> {
    pub fn anchor(self) -> Z12 {
        match self.0.origin_node() {
            G01::Origin { anchor, .. } => *anchor,
            G01::Step { .. } => unreachable!(),
        }
    }
    pub fn depth(self) -> usize { self.0.depth() }
    pub fn increment(self, index: usize) -> Option<Z12> {
        self.0.increment_at(index)
    }
    pub fn endpoint(self) -> Z12 {
        let mut result = self.anchor();
        for index in 0..self.depth() {
            if let Some(increment) = self.increment(index) {
                result = result.add(increment);
            }
        }
        result
    }
    pub fn structure(self) -> &'a G01 { self.0 }
    pub fn address(self) -> Address<'a> { Address(self.0) }
}

// The canonical address-path tuple contains all information required to
// reconstruct an inductive G01 tree. Zero-copy views remain distinct from the
// owned, lossless tuple representation.
pub type G01Tuple = (Vec<Z12>, Z12, Vec<Z12>);

// Encode an inductive tree by unwinding every constructor in chronological
// order; no terminal-coordinate compression or lost witness history.
pub fn encode_g01(tree: &G01) -> Result<G01Tuple, Error> {
    tree.validate()?;
    let address = tree.address();
    let path = tree.witness_path();
    let mut increments = Vec::with_capacity(path.depth());
    for index in 0..path.depth() {
        increments.push(
            path.increment(index).ok_or(Error::InverseViewViolation)?,
        );
    }
    Ok((address.coordinates().to_vec(), path.anchor(), increments))
}

// The inverse fold: each increment adds exactly one Step constructor.
// The constructor count equals the tuple's increment count.
pub fn decode_g01(tuple: &G01Tuple) -> Result<G01, Error> {
    let (coordinates, anchor, increments) = tuple;
    if increments.len() > MAX_WITNESS_DEPTH {
        return Err(Error::WitnessDepthExceeded);
    }
    let mut tree = G01::origin(coordinates.clone(), *anchor)?;
    for &increment in increments {
        tree = tree.append(increment)?;
    }
    Ok(tree)
}

// Induction over Step count proves the inverse laws:
// Base: decode(encode(Origin(C,a))) = Origin(C,a).
// Step: append preserves the predecessor and records exactly its new residue.
// Therefore decode(encode(T)) = T and encode(decode(U)) = U for all
// valid 2..=256-dimensional tuples with 0..=4 witness increments.
pub fn verify_g01_bijection(tree: &G01) -> Result<(), Error> {
    let tuple = encode_g01(tree)?;
    let decoded = decode_g01(&tuple)?;
    if &decoded != tree {
        return Err(Error::InverseViewViolation);
    }
    let encoded_again = encode_g01(&decoded)?;
    if encoded_again != tuple {
        return Err(Error::InverseViewViolation);
    }
    Ok(())
}

// Check both directions for a canonical tuple, including validation failures.
pub fn verify_g01_tuple(tuple: &G01Tuple) -> Result<(), Error> {
    let tree = decode_g01(tuple)?;
    let encoded = encode_g01(&tree)?;
    if &encoded != tuple {
        return Err(Error::InverseViewViolation);
    }
    let recovered = decode_g01(&encoded)?;
    if recovered != tree {
        return Err(Error::InverseViewViolation);
    }
    Ok(())
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct VerificationReceipt {
    pub checked_states: usize,
    pub maximum_raw_transient: usize,
    pub maximum_raw_period: usize,
    pub exact_projected_fixed_depth: usize,
    pub cycle_80_128_collapsed: bool,
}

// For every x, CRT gives g^3(x) in {0,32,80,128}; these are closed
// under g, with {80,128} a 2-cycle. P is constant on every g-cycle.
// Hence f=P∘g=P and f(f(x))=f(x) for all x in Z/144Z.
// Since f(1)=80 != 1, the least universal stabilization depth is N=1.
pub fn verify_entire_ring() -> Result<VerificationReceipt, Error> {
    let mut max_transient = 0;
    let mut max_period = 0;
    let mut observed = [false; 3];
    for value in 0..RING_ORDER {
        let x = Z144(value as u8);
        let t = kernel_step(x)?;
        verification_gate(&t)?;
        let (full_transient, _) = independent_orbit_properties(x)?;
        max_transient = max_transient.max(full_transient);
        max_period = max_period.max(t.certificate.period);
        observed[match t.certificate.attractor {
            Attractor::Zero => 0,
            Attractor::ThirtyTwo => 1,
            Attractor::Eighty => 2,
        }] = true;
        let mut y = x;
        for _ in 0..RAW_MAX_TRANSIENT {
            y = independent_raw_oracle(y);
        }
        if !matches!(y.0, 0 | 32 | 80 | 128) {
            return Err(Error::FoldInvariantViolation);
        }
        let fixed = independent_projection_oracle(x).representative();
        if independent_projection_oracle(fixed).representative() != fixed {
            return Err(Error::FoldInvariantViolation);
        }
        let (source, target) = x.register_pair();
        if Z144::from_register_pair(source, target) != x {
            return Err(Error::RawInvariantViolation);
        }
    }
    if max_transient != RAW_MAX_TRANSIENT || max_period != RAW_MAX_CYCLE
        || observed != [true, true, true]
        || independent_projection_oracle(Z144(1)).representative() == Z144(1)
        || independent_raw_oracle(Z144(80)) != Z144(128)
        || independent_raw_oracle(Z144(128)) != Z144(80)
    {
        return Err(Error::FoldInvariantViolation);
    }
    let example = G01::origin(vec![Z12(0), Z12(1)], Z12(0))?
        .append(Z12(3))?
        .append(Z12(4))?;
    verify_g01_bijection(&example)?;
    Ok(VerificationReceipt {
        checked_states: RING_ORDER,
        maximum_raw_transient: max_transient,
        maximum_raw_period: max_period,
        exact_projected_fixed_depth: FIXED_FOLD_DEPTH,
        cycle_80_128_collapsed: true,
    })
}

fn main() {
    match verify_entire_ring() {
        Ok(receipt) => println!("{receipt:?}"),
        Err(e) => {
            eprintln!("FAIL-CLOSED: {e:?}");
            std::process::exit(2);
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn exact_sum_and_all_attractors() {
        let receipt = verify_entire_ring().unwrap();
        assert_eq!(receipt.checked_states, 144);
        assert_eq!(receipt.maximum_raw_transient, 3);
        assert_eq!(receipt.maximum_raw_period, 2);
        assert_eq!(receipt.exact_projected_fixed_depth, 1);
    }

    #[test]
    fn all_24_axes_are_paired_once() {
        for x in 0u8..144 {
            let pairs = harmonic_decomposition(Z144(x));
            let mut forward = [false; 12];
            let mut mirrored = [false; 12];
            for pair in &pairs {
                forward[pair.alpha_axis as usize] = true;
                mirrored[pair.beta_axis as usize] = true;
                assert_eq!(pair.alpha_value, pair.beta_value);
            }
            assert!(forward.iter().all(|v| *v));
            assert!(mirrored.iter().all(|v| *v));
        }
    }

    #[test]
    fn independent_gate_rejects_mutations() {
        let mut t = kernel_step(Z144(1)).unwrap();
        t.raw = Z144(0);
        assert_eq!(verification_gate(&t), Err(Error::RawInvariantViolation));
        let mut t = kernel_step(Z144(1)).unwrap();
        t.output = Z144(32);
        assert_eq!(verification_gate(&t), Err(Error::ProjectionInvariantViolation));
    }

    #[test]
    fn g01_bijection_exact_and_zero_copy_views() {
        let tree = G01::origin(vec![Z12(2), Z12(9)], Z12(3)).unwrap()
            .append(Z12(4)).unwrap()
            .append(Z12(5)).unwrap();
        assert_eq!(tree.address().coordinates(), &[Z12(2), Z12(9)]);
        assert_eq!(tree.witness_path().endpoint(), Z12(0));
        assert_eq!(tree.witness_path().increment(0), Some(Z12(4)));
        assert_eq!(tree.witness_path().increment(1), Some(Z12(5)));
        let tuple = encode_g01(&tree).unwrap();
        assert_eq!(tuple, (vec![Z12(2), Z12(9)], Z12(3), vec![Z12(4), Z12(5)]));
        assert_eq!(decode_g01(&tuple).unwrap(), tree);
        assert_eq!(encode_g01(&decode_g01(&tuple).unwrap()).unwrap(), tuple);
        verify_g01_bijection(&tree).unwrap();
        verify_g01_tuple(&tuple).unwrap();
    }

    #[test]
    fn exhaustive_all_witness_residues_depths_and_anchors() {
        let mut tested: usize = 0;
        for anchor in 0u8..12 {
            for depth in 0..=MAX_WITNESS_DEPTH {
                for sequence in 0..12usize.pow(depth as u32) {
                    let mut n = sequence;
                    let mut increments = Vec::with_capacity(depth);
                    for _ in 0..depth {
                        increments.push(Z12((n % 12) as u8));
                        n /= 12;
                    }
                    let tuple = (
                        vec![Z12(anchor), Z12((anchor + 1) % 12)],
                        Z12(anchor),
                        increments,
                    );
                    let tree = decode_g01(&tuple).unwrap();
                    assert_eq!(encode_g01(&tree).unwrap(), tuple);
                    assert_eq!(decode_g01(&encode_g01(&tree).unwrap()).unwrap(), tree);
                    verify_g01_bijection(&tree).unwrap();
                    verify_g01_tuple(&tuple).unwrap();
                    tested += 1;
                }
            }
        }
        assert_eq!(tested, 12 * (1 + 12 + 144 + 1728 + 20736));
    }

    #[test]
    fn exhaustive_two_coordinate_residues_and_maximum_dimensions() {
        for a in 0u8..12 {
            for b in 0u8..12 {
                for anchor in 0u8..12 {
                    let tuple = (vec![Z12(a), Z12(b)], Z12(anchor), vec![]);
                    verify_g01_tuple(&tuple).unwrap();
                }
            }
        }
        for dimension in [2usize, 3, 256] {
            let coordinates = (0..dimension)
                .map(|i| Z12((i % 12) as u8))
                .collect::<Vec<_>>();
            let tuple = (coordinates, Z12(11), vec![Z12(0), Z12(11), Z12(6), Z12(0)]);
            verify_g01_tuple(&tuple).unwrap();
        }
    }

    #[test]
    fn g01_rejects_invalid_dimensions_and_depth() {
        assert_eq!(G01::origin(vec![Z12(1)], Z12(0)), Err(Error::InvalidAddressDimensions));
        let mut tree = G01::origin(vec![Z12(0), Z12(1)], Z12(0)).unwrap();
        for _ in 0..4 {
            tree = tree.append(Z12(1)).unwrap();
        }
        assert_eq!(tree.append(Z12(1)), Err(Error::WitnessDepthExceeded));
        assert_eq!(
            decode_g01(&(vec![Z12(1)], Z12(0), vec![])),
            Err(Error::InvalidAddressDimensions),
        );
        assert_eq!(
            decode_g01(&(vec![Z12(1); 257], Z12(0), vec![])),
            Err(Error::InvalidAddressDimensions),
        );
        assert_eq!(
            decode_g01(&(vec![Z12(1); 2], Z12(0), vec![Z12(1); 5])),
            Err(Error::WitnessDepthExceeded),
        );
    }

    #[test]
    fn closure_is_idempotent_and_nontrivial() {
        for value in 0u8..144 {
            let x = Z144(value);
            let projected = kernel_step(x).unwrap().output;
            assert_eq!(kernel_step(projected).unwrap().output, projected);
        }
        assert_ne!(kernel_step(Z144(1)).unwrap().output, Z144(1));
        assert_eq!(kernel_step(Z144(80)).unwrap().output, Z144(80));
        assert_eq!(kernel_step(Z144(128)).unwrap().output, Z144(80));
    }
}