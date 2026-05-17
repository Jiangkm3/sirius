// =====================================================================
// Permutation argument support
// =====================================================================

use std::sync::Arc;

use halo2_proofs::{
    arithmetic::{CurveAffine, Field},
    halo2curves::ff::PrimeField,
    plonk::Any,
};

use crate::{
    commitment::CommitmentKey,
    nifs::sangria::{
        decider::{OpeningEntry, ResolvedQuery},
        Error, QueryLayout,
    },
    plonk::{permutation::PermutationData, PlonkStructure},
    polynomial::Query,
};

/// Active columns in the permutation argument: markers + all advice.
/// Index 0 is markers; indices 1..=num_advice are advice columns.
pub struct PermLayout {
    pub num_active: usize,
    pub marker_idx_in_perm_data: usize, // index of markers in PermutationData.columns
    pub advice_idx_in_perm_data: Vec<usize>, // for each advice col i, its index in PermutationData.columns
}

fn build_perm_layout(perm_data: &PermutationData, num_advice: usize) -> PermLayout {
    let mut marker_idx = None;
    let mut advice_indices = vec![None; num_advice];

    for (perm_data_idx, col) in perm_data.columns.iter().enumerate() {
        match col.column_type() {
            Any::Instance if col.index() == 0 => {
                marker_idx = Some(perm_data_idx);
            }
            Any::Advice(_) => {
                if col.index() < num_advice {
                    advice_indices[col.index()] = Some(perm_data_idx);
                }
            }
            _ => {}
        }
    }

    PermLayout {
        num_active: 1 + num_advice,
        marker_idx_in_perm_data: marker_idx.expect("markers column 0 must be in permutation"),
        advice_idx_in_perm_data: advice_indices
            .into_iter()
            .map(|opt| opt.expect("advice column must be in permutation"))
            .collect(),
    }
}

fn extract_sigma<const MARKERS_LEN: usize>(
    perm_data: &PermutationData,
    layout: &PermLayout,
    n: usize,
) -> Vec<Vec<(usize, usize)>> {
    // sigma[active_col_idx][row] = (target_active_col_idx, target_row)
    let mut sigma = vec![vec![(0usize, 0usize); n]; layout.num_active];

    // Helper: convert PermutationData index → active column index
    let perm_data_to_active = |perm_data_idx: usize| -> Option<usize> {
        if perm_data_idx == layout.marker_idx_in_perm_data {
            Some(0)
        } else {
            layout
                .advice_idx_in_perm_data
                .iter()
                .position(|&pdi| pdi == perm_data_idx)
                .map(|i| i + 1) // active idx 0 is markers, advice starts at 1
        }
    };

    // Markers: only first MARKERS_LEN rows are meaningful.
    let marker_mapping = &perm_data.mapping[layout.marker_idx_in_perm_data];
    for j in 0..MARKERS_LEN.min(n) {
        let (target_perm_idx, target_row) = marker_mapping[j];
        match perm_data_to_active(target_perm_idx) {
            Some(target_active) => sigma[0][j] = (target_active, target_row),
            None => sigma[0][j] = (0, j), // identity (target was removed)
        }
    }
    // Remaining marker rows are identity (markers only have MARKERS_LEN cells).
    for j in MARKERS_LEN..n {
        sigma[0][j] = (0, j);
    }

    // Advice columns.
    for (advice_idx, &perm_data_idx) in layout.advice_idx_in_perm_data.iter().enumerate() {
        let active_idx = advice_idx + 1;
        let mapping = &perm_data.mapping[perm_data_idx];
        for j in 0..n {
            let (target_perm_idx, target_row) = mapping[j];
            match perm_data_to_active(target_perm_idx) {
                Some(target_active) => sigma[active_idx][j] = (target_active, target_row),
                None => sigma[active_idx][j] = (active_idx, j), // identity
            }
        }
    }

    sigma
}

/// The cell-encoding offset. Must be a non-root-of-unity primitive element.
/// For BN254 Fr, `7` works.
fn permutation_delta<F: PrimeField>() -> F {
    F::from(7)
}

/// Result of permutation preprocessing.
pub struct PermutationParams<C: CurveAffine> {
    pub s_polys: Arc<Vec<Vec<C::ScalarExt>>>,
    pub id_polys: Arc<Vec<Vec<C::ScalarExt>>>,
    pub s_commitments: Vec<C>,
    pub id_commitments: Vec<C>,
    pub num_active: usize,
}

impl<C: CurveAffine> Clone for PermutationParams<C> {
    fn clone(&self) -> Self {
        Self {
            s_polys: Arc::clone(&self.s_polys),
            id_polys: Arc::clone(&self.id_polys),
            s_commitments: self.s_commitments.clone(),
            id_commitments: self.id_commitments.clone(),
            num_active: self.num_active,
        }
    }
}

/// Build permutation preprocessing.
///
/// Takes the circuit's permutation data and produces `s_i` and `id_i`
/// polynomials, committed.
pub fn build_permutation_params<C: CurveAffine, const MARKERS_LEN: usize>(
    S: &PlonkStructure<C::ScalarExt>,
    ck: &CommitmentKey<C>,
    omega: C::ScalarExt,
    num_advice: usize,
) -> Result<PermutationParams<C>, Error>
where
    C::ScalarExt: PrimeField,
{
    let n = 1usize << S.k;
    let delta = permutation_delta::<C::ScalarExt>();

    // Use post-rm_copy_constraints permutation data — only markers + advice participate.
    let perm_data = S
        .permutation_data
        .clone()
        .rm_copy_constraints(1..S.num_io.len());
    let layout = build_perm_layout(&perm_data, num_advice);
    let sigma = extract_sigma::<MARKERS_LEN>(&perm_data, &layout, n);

    // Active columns: column 0 is markers, columns 1..=num_advice are advice.
    let num_active = layout.num_active;

    // Build id_i(ω^j) = δ^i · ω^j for each active column i.
    let id_polys: Vec<Vec<C::ScalarExt>> = (0..num_active)
        .map(|i| {
            let delta_to_i = delta.pow_vartime([i as u64]);
            let mut omega_pow_j = C::ScalarExt::ONE;
            let mut col = Vec::with_capacity(n);
            for _ in 0..n {
                col.push(delta_to_i * omega_pow_j);
                omega_pow_j *= omega;
            }
            col
        })
        .collect();

    // Build s_i(ω^j) = δ^{σ(i,j).col} · ω^{σ(i,j).row}.
    let s_polys: Vec<Vec<C::ScalarExt>> = (0..num_active)
        .map(|i| {
            let mut col = Vec::with_capacity(n);
            for j in 0..n {
                let (target_col, target_row) = sigma[i][j];
                let encoded =
                    delta.pow_vartime([target_col as u64]) * omega.pow_vartime([target_row as u64]);
                col.push(encoded);
            }
            col
        })
        .collect();

    // Commit each.
    let s_commitments: Vec<C> = s_polys
        .iter()
        .map(|p| ck.commit(p))
        .collect::<Result<_, _>>()?;
    let id_commitments: Vec<C> = id_polys
        .iter()
        .map(|p| ck.commit(p))
        .collect::<Result<_, _>>()?;

    Ok(PermutationParams {
        s_polys: s_polys.into(),
        id_polys: id_polys.into(),
        s_commitments,
        id_commitments,
        num_active,
    })
}

// =====================================================================
// Prover: build the grand product Z
// =====================================================================

/// Build Z(ω^j) for j = 0..n.
///
/// Z(ω^0) = 1
/// Z(ω^{j+1}) = Z(ω^j) · num_j / denom_j
///
/// where:
///   num_j = Π_i (w_i(ω^j) + β · id_i(ω^j) + γ)
///   denom_j = Π_i (w_i(ω^j) + β · s_i(ω^j) + γ)
///
/// Uses batch inversion to compute all the denom_j^{-1} efficiently.
pub fn build_permutation_grand_product<F: PrimeField>(
    permuted_witness: &[Vec<F>], // length = permuted_columns.len(), each of length n
    id_polys: &[Vec<F>],
    s_polys: &[Vec<F>],
    beta: F,
    gamma: F,
    n: usize,
) -> Vec<F> {
    debug_assert_eq!(permuted_witness.len(), id_polys.len());
    debug_assert_eq!(permuted_witness.len(), s_polys.len());

    // Compute (numerator_j, denominator_j) for each j in [0, n).
    let mut nums = Vec::with_capacity(n);
    let mut denoms = Vec::with_capacity(n);

    for j in 0..n {
        let mut num = F::ONE;
        let mut denom = F::ONE;
        for i in 0..permuted_witness.len() {
            let w_at_j = permuted_witness[i][j];
            num *= w_at_j + beta * id_polys[i][j] + gamma;
            denom *= w_at_j + beta * s_polys[i][j] + gamma;
        }
        nums.push(num);
        denoms.push(denom);
    }

    for (j, denom) in denoms.iter().enumerate() {
        if denom.is_zero_vartime() {
            // Find which factor is zero.
            for i in 0..permuted_witness.len() {
                let factor = permuted_witness[i][j] + beta * s_polys[i][j] + gamma;
                if factor.is_zero_vartime() {
                    println!("Zero denom at row {}: column {} has w + β·s + γ = 0", j, i,);
                    println!("  w[{}][{}] = {:?}", i, j, permuted_witness[i][j]);
                    println!("  s[{}][{}] = {:?}", i, j, s_polys[i][j]);
                    println!("  β = {:?}, γ = {:?}", beta, gamma);
                }
            }
            panic!("Cannot construct Z: zero denominator at row {}", j);
        }
    }

    // Batch-invert the denominators.
    let denom_inv = batch_invert_field(denoms);

    // Build Z evaluations.
    let mut z = vec![F::ZERO; n];
    z[0] = F::ONE;
    for j in 0..(n - 1) {
        z[j + 1] = z[j] * nums[j] * denom_inv[j];
    }

    z
}

/// Batch-invert a vector of field elements via Montgomery's trick.
fn batch_invert_field<F: PrimeField>(mut vals: Vec<F>) -> Vec<F> {
    let n = vals.len();
    if n == 0 {
        return vals;
    }
    let mut prefix = vec![F::ONE; n];
    let mut acc = F::ONE;
    for i in 0..n {
        prefix[i] = acc;
        acc *= vals[i];
    }
    let acc_inv = acc.invert().unwrap();
    let mut acc = acc_inv;
    for i in (0..n).rev() {
        let val_inv = acc * prefix[i];
        acc *= vals[i];
        vals[i] = val_inv;
    }
    vals
}

// =====================================================================
// Compute Z(ω · X) shifted polynomial in evaluation form
// =====================================================================

/// Given Z(ω^j) for j in [0, n), produce Z_shifted(ω^j) = Z(ω^{j+1}).
///
/// In evaluation form, this is just a cyclic shift of the evaluations.
pub fn shift_by_omega<F: Clone>(z_evals: &[F]) -> Vec<F> {
    let n = z_evals.len();
    let mut shifted = Vec::with_capacity(n);
    for j in 0..n {
        shifted.push(z_evals[(j + 1) % n].clone());
    }
    shifted
}

// =====================================================================
// L_0(X) as evaluation-form polynomial on H
// =====================================================================

/// L_0(ω^j) = 1 if j == 0, else 0.
pub fn l_0_evals<F: PrimeField>(n: usize) -> Vec<F> {
    let mut v = vec![F::ZERO; n];
    v[0] = F::ONE;
    v
}

pub(crate) fn gather_openings_with_permutation<'a, C: CurveAffine>(
    queries: &'a [Query],
    layout: &QueryLayout,
    advice_evals: &'a [Vec<C::ScalarExt>],
    fixed_evals: &'a [Vec<C::ScalarExt>],
    selector_evals: &'a [Vec<C::ScalarExt>],
    advice_commitments: &'a [C],
    fixed_commitments: &'a [C],
    selector_commitments: &'a [C],
    e_evals: &'a [C::ScalarExt],
    e_commitment: &'a C,
    t_chunks_evals: &'a [Vec<C::ScalarExt>],
    t_commitments: &'a [C],
    z_evals: &'a [C::ScalarExt],
    z_commitment: &'a C,
    s_polys: &'a [Vec<C::ScalarExt>],
    s_commitments: &'a [C],
    id_polys: &'a [Vec<C::ScalarExt>],
    id_commitments: &'a [C],
    query_evals: &'a [C::ScalarExt],
    e_eval: C::ScalarExt,
    t_chunks_eval: &'a [C::ScalarExt],
    z_at_zeta: C::ScalarExt,
    s_at_zeta: &'a [C::ScalarExt],
    id_at_zeta: &'a [C::ScalarExt],
    n: usize,
) -> Vec<OpeningEntry<'a, C>> {
    let mut out = Vec::new();

    // Queries (advice/fixed/selector).
    for (i, q) in queries.iter().enumerate() {
        let (evals, commitment, offset): (&[_], C, usize) = match layout.resolve(q.index) {
            ResolvedQuery::Advice(idx) => (&advice_evals[idx], advice_commitments[idx], idx * n),
            ResolvedQuery::Fixed(idx) => (&fixed_evals[idx], fixed_commitments[idx], 0),
            ResolvedQuery::Selector(idx) => (&selector_evals[idx], selector_commitments[idx], 0),
        };
        out.push(OpeningEntry {
            coeffs: evals,
            commitment,
            eval: query_evals[i],
            generator_offset: offset,
        });
    }

    out.push(OpeningEntry {
        coeffs: e_evals,
        commitment: *e_commitment,
        eval: e_eval,
        generator_offset: 0,
    });

    for (i, t) in t_chunks_evals.iter().enumerate() {
        out.push(OpeningEntry {
            coeffs: t,
            commitment: t_commitments[i],
            eval: t_chunks_eval[i],
            generator_offset: 0,
        });
    }

    out.push(OpeningEntry {
        coeffs: z_evals,
        commitment: *z_commitment,
        eval: z_at_zeta,
        generator_offset: 0,
    });

    for (i, s) in s_polys.iter().enumerate() {
        out.push(OpeningEntry {
            coeffs: s,
            commitment: s_commitments[i],
            eval: s_at_zeta[i],
            generator_offset: 0,
        });
    }
    for (i, id) in id_polys.iter().enumerate() {
        out.push(OpeningEntry {
            coeffs: id,
            commitment: id_commitments[i],
            eval: id_at_zeta[i],
            generator_offset: 0,
        });
    }

    out
}

pub fn gather_commitments_with_permutation<C: CurveAffine>(
    queries: &[Query],
    layout: &QueryLayout,
    advice_commitments: &[C],
    fixed_commitments: &[C],
    selector_commitments: &[C],
    e_commitment: &C,
    t_commitments: &[C],
    z_commitment: &C,
    s_commitments: &[C],
    id_commitments: &[C],
) -> Vec<C> {
    let mut out = Vec::new();
    for q in queries {
        let c = match layout.resolve(q.index) {
            ResolvedQuery::Advice(i) => advice_commitments[i],
            ResolvedQuery::Fixed(i) => fixed_commitments[i],
            ResolvedQuery::Selector(i) => selector_commitments[i],
        };
        out.push(c);
    }
    out.push(*e_commitment);
    out.extend_from_slice(t_commitments);
    out.push(*z_commitment);
    out.extend_from_slice(s_commitments);
    out.extend_from_slice(id_commitments);
    out
}
