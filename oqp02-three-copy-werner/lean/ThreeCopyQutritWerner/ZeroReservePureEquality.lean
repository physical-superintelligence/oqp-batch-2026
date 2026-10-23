module

public import ThreeCopyQutritWerner.ZeroReserveAlgebra
public import ThreeCopyQutritWerner.CoherentPencilSupport
public import ThreeCopyQutritWerner.RankOne

@[expose] public section


/-!
# The zero-local-entropy branch of reserve equality

A vanishing local purity deficit is converted to an actual product factor,
using the compound sum of squares. Two such rays at the same cut give a
literal two-dimensional local range for any weighted sum of their projections.
This closes the degenerate entropy branch only. It does not assert that a
rank-two reserve zero must have a vanishing local entropy deficit.
-/

noncomputable section

open scoped BigOperators Matrix ComplexConjugate

namespace ThreeCopyQutritWerner

/-- Vanishing rectangular 2×2 minors give an explicit outer-product factor,
including the zero matrix. -/
theorem zeroReserve_factor_of_minors_zero {m n : Type*}
    (A : Matrix m n ℂ)
    (h : ∀ i j k l, A i k * A j l - A i l * A j k = 0) :
    ∃ (x : m → ℂ) (y : n → ℂ), ∀ i j, A i j = x i * y j := by
  classical
  by_cases hz : A = 0
  · refine ⟨0, 0, ?_⟩
    intro i j
    simp [hz]
  · have hn : ∃ i j, A i j ≠ 0 := by
      by_contra hn
      push_neg at hn
      apply hz
      ext i j
      exact hn i j
    obtain ⟨i₀, j₀, hn⟩ := hn
    refine ⟨fun i => A i j₀, fun j => A i₀ j / A i₀ j₀, ?_⟩
    intro i j
    rw [mul_div_assoc', eq_div_iff hn]
    have hh := h i i₀ j j₀
    linear_combination hh

/-- Zero purity defect is a genuine rectangular rank-one factorization. -/
theorem zeroReserve_factor_of_gram_defect_zero {m n : Type*}
    [Fintype m] [Fintype n] (A : Matrix m n ℂ)
    (h : frobSq A ^ 2 - frobSq (Aᴴ * A) = 0) :
    ∃ (x : m → ℂ) (y : n → ℂ), ∀ i j, A i j = x i * y j := by
  have hnorm : frobSq (zeroReserveCompound A) = 0 := by
    have he := zeroReserveCompound_frobSq A
    rw [h] at he
    linarith
  have hz := matrix_eq_zero_of_frobSq_eq_zero (zeroReserveCompound A) hnorm
  apply zeroReserve_factor_of_minors_zero A
  intro i j k l
  have he := congrFun (congrFun hz (i, j)) (k, l)
  change (A i k * A j l - A i l * A j k) / 2 = 0 at he
  exact (div_eq_zero_iff).mp he |>.resolve_right (by norm_num)

/-- A unit ray with pure complementary reduction actually factors across the cut. -/
theorem zeroReserve_product_of_local_purity_one {L R : Type*}
    [Fintype L] [Fintype R] (u : L × R → ℂ)
    (hu : vecNormSq u = 1) (hp : frobSq (ptraceR (ketBra u u)) = 1) :
    ∃ (x : L → ℂ) (y : R → ℂ), ∀ l r, u (l, r) = x l * y r := by
  have hf : frobSq (zeroReserveCutFlatten u) ^ 2 -
      frobSq ((zeroReserveCutFlatten u)ᴴ * zeroReserveCutFlatten u) = 0 := by
    rw [zeroReserveCutFlatten_frobSq, zeroReserveCutFlatten_gram, hu]
    have ht : frobSq ((ptraceR (ketBra u u))ᵀ) = frobSq (ptraceR (ketBra u u)) := by
      simp only [frobSq, Matrix.transpose_apply]
      exact Finset.sum_comm
    rw [ht, hp]
    ring
  obtain ⟨y, x, h⟩ := zeroReserve_factor_of_gram_defect_zero (zeroReserveCutFlatten u) hf
  refine ⟨x, y, ?_⟩
  intro l r
  exact (h r l).trans (mul_comm _ _)

/-- Two rays that factor at site 1 occupy at most two local dimensions there,
for arbitrary complex weights on their projections. -/
theorem zeroReserve_localRange1_le_two_of_products
    {a b c : Type*} [Fintype a] [Fintype b] [Fintype c]
    (u v : a × b × c → ℂ) (x y : a → ℂ) (p q : b × c → ℂ)
    (hu : ∀ i r, u (i, r) = x i * p r)
    (hv : ∀ i r, v (i, r) = y i * q r) (z w : ℂ) :
    localRangeDim₁ (z • ketBra u u + w • ketBra v v) ≤ 2 := by
  rw [localRangeDim₁_eq_coherentFlatten_rank]
  apply (rank_le_iff_exists_mul _ 2).mpr
  refine ⟨Matrix.of (fun i k => ![x i, y i] k),
    Matrix.of (fun k t => ![z * p t.1 * conj (u t.2), w * q t.1 * conj (v t.2)] k), ?_⟩
  ext i t
  simp only [coherentFlatten₁, Matrix.add_apply, Matrix.smul_apply,
    smul_eq_mul, ketBra, Matrix.mul_apply, Fin.sum_univ_two, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Complex.star_def]
  rw [hu i t.1, hv i t.1]
  ring

/-- Actual pure local marginals give the physical thin-site conclusion. -/
theorem zeroReserve_localRange1_le_two_of_local_purity_one
    {a b c : Type*} [Fintype a] [Fintype b] [Fintype c]
    (u v : a × b × c → ℂ) (hu : vecNormSq u = 1) (hv : vecNormSq v = 1)
    (hpu : frobSq (ptrace₂₃ (ketBra u u)) = 1)
    (hpv : frobSq (ptrace₂₃ (ketBra v v)) = 1) (z w : ℂ) :
    localRangeDim₁ (z • ketBra u u + w • ketBra v v) ≤ 2 := by
  have hru : frobSq (ptraceR (ketBra u u)) = 1 := by
    simpa only [ptrace₂₃_ketBra_eq_ptraceR] using hpu
  have hrv : frobSq (ptraceR (ketBra v v)) = 1 := by
    simpa only [ptrace₂₃_ketBra_eq_ptraceR] using hpv
  obtain ⟨x, p, hx⟩ := zeroReserve_product_of_local_purity_one u hu hru
  obtain ⟨y, q, hy⟩ := zeroReserve_product_of_local_purity_one v hv hrv
  exact zeroReserve_localRange1_le_two_of_products u v x y p q hx hy z w

end ThreeCopyQutritWerner
