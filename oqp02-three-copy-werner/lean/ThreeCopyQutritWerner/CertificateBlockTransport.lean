module

public import ThreeCopyQutritWerner.CertificateIntertwinerTrace

@[expose] public section


/-! Exact original-metric positivity and literal repetition counts for complete frames. -/

noncomputable section

open scoped BigOperators Matrix ComplexOrder

namespace ThreeCopyQutritWerner

/-- Group a sum by the actual number of occurrences of each source type. -/
theorem certificate_sum_type_counts
    {f t : Type*} [Fintype f] [Fintype t] [DecidableEq t]
    (type : f → t) (count : t → ℕ)
    (hcount : ∀ a, (Finset.univ.filter (fun i => type i = a)).card = count a)
    (value : t → ℂ) :
    (∑ i, value (type i)) = ∑ a, (count a : ℂ) * value a := by
  rw [← Finset.sum_fiberwise' Finset.univ type value]
  simp only [Finset.sum_const, nsmul_eq_mul, hcount]

/-- Positivity of the actual quadratic-form blocks transfers through a spanning
intertwiner even when its full descendant Gram matrix is not block diagonal. -/
theorem certificate_posSemidef_of_block_intertwiner
    {n ι : Type*} {m : ι → Type*} [Fintype n] [DecidableEq n]
    [Fintype ι] [DecidableEq ι] [∀ i, Fintype (m i)] [∀ i, DecidableEq (m i)]
    (M : Matrix n n ℂ) (S : Matrix n (Σ i, m i) ℂ)
    (G A : ∀ i, Matrix (m i) (m i) ℂ)
    (hM : M.IsHermitian) (hS : Function.Surjective S.mulVec)
    (hG : ∀ i, (G i).PosDef) (hD : ∀ i, (G i * A i).PosSemidef)
    (hinter : M * S = S * Matrix.blockDiagonal' A) : M.PosSemidef := by
  have hGb := certificate_blockDiagonal_posDef G hG
  have hDb : (Matrix.blockDiagonal' G * Matrix.blockDiagonal' A).PosSemidef := by
    rw [← Matrix.blockDiagonal'_mul]
    exact certificate_blockDiagonal_posSemidef _ hD
  apply certificate_posSemidef_of_weighted_intertwiner M S
    (Matrix.blockDiagonal' G) (Matrix.blockDiagonal' G * Matrix.blockDiagonal' A)
    hM hS hGb hDb
  rw [Matrix.nonsing_inv_mul_cancel_left _ _
    ((Matrix.isUnit_iff_isUnit_det _).mp hGb.isUnit)]
  exact hinter

end ThreeCopyQutritWerner
