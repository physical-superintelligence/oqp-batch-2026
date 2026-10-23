module

public import ThreeCopyQutritWerner.CertificateIntertwinerPositivity
public import Mathlib.Data.Matrix.Block

@[expose] public section


/-! Positivity of finite blocks with differing dimensions, in their original metrics. -/

noncomputable section

open scoped BigOperators Matrix ComplexOrder

namespace ThreeCopyQutritWerner

/-- Multiplication by a dependent block diagonal matrix acts within each block. -/
theorem certificate_blockDiagonal_mulVec
    {ι : Type*} {m : ι → Type*} [Fintype ι] [DecidableEq ι]
    [∀ i, Fintype (m i)]
    (D : ∀ i, Matrix (m i) (m i) ℂ) (v : (Σ i, m i) → ℂ) (i : ι) (a : m i) :
    (Matrix.blockDiagonal' D *ᵥ v) ⟨i, a⟩ =
      (D i *ᵥ fun b => v ⟨i, b⟩) a := by
  simp [Matrix.mulVec, dotProduct, Fintype.sum_sigma,
    Matrix.blockDiagonal'_apply', dite_mul]

/-- The full quadratic form is exactly the sum of the physical block forms. -/
theorem certificate_blockDiagonal_form
    {ι : Type*} {m : ι → Type*} [Fintype ι] [DecidableEq ι]
    [∀ i, Fintype (m i)]
    (D : ∀ i, Matrix (m i) (m i) ℂ) (v : (Σ i, m i) → ℂ) :
    star v ⬝ᵥ (Matrix.blockDiagonal' D *ᵥ v) =
      ∑ i, star (fun a => v ⟨i, a⟩) ⬝ᵥ (D i *ᵥ fun a => v ⟨i, a⟩) := by
  simp only [dotProduct, Fintype.sum_sigma, Pi.star_apply,
    certificate_blockDiagonal_mulVec]

/-- A dependent block diagonal matrix is positive whenever each actual block is positive. -/
theorem certificate_blockDiagonal_posSemidef
    {ι : Type*} {m : ι → Type*} [Fintype ι] [DecidableEq ι]
    [∀ i, Fintype (m i)]
    (D : ∀ i, Matrix (m i) (m i) ℂ) (hD : ∀ i, (D i).PosSemidef) :
    (Matrix.blockDiagonal' D).PosSemidef := by
  apply Matrix.PosSemidef.of_dotProduct_mulVec_nonneg
  · change (Matrix.blockDiagonal' D)ᴴ = Matrix.blockDiagonal' D
    rw [Matrix.blockDiagonal'_conjTranspose]
    congr 1
    funext i
    exact (hD i).isHermitian.eq
  · intro v
    rw [certificate_blockDiagonal_form]
    exact Finset.sum_nonneg fun i _ => (hD i).dotProduct_mulVec_nonneg _

/-- Positive definiteness is retained with arbitrary finite block dimensions. -/
theorem certificate_blockDiagonal_posDef
    {ι : Type*} {m : ι → Type*} [Fintype ι] [DecidableEq ι]
    [∀ i, Fintype (m i)]
    (G : ∀ i, Matrix (m i) (m i) ℂ) (hG : ∀ i, (G i).PosDef) :
    (Matrix.blockDiagonal' G).PosDef := by
  apply (certificate_blockDiagonal_posSemidef G
    (fun i => (hG i).posSemidef)).posDef_iff_mulVec_injective.mpr
  intro v w h
  funext ⟨i, a⟩
  have hi : G i *ᵥ (fun b => v ⟨i, b⟩) = G i *ᵥ (fun b => w ⟨i, b⟩) := by
    funext b
    simpa only [certificate_blockDiagonal_mulVec] using congrFun h ⟨i, b⟩
  exact congrFun ((hG i).mulVec_injective hi) a

end ThreeCopyQutritWerner
