module

public import ThreeCopyQutritWerner.FirstSiteCutKernel
public import ThreeCopyQutritWerner.ThinFirstSitePencil

@[expose] public section


/-!
# Thin zero contractions with unrestricted input rays

The output ray lies in the actual thin plane. Its orthogonal input ray may
have an arbitrary third component. Off-plane blocks are retained and their
cut zeros are combined only through contractions of the original matrix.
-/

noncomputable section

open scoped BigOperators Matrix ComplexConjugate

namespace ThreeCopyQutritWerner

variable {b c : Type*} [Fintype b] [Fintype c] [DecidableEq b] [DecidableEq c]

theorem firstSiteContraction_offplane_cutForm_zero
    (C : Matrix (Fin 3 × b × c) (Fin 3 × b × c) ℂ) (hC : C.rank ≤ 2)
    (hz : endpointEnergy C = 0) (hrow : ∀ r q, C (2, r) q = 0)
    (x : Fin 3 → ℂ) (hx₂ : x 2 = 0) :
    cutForm (firstSiteContraction C x ![0, 0, 1]) = 0 := by
  let x₀ : Fin 3 → ℂ := ![x 0, 0, 0]
  let x₁ : Fin 3 → ℂ := ![0, x 1, 0]
  have he₀ : firstSiteContraction C x₀ ![0, 0, 1] =
      conj (x 0) • firstSiteBlock C 0 2 := by
    ext r s
    simp [firstSiteContraction_apply, x₀, Fin.sum_univ_three,
      firstSiteBlock, Matrix.submatrix_apply, Matrix.smul_apply, smul_eq_mul]
  have he₁ : firstSiteContraction C x₁ ![0, 0, 1] =
      conj (x 1) • firstSiteBlock C 1 2 := by
    ext r s
    simp [firstSiteContraction_apply, x₁, Fin.sum_univ_three,
      firstSiteBlock, Matrix.submatrix_apply, Matrix.smul_apply, smul_eq_mul]
  have h₀ : cutForm (firstSiteContraction C x₀ ![0, 0, 1]) = 0 := by
    rw [he₀, cutForm_smul,
      firstSiteBlock_cutForm_zero_of_thin_endpoint_zero C hC hz 2 hrow 0, mul_zero]
  have h₁ : cutForm (firstSiteContraction C x₁ ![0, 0, 1]) = 0 := by
    rw [he₁, cutForm_smul,
      firstSiteBlock_cutForm_zero_of_thin_endpoint_zero C hC hz 2 hrow 1, mul_zero]
  have he : x₀ + x₁ = x := by
    ext i
    fin_cases i <;> simp [x₀, x₁, hx₂]
  simpa only [he] using
    firstSiteContraction_cutForm_add_left C hC x₀ x₁ ![0, 0, 1] h₀ h₁

/-- Orthogonality is the sole input-ray restriction; its third component
is neither zero nor assumed to be supported in the output plane. -/
theorem firstSiteContraction_cutForm_zero_of_thin_orthogonal_free_input
    (C : Matrix (Fin 3 × b × c) (Fin 3 × b × c) ℂ) (hC : C.rank ≤ 2)
    (hz : endpointEnergy C = 0) (hrow : ∀ r q, C (2, r) q = 0)
    (x y : Fin 3 → ℂ) (hxy : braket x y = 0) (hx₂ : x 2 = 0) :
    cutForm (firstSiteContraction C x y) = 0 := by
  let yP : Fin 3 → ℂ := ![y 0, y 1, 0]
  let yQ : Fin 3 → ℂ := ![0, 0, y 2]
  have hxyP : braket x yP = 0 := by
    simpa [braket, Fin.sum_univ_three, yP, hx₂] using hxy
  have hP := firstSiteContraction_cutForm_zero_of_thin_orthogonal
    C hC hz hrow x yP hxyP hx₂ (by simp [yP])
  have heQ : firstSiteContraction C x yQ =
      y 2 • firstSiteContraction C x ![0, 0, 1] := by
    have hyQ : yQ = y 2 • (![0, 0, 1] : Fin 3 → ℂ) := by
      ext i
      fin_cases i <;> simp [yQ]
    rw [hyQ]
    simpa using firstSiteContraction_smul C x ![0, 0, 1] 1 (y 2)
  have hQ : cutForm (firstSiteContraction C x yQ) = 0 := by
    rw [heQ, cutForm_smul,
      firstSiteContraction_offplane_cutForm_zero C hC hz hrow x hx₂, mul_zero]
  have he : yP + yQ = y := by
    ext i
    fin_cases i <;> simp [yP, yQ]
  simpa only [he] using firstSiteContraction_cutForm_add_right C hC x yP yQ hP hQ

end ThreeCopyQutritWerner
