module

public import ThreeCopyQutritWerner.CertificateCarrierCoefficients
public import ThreeCopyQutritWerner.CertificateSectorProjectors

@[expose] public section


/-!
# Character sums multiplied by the two actual minor antisymmetrizers

The finite coefficient shifts are derived from physical matrix multiplication.
This connects the canonical character/antisymmetrizer formulas to weighted
permutation sums without a saved projector or rank assumption.
-/

noncomputable section

open scoped BigOperators Matrix

namespace ThreeCopyQutritWerner

/-- Multiplying a representation sum shifts its coefficients on the right. -/
theorem certificateRepresentationSum_mul_right
    {G n : Type*} [Group G] [Fintype G] [Fintype n]
    (A : G → Matrix n n ℂ) (w : G → ℂ)
    (hA : ∀ σ τ, A σ * A τ = A (σ * τ)) (τ : G) :
    (∑ σ, w σ • A σ) * A τ = ∑ σ, w (σ * τ⁻¹) • A σ := by
  simp only [Finset.sum_mul, Matrix.smul_mul, hA]
  refine Fintype.sum_equiv (Equiv.mulRight τ) _ _ ?_
  intro σ
  simp

/-- One exact antisymmetrizer gives the difference of two shifted coefficients. -/
theorem certificateRepresentationSum_mul_antisym
    {G n : Type*} [Group G] [Fintype G] [Fintype n] [DecidableEq n]
    (A : G → Matrix n n ℂ) (w : G → ℂ)
    (hA : ∀ σ τ, A σ * A τ = A (σ * τ)) (τ : G) :
    (∑ σ, w σ • A σ) * ((1 / 2 : ℂ) • (1 - A τ)) =
      ∑ σ, ((w σ - w (σ * τ⁻¹)) / 2) • A σ := by
  rw [Matrix.mul_smul, Matrix.mul_sub, Matrix.mul_one,
    certificateRepresentationSum_mul_right A w hA τ,
    ← Finset.sum_sub_distrib, Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro σ _
  rw [← sub_smul, smul_smul]
  congr 1
  ring

/-- The ordered product of two minor antisymmetrizers has four coefficient terms. -/
theorem certificateRepresentationSum_mul_two_antisym
    {G n : Type*} [Group G] [Fintype G] [Fintype n] [DecidableEq n]
    (A : G → Matrix n n ℂ) (w : G → ℂ)
    (hA : ∀ σ τ, A σ * A τ = A (σ * τ)) (s t : G) :
    (∑ σ, w σ • A σ) * ((1 / 2 : ℂ) • (1 - A s)) *
        ((1 / 2 : ℂ) • (1 - A t)) =
      ∑ σ, ((w σ - w (σ * s⁻¹) - w (σ * t⁻¹) +
        w (σ * t⁻¹ * s⁻¹)) / 4) • A σ := by
  rw [certificateRepresentationSum_mul_antisym A w hA s,
    certificateRepresentationSum_mul_antisym A _ hA t]
  apply Finset.sum_congr rfl
  intro σ _
  congr 1
  ring

/-- Physical character compression has the literal four-term rational coefficient. -/
theorem certificateCentralMatrix_two_antisym
    {k : ℕ} {n : Type*} [Fintype n] [DecidableEq n]
    (d : ℚ) (i j u v : Fin k) :
    certificateCentralMatrix d * certificateRegisterAntisym (n := n) i j *
        certificateRegisterAntisym u v =
      ∑ σ : Equiv.Perm (Fin k),
        (((certificateCharacter σ - certificateCharacter (σ * Equiv.swap i j) -
          certificateCharacter (σ * Equiv.swap u v) +
          certificateCharacter (σ * Equiv.swap u v * Equiv.swap i j)) / (4 * d) : ℚ) : ℂ) •
          (certificateRegisterPerm σ).permMatrix ℂ := by
  unfold certificateCentralMatrix certificateRegisterAntisym
  rw [certificateRepresentationSum_mul_two_antisym _ _ certificateRegisterMatrix_mul]
  simp only [Equiv.swap_inv]
  apply Finset.sum_congr rfl
  intro σ _
  congr 1
  push_cast
  simp only [div_eq_mul_inv, mul_inv_rev]
  ring

/-- The holomorphic carrier is a physical five-register permutation sum in source order. -/
theorem certificateHolomorphicCarrier_source_sum {n : Type*} [Fintype n] [DecidableEq n] :
    certificateHolomorphicCarrier (n := n) =
      ∑ p : Fin 120, (certificateCarrierWeight0 p : ℂ) •
        (certificateRegisterPerm (certificatePerm5 (certificateCarrierIndex0 p))).permMatrix ℂ := by
  rw [certificateHolomorphicCarrier_eq, certificateCentralMatrix_two_antisym]
  have hs : (Equiv.swap (3 : Fin 5) 4) * Equiv.swap 1 2 =
      (Equiv.swap 1 2) * Equiv.swap 3 4 := by decide
  have horder (σ : Equiv.Perm (Fin 5)) : σ * Equiv.swap 3 4 * Equiv.swap 1 2 =
      σ * Equiv.swap 1 2 * Equiv.swap 3 4 := by
    rw [mul_assoc, hs, ← mul_assoc]
  simp_rw [horder]
  rw [certificate_sum_perm5]
  refine Fintype.sum_equiv (Equiv.ofBijective certificateCarrierIndex0
    certificateCarrierIndex0_bijective).symm _ _ ?_
  intro p
  try simp only [Equiv.symm_symm, Equiv.ofBijective_apply]
  have hi : certificateCarrierIndex0
      ((Equiv.ofBijective certificateCarrierIndex0 certificateCarrierIndex0_bijective).symm p) = p :=
    (Equiv.ofBijective certificateCarrierIndex0 certificateCarrierIndex0_bijective).apply_symm_apply p
  rw [certificateCarrierWeight0_character, hi]

/-- The four-register auxiliary carrier uses the same checked original source weights. -/
theorem certificateAuxiliaryFourCarrier_source_sum {n : Type*} [Fintype n] [DecidableEq n] :
    certificateAuxiliaryFourCarrier (n := n) =
      ∑ p : Fin 24, (certificateCarrierWeight2 p : ℂ) •
        (certificateRegisterPerm (certificatePerm4 (certificateCarrierIndex2 p))).permMatrix ℂ := by
  rw [certificateAuxiliaryFourCarrier, certificateCentralMatrix_two_antisym]
  have hs : (Equiv.swap (2 : Fin 4) 3) * Equiv.swap 0 1 =
      (Equiv.swap 0 1) * Equiv.swap 2 3 := by decide
  have horder (σ : Equiv.Perm (Fin 4)) : σ * Equiv.swap 2 3 * Equiv.swap 0 1 =
      σ * Equiv.swap 0 1 * Equiv.swap 2 3 := by
    rw [mul_assoc, hs, ← mul_assoc]
  simp_rw [horder]
  rw [certificate_sum_perm4]
  refine Fintype.sum_equiv (Equiv.ofBijective certificateCarrierIndex2
    certificateCarrierIndex2_bijective).symm _ _ ?_
  intro p
  try simp only [Equiv.symm_symm, Equiv.ofBijective_apply]
  have hi : certificateCarrierIndex2
      ((Equiv.ofBijective certificateCarrierIndex2 certificateCarrierIndex2_bijective).symm p) = p :=
    (Equiv.ofBijective certificateCarrierIndex2 certificateCarrierIndex2_bijective).apply_symm_apply p
  rw [certificateCarrierWeight2_character, hi]

end ThreeCopyQutritWerner
