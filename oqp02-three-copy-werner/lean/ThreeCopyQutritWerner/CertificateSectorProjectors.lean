module

public import ThreeCopyQutritWerner.CertificateS3Projections
public import ThreeCopyQutritWerner.CertificateImageProjector

@[expose] public section


/-!
# The canonical auxiliary carrier projectors

The mixed carrier uses A12 minus the three-register alternator, followed by
A34. The auxiliary carrier uses E[22] and both minor antisymmetrizers. All
registers and rational normalizations are literal; no saved rank is assumed.
-/

noncomputable section

open scoped BigOperators Matrix Kronecker

namespace ThreeCopyQutritWerner

def certificateMixedThreeWeight (σ : Equiv.Perm (Fin 3)) : ℚ :=
  (if σ = 1 then 1 / 2 else 0) -
    (if σ = Equiv.swap 1 2 then 1 / 2 else 0) - certificateS3Weight 1 σ

set_option maxHeartbeats 2000000 in
theorem certificateMixedThreeWeight_convolution (τ : Equiv.Perm (Fin 3)) :
    (∑ σ, certificateMixedThreeWeight σ * certificateMixedThreeWeight (σ⁻¹ * τ)) =
      certificateMixedThreeWeight τ := by
  obtain ⟨p, rfl⟩ := certificatePerm3_bijective.surjective τ
  rw [certificate_sum_perm3]
  fin_cases p <;> decide +kernel

theorem certificateMixedThreeWeight_inv (σ : Equiv.Perm (Fin 3)) :
    certificateMixedThreeWeight σ⁻¹ = certificateMixedThreeWeight σ := by
  obtain ⟨p, rfl⟩ := certificatePerm3_bijective.surjective σ
  fin_cases p <;> decide +kernel

def certificateMixedThreeCarrier {n : Type*} [Fintype n] [DecidableEq n] :
    Matrix (Fin 3 → n) (Fin 3 → n) ℂ :=
  ∑ σ, (certificateMixedThreeWeight σ : ℂ) • (certificateRegisterPerm σ).permMatrix ℂ

theorem certificateMixedThreeCarrier_idempotent {n : Type*} [Fintype n] [DecidableEq n] :
    certificateMixedThreeCarrier (n := n) * certificateMixedThreeCarrier =
      certificateMixedThreeCarrier := by
  apply certificate_matrix_sum_idempotent
  · exact certificateRegisterMatrix_mul
  · intro τ
    exact_mod_cast certificateMixedThreeWeight_convolution τ

theorem certificateMixedThreeCarrier_hermitian {n : Type*} [Fintype n] [DecidableEq n] :
    (certificateMixedThreeCarrier (n := n))ᴴ = certificateMixedThreeCarrier := by
  unfold certificateMixedThreeCarrier
  rw [Matrix.conjTranspose_sum]
  refine Fintype.sum_equiv (Equiv.inv (Equiv.Perm (Fin 3))) _ _ ?_
  intro σ
  simp only [Matrix.conjTranspose_smul, Matrix.conjTranspose_permMatrix,
    star_ratCast, Equiv.inv_apply, certificateMixedThreeWeight_inv,
    certificateRegisterPerm_inv]

/-- The finite mixed weight is exactly the manuscript's antisymmetrizer difference. -/
theorem certificateMixedThreeCarrier_eq {n : Type*} [Fintype n] [DecidableEq n] :
    certificateMixedThreeCarrier (n := n) =
      certificateRegisterAntisym 1 2 - certificateS3SiteProjection 1 := by
  unfold certificateMixedThreeCarrier
  simp only [certificateMixedThreeWeight, Rat.cast_sub, sub_smul, Finset.sum_sub_distrib]
  have he : (∑ σ : Equiv.Perm (Fin 3),
      ((if σ = 1 then 1 / 2 else 0 : ℚ) : ℂ) •
        (certificateRegisterPerm (n := n) σ).permMatrix ℂ) = (1 / 2 : ℂ) • 1 := by
    rw [Finset.sum_eq_single (1 : Equiv.Perm (Fin 3))]
    · rw [if_pos rfl, certificateRegisterMatrix_one]
      norm_num
    · intro b _ hb
      rw [if_neg hb, Rat.cast_zero, zero_smul]
    · intro h
      exact absurd (Finset.mem_univ _) h
  have hs : (∑ σ : Equiv.Perm (Fin 3),
      ((if σ = Equiv.swap 1 2 then 1 / 2 else 0 : ℚ) : ℂ) •
        (certificateRegisterPerm (n := n) σ).permMatrix ℂ) =
      (1 / 2 : ℂ) • (certificateRegisterPerm (Equiv.swap 1 2)).permMatrix ℂ := by
    rw [Finset.sum_eq_single (Equiv.swap (1 : Fin 3) 2)]
    · rw [if_pos rfl]
      norm_num
    · intro b _ hb
      rw [if_neg hb, Rat.cast_zero, zero_smul]
    · intro h
      exact absurd (Finset.mem_univ _) h
  rw [he, hs]
  simp only [certificateRegisterAntisym, smul_sub,
    certificateS3SiteProjection, certificateS3Projection]

/-- The four dual registers in the auxiliary carrier carry E[22] A01 A23. -/
def certificateAuxiliaryFourCarrier {n : Type*} [Fintype n] [DecidableEq n] :
    Matrix (Fin 4 → n) (Fin 4 → n) ℂ :=
  certificateCentralMatrix 12 * certificateRegisterAntisym (0 : Fin 4) 1 *
    certificateRegisterAntisym 2 3

theorem certificateAuxiliaryFourCarrier_pairs_commute {n : Type*} [Fintype n] [DecidableEq n] :
    certificateRegisterAntisym (n := n) (0 : Fin 4) 1 * certificateRegisterAntisym 2 3 =
      certificateRegisterAntisym 2 3 * certificateRegisterAntisym 0 1 := by
  have hs : (Equiv.swap (0 : Fin 4) 1) * Equiv.swap 2 3 =
      (Equiv.swap 2 3) * Equiv.swap 0 1 := by decide
  have hF : (certificateRegisterPerm (n := n) (Equiv.swap (0 : Fin 4) 1)).permMatrix ℂ *
      (certificateRegisterPerm (Equiv.swap 2 3)).permMatrix ℂ =
      (certificateRegisterPerm (Equiv.swap 2 3)).permMatrix ℂ *
      (certificateRegisterPerm (Equiv.swap 0 1)).permMatrix ℂ := by
    rw [certificateRegisterMatrix_mul, certificateRegisterMatrix_mul, hs]
  have h1 := (Commute.one_right ((certificateRegisterPerm (n := n)
    (Equiv.swap (0 : Fin 4) 1)).permMatrix ℂ)).sub_right hF
  have h2 := (Commute.one_left _).sub_left h1
  exact ((h2.smul_left (1 / 2 : ℂ)).smul_right (1 / 2 : ℂ)).eq

theorem certificateAuxiliaryFourCarrier_idempotent {n : Type*} [Fintype n] [DecidableEq n] :
    certificateAuxiliaryFourCarrier (n := n) * certificateAuxiliaryFourCarrier =
      certificateAuxiliaryFourCarrier := by
  let E : Matrix (Fin 4 → n) (Fin 4 → n) ℂ := certificateCentralMatrix 12
  let P := certificateRegisterAntisym (n := n) (0 : Fin 4) 1
  let Q := certificateRegisterAntisym (n := n) (2 : Fin 4) 3
  have hPQ : Commute P Q := certificateAuxiliaryFourCarrier_pairs_commute
  have hEP : Commute E P := certificateCentralMatrix_commutes_antisym 12 0 1
  have hEQ : Commute E Q := certificateCentralMatrix_commutes_antisym 12 2 3
  have hpair : IsIdempotentElem (P * Q) := IsIdempotentElem.mul_of_commute hPQ
    (certificateRegisterAntisym_idempotent 0 1) (certificateRegisterAntisym_idempotent 2 3)
  have h := IsIdempotentElem.mul_of_commute (hEP.mul_right hEQ)
    certificateCentralMatrix_four_idempotent hpair
  simpa only [certificateAuxiliaryFourCarrier, Matrix.mul_assoc] using h.eq

theorem certificateAuxiliaryFourCarrier_hermitian {n : Type*} [Fintype n] [DecidableEq n] :
    (certificateAuxiliaryFourCarrier (n := n))ᴴ = certificateAuxiliaryFourCarrier := by
  simp only [certificateAuxiliaryFourCarrier, Matrix.conjTranspose_mul,
    certificateRegisterAntisym_hermitian, certificateCentralMatrix_hermitian]
  calc
    certificateRegisterAntisym (n := n) (2 : Fin 4) 3 *
        (certificateRegisterAntisym 0 1 * certificateCentralMatrix 12) =
      certificateCentralMatrix 12 *
        (certificateRegisterAntisym 2 3 * certificateRegisterAntisym 0 1) := by
      rw [← certificateCentralMatrix_commutes_antisym, ← Matrix.mul_assoc,
        ← certificateCentralMatrix_commutes_antisym, Matrix.mul_assoc]
    _ = certificateCentralMatrix 12 *
        (certificateRegisterAntisym 0 1 * certificateRegisterAntisym 2 3) := by
      rw [← certificateAuxiliaryFourCarrier_pairs_commute]
    _ = _ := (Matrix.mul_assoc _ _ _).symm

/-- Exact 3+2 register split used by the mixed carrier. -/
def certificateFiveSplit32 (n : Type*) : (Fin 5 → n) ≃ ((Fin 3 → n) × (Fin 2 → n)) where
  toFun r := (![r 0, r 1, r 2], ![r 3, r 4])
  invFun x := ![x.1 0, x.1 1, x.1 2, x.2 0, x.2 1]
  left_inv r := by funext i; fin_cases i <;> rfl
  right_inv x := by
    apply Prod.ext
    · funext i; fin_cases i <;> rfl
    · funext i; fin_cases i <;> rfl

def certificateMixedFiveCarrier {n : Type*} [Fintype n] [DecidableEq n] :
    Matrix (Fin 5 → n) (Fin 5 → n) ℂ :=
  (certificateMixedThreeCarrier ⊗ₖ certificateRegisterAntisym (n := n) (0 : Fin 2) 1).submatrix
    (certificateFiveSplit32 n) (certificateFiveSplit32 n)

theorem certificateMixedFiveCarrier_idempotent {n : Type*} [Fintype n] [DecidableEq n] :
    certificateMixedFiveCarrier (n := n) * certificateMixedFiveCarrier =
      certificateMixedFiveCarrier := by
  unfold certificateMixedFiveCarrier
  rw [Matrix.submatrix_mul_equiv, ← Matrix.mul_kronecker_mul,
    certificateMixedThreeCarrier_idempotent, certificateRegisterAntisym_idempotent]

theorem certificateMixedFiveCarrier_hermitian {n : Type*} [Fintype n] [DecidableEq n] :
    (certificateMixedFiveCarrier (n := n))ᴴ = certificateMixedFiveCarrier := by
  simp only [certificateMixedFiveCarrier, Matrix.conjTranspose_submatrix,
    Matrix.conjTranspose_kronecker, certificateMixedThreeCarrier_hermitian,
    certificateRegisterAntisym_hermitian]

/-- Exact 1+4 register split used by the auxiliary carrier. -/
def certificateFiveSplit14 (n : Type*) : (Fin 5 → n) ≃ (n × (Fin 4 → n)) where
  toFun r := (r 0, ![r 1, r 2, r 3, r 4])
  invFun x := ![x.1, x.2 0, x.2 1, x.2 2, x.2 3]
  left_inv r := by funext i; fin_cases i <;> rfl
  right_inv x := by
    apply Prod.ext
    · rfl
    · funext i; fin_cases i <;> rfl

def certificateAuxiliaryFiveCarrier {n : Type*} [Fintype n] [DecidableEq n] :
    Matrix (Fin 5 → n) (Fin 5 → n) ℂ :=
  ((1 : Matrix n n ℂ) ⊗ₖ certificateAuxiliaryFourCarrier).submatrix
    (certificateFiveSplit14 n) (certificateFiveSplit14 n)

theorem certificateAuxiliaryFiveCarrier_idempotent {n : Type*} [Fintype n] [DecidableEq n] :
    certificateAuxiliaryFiveCarrier (n := n) * certificateAuxiliaryFiveCarrier =
      certificateAuxiliaryFiveCarrier := by
  unfold certificateAuxiliaryFiveCarrier
  rw [Matrix.submatrix_mul_equiv, ← Matrix.mul_kronecker_mul,
    Matrix.one_mul, certificateAuxiliaryFourCarrier_idempotent]

theorem certificateAuxiliaryFiveCarrier_hermitian {n : Type*} [Fintype n] [DecidableEq n] :
    (certificateAuxiliaryFiveCarrier (n := n))ᴴ = certificateAuxiliaryFiveCarrier := by
  simp only [certificateAuxiliaryFiveCarrier, Matrix.conjTranspose_submatrix,
    Matrix.conjTranspose_kronecker, Matrix.conjTranspose_one,
    certificateAuxiliaryFourCarrier_hermitian]

/-- The column register is last in the source's six-register order. -/
def certificateSixSplit51 (n : Type*) : (Fin 6 → n) ≃ ((Fin 5 → n) × n) where
  toFun r := (![r 0, r 1, r 2, r 3, r 4], r 5)
  invFun x := ![x.1 0, x.1 1, x.1 2, x.1 3, x.1 4, x.2]
  left_inv r := by funext i; fin_cases i <;> rfl
  right_inv x := by
    apply Prod.ext
    · funext i; fin_cases i <;> rfl
    · rfl

/-- Restore the independent column identity without changing any carrier action. -/
def certificateCarrierWithColumn {n : Type*} [Fintype n] [DecidableEq n]
    (P : Matrix (Fin 5 → n) (Fin 5 → n) ℂ) : Matrix (Fin 6 → n) (Fin 6 → n) ℂ :=
  (P ⊗ₖ (1 : Matrix n n ℂ)).submatrix (certificateSixSplit51 n) (certificateSixSplit51 n)

theorem certificateCarrierWithColumn_idempotent {n : Type*} [Fintype n] [DecidableEq n]
    (P : Matrix (Fin 5 → n) (Fin 5 → n) ℂ) (hP : P * P = P) :
    certificateCarrierWithColumn P * certificateCarrierWithColumn P = certificateCarrierWithColumn P := by
  unfold certificateCarrierWithColumn
  rw [Matrix.submatrix_mul_equiv, ← Matrix.mul_kronecker_mul, hP, Matrix.one_mul]

theorem certificateCarrierWithColumn_hermitian {n : Type*} [Fintype n] [DecidableEq n]
    (P : Matrix (Fin 5 → n) (Fin 5 → n) ℂ) (hP : Pᴴ = P) :
    (certificateCarrierWithColumn P)ᴴ = certificateCarrierWithColumn P := by
  simp only [certificateCarrierWithColumn, Matrix.conjTranspose_submatrix,
    Matrix.conjTranspose_kronecker, Matrix.conjTranspose_one, hP]

end ThreeCopyQutritWerner
