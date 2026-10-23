module

public import ThreeCopyQutritWerner.CertificateCarrierTensorExpansion
public import ThreeCopyQutritWerner.CertificateSiteRegroup

@[expose] public section


/-!
# Canonical carriers in the actual six-register source order

The five-register holomorphic, mixed and auxiliary carriers are extended by the
independent column identity. Their literal tensor-coordinate permutations are
the original source permutations. Hermiticity then supplies the source's inverse
permutation convention, so these are actual physical diagram sums.
-/

noncomputable section

open scoped BigOperators Matrix Kronecker

set_option maxRecDepth 100000
set_option maxHeartbeats 10000000

namespace ThreeCopyQutritWerner

/-- Exact five-register mixed permutation before restoring the column. -/
def certificateCarrierWordPerm1Five (n : Type*) (p : Fin 12) :
    Equiv.Perm (Fin 5 → n) :=
  Equiv.permCongr (certificateFiveSplit32 n).symm
    (Equiv.prodCongr
      (certificateRegisterPerm (certificatePerm3 (certificateCarrierIndex1 p).1))
      (certificateRegisterPerm (certificateMinorTwoPerm (certificateCarrierIndex1 p).2)))

/-- Exact five-register auxiliary permutation, with row register fixed. -/
def certificateCarrierWordPerm2Five (n : Type*) (p : Fin 24) :
    Equiv.Perm (Fin 5 → n) :=
  Equiv.permCongr (certificateFiveSplit14 n).symm
    (Equiv.prodCongr (Equiv.refl n)
      (certificateRegisterPerm (certificatePerm4 (certificateCarrierIndex2 p))))

/-- Literal extension of a holomorphic source permutation fixes its column. -/
theorem certificateCarrierWordPerm0_six (n : Type*) (p : Fin 120) :
    Equiv.permCongr (certificateSixSplit51 n).symm
      (Equiv.prodCongr
        (certificateRegisterPerm (certificatePerm5 (certificateCarrierIndex0 p)))
        (Equiv.refl n)) = certificateRegisterPerm (certificateCarrierPerm0 p) := by
  ext r i
  fin_cases p <;> fin_cases i <;> rfl

/-- Literal mixed source permutation on all six original registers. -/
theorem certificateCarrierWordPerm1_six (n : Type*) (p : Fin 12) :
    Equiv.permCongr (certificateSixSplit51 n).symm
      (Equiv.prodCongr (certificateCarrierWordPerm1Five n p) (Equiv.refl n)) =
        certificateRegisterPerm (certificateCarrierPerm1 p) := by
  ext r i
  fin_cases p <;> fin_cases i <;> rfl

/-- Literal auxiliary source permutation on all six original registers. -/
theorem certificateCarrierWordPerm2_six (n : Type*) (p : Fin 24) :
    Equiv.permCongr (certificateSixSplit51 n).symm
      (Equiv.prodCongr (certificateCarrierWordPerm2Five n p) (Equiv.refl n)) =
        certificateRegisterPerm (certificateCarrierPerm2 p) := by
  ext r i
  fin_cases p <;> fin_cases i <;> rfl

/-- Adding a column identity realizes the literal extended permutation. -/
theorem certificateCarrierWithColumn_perm {n : Type*} [Fintype n] [DecidableEq n]
    (σ : Equiv.Perm (Fin 5 → n)) :
    certificateCarrierWithColumn (σ.permMatrix ℂ) =
      (Equiv.permCongr (certificateSixSplit51 n).symm
        (Equiv.prodCongr σ (Equiv.refl n))).permMatrix ℂ := by
  unfold certificateCarrierWithColumn
  rw [← Matrix.permMatrix_refl (n := n) (R := ℂ),
    certificatePermMatrix_prod, certificatePermMatrix_reindex]

/-- The auxiliary five-register sum keeps the original row identity. -/
theorem certificateAuxiliaryFiveCarrier_source_sum {n : Type*}
    [Fintype n] [DecidableEq n] :
    certificateAuxiliaryFiveCarrier (n := n) =
      ∑ p : Fin 24, (certificateCarrierWeight2 p : ℂ) •
        (certificateCarrierWordPerm2Five n p).permMatrix ℂ := by
  unfold certificateAuxiliaryFiveCarrier
  rw [certificateAuxiliaryFourCarrier_source_sum]
  have hperm (p : Fin 24) :
      ((1 : Matrix n n ℂ) ⊗ₖ
        (certificateRegisterPerm (certificatePerm4 (certificateCarrierIndex2 p))).permMatrix ℂ).submatrix
          (certificateFiveSplit14 n) (certificateFiveSplit14 n) =
        (certificateCarrierWordPerm2Five n p).permMatrix ℂ := by
    rw [← Matrix.permMatrix_refl (n := n) (R := ℂ),
      certificatePermMatrix_prod, certificatePermMatrix_reindex]
    rfl
  simp_rw [← hperm]
  ext i j
  simp only [Matrix.submatrix_apply, Matrix.kronecker_apply, Matrix.kroneckerMap_apply,
    Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro p _
  ring

/-- The holomorphic carrier is exactly the original six-register forward sum. -/
theorem certificateHolomorphicSixCarrier_source_sum {n : Type*}
    [Fintype n] [DecidableEq n] :
    certificateCarrierWithColumn (certificateHolomorphicCarrier (n := n)) =
      ∑ p : Fin 120, (certificateCarrierWeight0 p : ℂ) •
        (certificateRegisterPerm (certificateCarrierPerm0 p)).permMatrix ℂ := by
  rw [certificateHolomorphicCarrier_source_sum, certificateCarrierWithColumn_sum]
  apply Finset.sum_congr rfl
  intro p _
  rw [certificateCarrierWithColumn_perm, certificateCarrierWordPerm0_six]

/-- The mixed carrier is exactly the original six-register forward sum. -/
theorem certificateMixedSixCarrier_source_sum {n : Type*}
    [Fintype n] [DecidableEq n] :
    certificateCarrierWithColumn (certificateMixedFiveCarrier (n := n)) =
      ∑ p : Fin 12, (certificateCarrierWeight1 p : ℂ) •
        (certificateRegisterPerm (certificateCarrierPerm1 p)).permMatrix ℂ := by
  rw [certificateMixedFiveCarrier_source_sum, certificateCarrierWithColumn_sum]
  apply Finset.sum_congr rfl
  intro p _
  rw [certificatePermMatrix_prod, certificatePermMatrix_reindex]
  change (certificateCarrierWeight1 p : ℂ) •
      certificateCarrierWithColumn ((certificateCarrierWordPerm1Five n p).permMatrix ℂ) = _
  rw [certificateCarrierWithColumn_perm, certificateCarrierWordPerm1_six]

/-- The auxiliary carrier is exactly the original six-register forward sum. -/
theorem certificateAuxiliarySixCarrier_source_sum {n : Type*}
    [Fintype n] [DecidableEq n] :
    certificateCarrierWithColumn (certificateAuxiliaryFiveCarrier (n := n)) =
      ∑ p : Fin 24, (certificateCarrierWeight2 p : ℂ) •
        (certificateRegisterPerm (certificateCarrierPerm2 p)).permMatrix ℂ := by
  rw [certificateAuxiliaryFiveCarrier_source_sum, certificateCarrierWithColumn_sum]
  apply Finset.sum_congr rfl
  intro p _
  rw [certificateCarrierWithColumn_perm, certificateCarrierWordPerm2_six]

/-- The canonical holomorphic carrier uses the archive's ordinary inverse action. -/
theorem certificateHolomorphicSixCarrier_diagram_sum {n : Type*}
    [Fintype n] [DecidableEq n] :
    certificateCarrierWithColumn (certificateHolomorphicCarrier (n := n)) =
      ∑ p : Fin 120, (certificateCarrierWeight0 p : ℂ) •
        certificateLocalDiagram (n := n) (R := ℂ) ∅ (certificateCarrierPerm0 p) := by
  simp_rw [certificateLocalDiagram_empty]
  exact certificateRealPermSum_inverse _ _ _
    (certificateCarrierWithColumn_hermitian _ certificateHolomorphicCarrier_hermitian)
    certificateHolomorphicSixCarrier_source_sum

/-- The canonical mixed carrier uses the same original inverse convention. -/
theorem certificateMixedSixCarrier_diagram_sum {n : Type*}
    [Fintype n] [DecidableEq n] :
    certificateCarrierWithColumn (certificateMixedFiveCarrier (n := n)) =
      ∑ p : Fin 12, (certificateCarrierWeight1 p : ℂ) •
        certificateLocalDiagram (n := n) (R := ℂ) ∅ (certificateCarrierPerm1 p) := by
  simp_rw [certificateLocalDiagram_empty]
  exact certificateRealPermSum_inverse _ _ _
    (certificateCarrierWithColumn_hermitian _ certificateMixedFiveCarrier_hermitian)
    certificateMixedSixCarrier_source_sum

/-- The canonical auxiliary carrier uses the same original inverse convention. -/
theorem certificateAuxiliarySixCarrier_diagram_sum {n : Type*}
    [Fintype n] [DecidableEq n] :
    certificateCarrierWithColumn (certificateAuxiliaryFiveCarrier (n := n)) =
      ∑ p : Fin 24, (certificateCarrierWeight2 p : ℂ) •
        certificateLocalDiagram (n := n) (R := ℂ) ∅ (certificateCarrierPerm2 p) := by
  simp_rw [certificateLocalDiagram_empty]
  exact certificateRealPermSum_inverse _ _ _
    (certificateCarrierWithColumn_hermitian _ certificateAuxiliaryFiveCarrier_hermitian)
    certificateAuxiliarySixCarrier_source_sum

/-- The original statement-base carrier has precisely the same six-register coordinates. -/
theorem certificateQutritCarrier_eq_word_carrier :
    certificateQutritCarrier =
      (certificateCarrierWithColumn (certificateHolomorphicCarrier
        (n := Fin 3 × Fin 3 × Fin 3))).submatrix
          certificateSixRegisterWordEquiv certificateSixRegisterWordEquiv := by
  ext r c
  rfl

end ThreeCopyQutritWerner
