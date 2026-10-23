module

public import ThreeCopyQutritWerner.CertificateCarrierExpansion

@[expose] public section


/-!
# Tensor and coordinate transport for the original carrier sums

All permutation matrices in this file use explicit equivalences. Hermiticity
converts the forward canonical permutation sum to the archive's inverse action,
without a separate assumption about saved coefficients or projectors.
-/

noncomputable section

open scoped BigOperators Matrix Kronecker

namespace ThreeCopyQutritWerner

/-- Tensoring two finite matrix sums multiplies their literal coefficients. -/
theorem certificateTensor_weighted_sums
    {a b n m : Type*} [Fintype a] [Fintype b]
    (A : a → Matrix n n ℂ) (B : b → Matrix m m ℂ) (w : a → ℂ) (v : b → ℂ) :
    (∑ i, w i • A i) ⊗ₖ (∑ j, v j • B j) =
      ∑ p : a × b, (w p.1 * v p.2) • (A p.1 ⊗ₖ B p.2) := by
  ext ⟨i, j⟩ ⟨k, l⟩
  simp only [Matrix.kronecker_apply, Matrix.sum_apply, Matrix.smul_apply,
    smul_eq_mul, Fintype.sum_prod_type, Finset.sum_mul_sum]
  apply Finset.sum_congr rfl
  intro x _
  apply Finset.sum_congr rfl
  intro y _
  ring

/-- Tensor products of literal permutation matrices realize product equivalences. -/
theorem certificatePermMatrix_prod {n m : Type*} [DecidableEq n] [DecidableEq m]
    (σ : Equiv.Perm n) (τ : Equiv.Perm m) :
    σ.permMatrix ℂ ⊗ₖ τ.permMatrix ℂ = Equiv.Perm.permMatrix ℂ (Equiv.prodCongr σ τ) := by
  ext ⟨i, j⟩ ⟨k, l⟩
  by_cases hi : σ i = k <;> by_cases hj : τ j = l <;>
    simp [Matrix.kronecker_apply, PEquiv.toMatrix_toPEquiv_apply, Pi.single_apply,
      Prod.ext_iff, hi, hj]

/-- A literal row/column equivalence transports the same physical permutation. -/
theorem certificatePermMatrix_reindex {n m : Type*} [DecidableEq n] [DecidableEq m]
    (σ : Equiv.Perm n) (e : m ≃ n) :
    (σ.permMatrix ℂ).submatrix e e = (Equiv.permCongr e.symm σ).permMatrix ℂ := by
  ext i j
  simp [Matrix.submatrix_apply, PEquiv.toMatrix_toPEquiv_apply, Pi.single_apply,
    Equiv.permCongr_def, Equiv.symm_apply_eq]

/-- Adding the independent column register preserves a finite weighted sum. -/
theorem certificateCarrierWithColumn_sum {a n : Type*} [Fintype a]
    [Fintype n] [DecidableEq n]
    (A : a → Matrix (Fin 5 → n) (Fin 5 → n) ℂ) (w : a → ℂ) :
    certificateCarrierWithColumn (∑ p, w p • A p) =
      ∑ p, w p • certificateCarrierWithColumn (A p) := by
  ext i j
  simp only [certificateCarrierWithColumn, Matrix.submatrix_apply,
    Matrix.kronecker_apply, Matrix.kroneckerMap_apply, Matrix.sum_apply, Matrix.smul_apply,
    smul_eq_mul, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro p _
  ring

/-- Hermiticity converts the exact real forward sum to its inverse convention. -/
theorem certificateRealPermSum_inverse {a n : Type*} [Fintype a] [DecidableEq n]
    (P : Matrix n n ℂ) (σ : a → Equiv.Perm n) (w : a → ℚ)
    (hP : Pᴴ = P) (hsum : P = ∑ p, (w p : ℂ) • (σ p).permMatrix ℂ) :
    P = ∑ p, (w p : ℂ) • (σ p)⁻¹.permMatrix ℂ := by
  rw [← hP, hsum, Matrix.conjTranspose_sum]
  simp only [Matrix.conjTranspose_smul, star_ratCast, Matrix.conjTranspose_permMatrix]

/-- The ordinary two-register identity/swap enumeration for a minor antisymmetrizer. -/
def certificateMinorTwoPerm (b : Fin 2) : Equiv.Perm (Fin 2) :=
  if b = 0 then 1 else Equiv.swap 0 1

def certificateMinorTwoWeight (b : Fin 2) : ℚ := if b = 0 then 1 / 2 else -(1 / 2)

theorem certificateMinorTwo_sum {n : Type*} [Fintype n] [DecidableEq n] :
    certificateRegisterAntisym (n := n) (0 : Fin 2) 1 =
      ∑ b : Fin 2, (certificateMinorTwoWeight b : ℂ) •
        (certificateRegisterPerm (certificateMinorTwoPerm b)).permMatrix ℂ := by
  simp [Fin.sum_univ_two, certificateMinorTwoWeight, certificateMinorTwoPerm,
    certificateRegisterMatrix_one, certificateRegisterAntisym, smul_sub, sub_eq_add_neg]

/-- The canonical mixed five-register matrix in the original source order. -/
theorem certificateMixedFiveCarrier_source_sum {n : Type*} [Fintype n] [DecidableEq n] :
    certificateMixedFiveCarrier (n := n) =
      ∑ p : Fin 12, (certificateCarrierWeight1 p : ℂ) •
        (((certificateRegisterPerm (certificatePerm3 (certificateCarrierIndex1 p).1)).permMatrix ℂ ⊗ₖ
          (certificateRegisterPerm (certificateMinorTwoPerm (certificateCarrierIndex1 p).2)).permMatrix ℂ).submatrix
            (certificateFiveSplit32 n) (certificateFiveSplit32 n)) := by
  have hexpand : certificateMixedFiveCarrier (n := n) =
      ∑ p : Fin 6 × Fin 2,
        ((certificateMixedThreeWeight (certificatePerm3 p.1) : ℂ) *
          (certificateMinorTwoWeight p.2 : ℂ)) •
          (((certificateRegisterPerm (certificatePerm3 p.1)).permMatrix ℂ ⊗ₖ
            (certificateRegisterPerm (certificateMinorTwoPerm p.2)).permMatrix ℂ).submatrix
              (certificateFiveSplit32 n) (certificateFiveSplit32 n)) := by
    unfold certificateMixedFiveCarrier certificateMixedThreeCarrier
    rw [certificate_sum_perm3, certificateMinorTwo_sum, certificateTensor_weighted_sums]
    ext i j
    simp only [Matrix.submatrix_apply, Matrix.sum_apply, Matrix.smul_apply]
  rw [hexpand]
  refine Fintype.sum_equiv (Equiv.ofBijective certificateCarrierIndex1
    certificateCarrierIndex1_bijective).symm _ _ ?_
  intro p
  have hi : certificateCarrierIndex1
      ((Equiv.ofBijective certificateCarrierIndex1 certificateCarrierIndex1_bijective).symm p) = p :=
    (Equiv.ofBijective certificateCarrierIndex1 certificateCarrierIndex1_bijective).apply_symm_apply p
  rw [certificateCarrierWeight1_antisym, hi]
  simp only [certificateMixedThreeWeight, certificateMinorTwoWeight, Rat.cast_mul]

end ThreeCopyQutritWerner
