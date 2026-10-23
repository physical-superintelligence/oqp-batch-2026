module

public import ThreeCopyQutritWerner.CertificateX2BridgePair

@[expose] public section


/-!
# S3 covariance of the h-side forms

Swapping two adjacent sites of an h type triple reindexes the carrier action, the endpoint
target form and both transferred forms by the same index equivalence (the source tensor is
symmetric under site permutations, `x2FullTensor_perm`). Hence the h-side form at `τ` is a
reindexing of the form at the swapped triple, and positivity on the sorted type triples gives
positivity on all of them (`x2_hres_of_sorted`).
-/

noncomputable section

open scoped BigOperators Matrix Kronecker ComplexOrder

namespace ThreeCopyQutritWerner

/-- The h-side form on a type triple. -/
def x2HForm (D : X2Data) (Nm : X2Blocks 1) (Na : X2Blocks 2) (τ : Fin 7 × Fin 7 × Fin 7) :
    Matrix (Fin (certificatePhysicalFrameSystem0.size τ.1 *
        (certificatePhysicalFrameSystem0.size τ.2.1 * certificatePhysicalFrameSystem0.size τ.2.2)))
      (Fin (certificatePhysicalFrameSystem0.size τ.1 *
        (certificatePhysicalFrameSystem0.size τ.2.1 * certificatePhysicalFrameSystem0.size τ.2.2))) ℂ :=
  (certificateCarrierJointAction0 τ)ᴴ *
    (x2TargetQForm τ - x2TransferQForm D 1 Nm τ - x2TransferQForm D 2 Na τ) *
      certificateCarrierJointAction0 τ

/-- Swap of the first two sites of a type triple. -/
abbrev x2TauSwap01 (τ : Fin 7 × Fin 7 × Fin 7) : Fin 7 × Fin 7 × Fin 7 := (τ.2.1, τ.1, τ.2.2)

/-- Swap of the last two sites of a type triple. -/
abbrev x2TauSwap12 (τ : Fin 7 × Fin 7 × Fin 7) : Fin 7 × Fin 7 × Fin 7 := (τ.1, τ.2.2, τ.2.1)

/-- Frame indices under the swap of the first two sites. -/
def x2IdxSwap01 (a b c : ℕ) : Fin (a * (b * c)) ≃ Fin (b * (a * c)) :=
  (finProdFinEquiv.symm.trans ((Equiv.refl _).prodCongr finProdFinEquiv.symm)).trans
    ((((Equiv.prodAssoc _ _ _).symm.trans ((Equiv.prodComm _ _).prodCongr (Equiv.refl _))).trans
      (Equiv.prodAssoc _ _ _)).trans (((Equiv.refl _).prodCongr finProdFinEquiv).trans finProdFinEquiv))

/-- Frame indices under the swap of the last two sites. -/
def x2IdxSwap12 (a b c : ℕ) : Fin (a * (b * c)) ≃ Fin (a * (c * b)) :=
  (finProdFinEquiv.symm.trans ((Equiv.refl _).prodCongr finProdFinEquiv.symm)).trans
    (((Equiv.refl _).prodCongr (Equiv.prodComm _ _)).trans
      (((Equiv.refl _).prodCongr finProdFinEquiv).trans finProdFinEquiv))

theorem x2IdxSwap01_decode (a b c : ℕ) (i : Fin (a * (b * c))) :
    (finProdFinEquiv.symm (x2IdxSwap01 a b c i)).1 =
        (finProdFinEquiv.symm (finProdFinEquiv.symm i).2).1 ∧
      (finProdFinEquiv.symm (finProdFinEquiv.symm (x2IdxSwap01 a b c i)).2).1 =
        (finProdFinEquiv.symm i).1 ∧
      (finProdFinEquiv.symm (finProdFinEquiv.symm (x2IdxSwap01 a b c i)).2).2 =
        (finProdFinEquiv.symm (finProdFinEquiv.symm i).2).2 := by
  simp [x2IdxSwap01]

theorem x2IdxSwap12_decode (a b c : ℕ) (i : Fin (a * (b * c))) :
    (finProdFinEquiv.symm (x2IdxSwap12 a b c i)).1 = (finProdFinEquiv.symm i).1 ∧
      (finProdFinEquiv.symm (finProdFinEquiv.symm (x2IdxSwap12 a b c i)).2).1 =
        (finProdFinEquiv.symm (finProdFinEquiv.symm i).2).2 ∧
      (finProdFinEquiv.symm (finProdFinEquiv.symm (x2IdxSwap12 a b c i)).2).2 =
        (finProdFinEquiv.symm (finProdFinEquiv.symm i).2).1 := by
  simp [x2IdxSwap12]

/-- Subtraction commutes with reindexing (applied form). -/
theorem x2_submatrix_sub {l m n o : Type*} (A B : Matrix m n ℂ) (r : l → m) (c : o → n) :
    A.submatrix r c - B.submatrix r c = (A - B).submatrix r c := rfl

/-- Reindexing commutes with the h-side form's products. -/
theorem x2_form_submatrix {n m : Type*} [Fintype n] [Fintype m] [DecidableEq n] [DecidableEq m]
    (e : n ≃ m) (π f : Matrix m m ℂ) :
    (π.submatrix e e)ᴴ * f.submatrix e e * π.submatrix e e = (πᴴ * f * π).submatrix e e := by
  rw [Matrix.conjTranspose_submatrix, Matrix.submatrix_mul_equiv, Matrix.submatrix_mul_equiv]

/-- A three-site source action is reindexed by the site swap. -/
theorem x2_tripleSourceAction_swap01 {n F T : Type*} [Fintype n] [Fintype F] [DecidableEq T]
    (s : CertificatePhysicalFrameSystem n F T)
    (A : (t : T) → Matrix (Fin (s.size t)) (Fin (s.size t)) ℂ) (τ : T × T × T) :
    certificateTripleSourceAction s A A A τ =
      (certificateTripleSourceAction s A A A (τ.2.1, τ.1, τ.2.2)).submatrix
        (x2IdxSwap01 (s.size τ.1) (s.size τ.2.1) (s.size τ.2.2))
        (x2IdxSwap01 (s.size τ.1) (s.size τ.2.1) (s.size τ.2.2)) := by
  ext i j
  rw [Matrix.submatrix_apply, x2_tripleSourceAction_apply, x2_tripleSourceAction_apply]
  obtain ⟨hi0, hi1, hi2⟩ := x2IdxSwap01_decode (s.size τ.1) (s.size τ.2.1) (s.size τ.2.2) i
  obtain ⟨hj0, hj1, hj2⟩ := x2IdxSwap01_decode (s.size τ.1) (s.size τ.2.1) (s.size τ.2.2) j
  dsimp only
  rw [hi0, hi1, hi2, hj0, hj1, hj2]
  ring

theorem x2_tripleSourceAction_swap12 {n F T : Type*} [Fintype n] [Fintype F] [DecidableEq T]
    (s : CertificatePhysicalFrameSystem n F T)
    (A : (t : T) → Matrix (Fin (s.size t)) (Fin (s.size t)) ℂ) (τ : T × T × T) :
    certificateTripleSourceAction s A A A τ =
      (certificateTripleSourceAction s A A A (τ.1, τ.2.2, τ.2.1)).submatrix
        (x2IdxSwap12 (s.size τ.1) (s.size τ.2.1) (s.size τ.2.2))
        (x2IdxSwap12 (s.size τ.1) (s.size τ.2.1) (s.size τ.2.2)) := by
  ext i j
  rw [Matrix.submatrix_apply, x2_tripleSourceAction_apply, x2_tripleSourceAction_apply]
  obtain ⟨hi0, hi1, hi2⟩ := x2IdxSwap12_decode (s.size τ.1) (s.size τ.2.1) (s.size τ.2.2) i
  obtain ⟨hj0, hj1, hj2⟩ := x2IdxSwap12_decode (s.size τ.1) (s.size τ.2.1) (s.size τ.2.2) j
  dsimp only
  rw [hi0, hi1, hi2, hj0, hj1, hj2]
  ring

theorem x2_carrier_swap01 (τ : Fin 7 × Fin 7 × Fin 7) :
    certificateCarrierJointAction0 τ =
      (certificateCarrierJointAction0 (x2TauSwap01 τ)).submatrix
        (x2IdxSwap01 _ _ _) (x2IdxSwap01 _ _ _) := by
  unfold certificateCarrierJointAction0 x2TauSwap01
  ext i j
  simp only [Matrix.sum_apply, Matrix.smul_apply, Matrix.submatrix_apply]
  apply Finset.sum_congr rfl
  intro p _
  rw [x2_tripleSourceAction_swap01 certificatePhysicalFrameSystem0 _ τ, Matrix.submatrix_apply]

theorem x2_carrier_swap12 (τ : Fin 7 × Fin 7 × Fin 7) :
    certificateCarrierJointAction0 τ =
      (certificateCarrierJointAction0 (x2TauSwap12 τ)).submatrix
        (x2IdxSwap12 _ _ _) (x2IdxSwap12 _ _ _) := by
  unfold certificateCarrierJointAction0 x2TauSwap12
  ext i j
  simp only [Matrix.sum_apply, Matrix.smul_apply, Matrix.submatrix_apply]
  apply Finset.sum_congr rfl
  intro p _
  rw [x2_tripleSourceAction_swap12 certificatePhysicalFrameSystem0 _ τ, Matrix.submatrix_apply]

theorem x2_target_swap01 (τ : Fin 7 × Fin 7 × Fin 7) :
    x2TargetQForm τ = (x2TargetQForm (x2TauSwap01 τ)).submatrix (x2IdxSwap01 _ _ _) (x2IdxSwap01 _ _ _) := by
  unfold x2TargetQForm certificateThreeSiteFrameSystem0 x2TauSwap01
  rw [x2_metric_tripleSourceAction, x2_metric_tripleSourceAction]
  exact x2_tripleSourceAction_swap01 certificatePhysicalFrameSystem0 _ τ

theorem x2_target_swap12 (τ : Fin 7 × Fin 7 × Fin 7) :
    x2TargetQForm τ = (x2TargetQForm (x2TauSwap12 τ)).submatrix (x2IdxSwap12 _ _ _) (x2IdxSwap12 _ _ _) := by
  unfold x2TargetQForm certificateThreeSiteFrameSystem0 x2TauSwap12
  rw [x2_metric_tripleSourceAction, x2_metric_tripleSourceAction]
  exact x2_tripleSourceAction_swap12 certificatePhysicalFrameSystem0 _ τ

/-- The source tensor is symmetric under swapping its last two unit arguments. -/
theorem x2FmVec_swap12 (D : X2Data) (s : Fin 3) (N : X2Blocks s) (x : X2U s × X2U s × X2U s) :
    x2FmVec D s N (x.1, x.2.2, x.2.1) = x2FmVec D s N x := by
  have h := x2FullTensor_perm D s N 1 ![x.1.1, x.2.1.1, x.2.2.1]
    ![(x.1.2.1 : ℕ), x.2.1.2.1, x.2.2.2.1] ![(x.1.2.2 : ℕ), x.2.1.2.2, x.2.2.2.2]
  have e1 : (![x.1.1, x.2.1.1, x.2.2.1] ∘ x2Perm3 1) = ![x.1.1, x.2.2.1, x.2.1.1] := by
    funext i
    fin_cases i <;> rfl
  have e2 : (![(x.1.2.1 : ℕ), x.2.1.2.1, x.2.2.2.1] ∘ x2Perm3 1) =
      ![(x.1.2.1 : ℕ), x.2.2.2.1, x.2.1.2.1] := by
    funext i
    fin_cases i <;> rfl
  have e3 : (![(x.1.2.2 : ℕ), x.2.1.2.2, x.2.2.2.2] ∘ x2Perm3 1) =
      ![(x.1.2.2 : ℕ), x.2.2.2.2, x.2.1.2.2] := by
    funext i
    fin_cases i <;> rfl
  rw [e1, e2, e3] at h
  exact h

theorem x2_transferVec_swap12 (D : X2Data) (s : Fin 3) (N : X2Blocks s) (u v w : X2U 0) :
    ((x2Qu D s ⊗ₖ (x2Qu D s ⊗ₖ x2Qu D s)) *ᵥ x2FmVec D s N) (u, w, v) =
      ((x2Qu D s ⊗ₖ (x2Qu D s ⊗ₖ x2Qu D s)) *ᵥ x2FmVec D s N) (u, v, w) := by
  simp only [Matrix.mulVec, dotProduct, Matrix.kroneckerMap_apply]
  let e : (X2U s × X2U s × X2U s) ≃ (X2U s × X2U s × X2U s) :=
    { toFun := fun x => (x.1, x.2.2, x.2.1), invFun := fun x => (x.1, x.2.2, x.2.1),
      left_inv := fun _ => rfl, right_inv := fun _ => rfl }
  refine Fintype.sum_equiv e _ _ (fun x => ?_)
  show x2Qu D s u x.1 * (x2Qu D s w x.2.1 * x2Qu D s v x.2.2) * x2FmVec D s N x =
    x2Qu D s u x.1 * (x2Qu D s v x.2.2 * x2Qu D s w x.2.1) * x2FmVec D s N (x.1, x.2.2, x.2.1)
  rw [x2FmVec_swap12]
  ring

theorem x2_transferQForm_swap01 (D : X2Data) (s : Fin 3) (N : X2Blocks s)
    (τ : Fin 7 × Fin 7 × Fin 7) :
    x2TransferQForm D s N τ =
      (x2TransferQForm D s N (x2TauSwap01 τ)).submatrix (x2IdxSwap01 _ _ _) (x2IdxSwap01 _ _ _) := by
  ext i j
  rw [Matrix.submatrix_apply]
  obtain ⟨hi0, hi1, hi2⟩ := x2IdxSwap01_decode _ _ _ i
  obtain ⟨hj0, hj1, hj2⟩ := x2IdxSwap01_decode _ _ _ j
  simp only [x2TransferQForm, Matrix.of_apply, x2TauSwap01]
  rw [hi0, hi1, hi2, hj0, hj1, hj2, x2_transferVec_swap01]

theorem x2_transferQForm_swap12 (D : X2Data) (s : Fin 3) (N : X2Blocks s)
    (τ : Fin 7 × Fin 7 × Fin 7) :
    x2TransferQForm D s N τ =
      (x2TransferQForm D s N (x2TauSwap12 τ)).submatrix (x2IdxSwap12 _ _ _) (x2IdxSwap12 _ _ _) := by
  ext i j
  rw [Matrix.submatrix_apply]
  obtain ⟨hi0, hi1, hi2⟩ := x2IdxSwap12_decode _ _ _ i
  obtain ⟨hj0, hj1, hj2⟩ := x2IdxSwap12_decode _ _ _ j
  simp only [x2TransferQForm, Matrix.of_apply, x2TauSwap12]
  rw [hi0, hi1, hi2, hj0, hj1, hj2, x2_transferVec_swap12]

theorem x2_hform_swap01 (D : X2Data) (Nm : X2Blocks 1) (Na : X2Blocks 2)
    (τ : Fin 7 × Fin 7 × Fin 7) :
    x2HForm D Nm Na τ =
      (x2HForm D Nm Na (x2TauSwap01 τ)).submatrix (x2IdxSwap01 _ _ _) (x2IdxSwap01 _ _ _) := by
  unfold x2HForm
  rw [x2_carrier_swap01 τ, x2_target_swap01 τ, x2_transferQForm_swap01 D 1 Nm τ,
    x2_transferQForm_swap01 D 2 Na τ, x2_submatrix_sub, x2_submatrix_sub,
    x2_form_submatrix]

theorem x2_hform_swap12 (D : X2Data) (Nm : X2Blocks 1) (Na : X2Blocks 2)
    (τ : Fin 7 × Fin 7 × Fin 7) :
    x2HForm D Nm Na τ =
      (x2HForm D Nm Na (x2TauSwap12 τ)).submatrix (x2IdxSwap12 _ _ _) (x2IdxSwap12 _ _ _) := by
  unfold x2HForm
  rw [x2_carrier_swap12 τ, x2_target_swap12 τ, x2_transferQForm_swap12 D 1 Nm τ,
    x2_transferQForm_swap12 D 2 Na τ, x2_submatrix_sub, x2_submatrix_sub,
    x2_form_submatrix]

/-- COVARIANCE: positivity of the h-side forms on the sorted type triples gives it on all. -/
theorem x2_hres_of_sorted (D : X2Data) (Nm : X2Blocks 1) (Na : X2Blocks 2)
    (hsorted : ∀ τ : Fin 7 × Fin 7 × Fin 7, τ.1 ≤ τ.2.1 → τ.2.1 ≤ τ.2.2 →
      (x2HForm D Nm Na τ).PosSemidef) (τ : Fin 7 × Fin 7 × Fin 7) :
    (x2HForm D Nm Na τ).PosSemidef := by
  have s01 : ∀ σ, (x2HForm D Nm Na (x2TauSwap01 σ)).PosSemidef → (x2HForm D Nm Na σ).PosSemidef :=
    fun σ h => by rw [x2_hform_swap01]; exact h.submatrix _
  have s12 : ∀ σ, (x2HForm D Nm Na (x2TauSwap12 σ)).PosSemidef → (x2HForm D Nm Na σ).PosSemidef :=
    fun σ h => by rw [x2_hform_swap12]; exact h.submatrix _
  obtain ⟨a, b, c⟩ := τ
  rcases le_or_gt a b with hab | hab <;> rcases le_or_gt b c with hbc | hbc <;>
    rcases le_or_gt a c with hac | hac
  · exact hsorted _ hab hbc
  · exact absurd (le_trans hab hbc) (not_le.mpr hac)
  · exact s12 _ (hsorted (a, c, b) hac (le_of_lt hbc))
  · -- c < a ≤ b
    exact s12 _ (s01 _ (hsorted (c, a, b) (le_of_lt hac) hab))
  · -- b < a ≤ c
    exact s01 _ (hsorted (b, a, c) (le_of_lt hab) hac)
  · -- b < a, b ≤ c < a
    exact s01 _ (s12 _ (hsorted (b, c, a) hbc (le_of_lt hac)))
  · exact absurd (lt_trans hbc hab) (not_lt.mpr hac)
  · -- c < b < a
    exact s01 _ (s12 _ (s01 _ (hsorted (c, b, a) (le_of_lt hbc) (le_of_lt hab))))

end ThreeCopyQutritWerner

end
