module

public import ThreeCopyQutritWerner.CertificateX2BridgeHBlock
public import ThreeCopyQutritWerner.CertificateX2BridgeSwap

@[expose] public section


/-!
# h type triples with two equal sites

On an h type triple `(a, a, c)` the swap of the two equal sites (`x2SwapMat`) commutes with the
carrier's joint action, the endpoint target form and both transferred forms (the source tensor
is symmetric under the swap, `x2FmVec_swap01`). Its two parts `(1 ± S)/2` then decompose the
h-side form, and `x2_hres_pair2` proves it positive semidefinite from the two keys of the
triple (symmetric and alternating kind) and their image facts.

Images are read at any type triple by a total natural-coordinate lookup (`x2ImageAt`); on the
key's own triple this is `x2ImageFrame` (`x2ImageAt_key`), so the h-block identity holds at
every triple equal to the key's (`x2_hblock_identity_at`).
-/

noncomputable section

open scoped BigOperators Matrix Kronecker ComplexOrder

namespace ThreeCopyQutritWerner

/-! ## Images at a type triple -/

/-- Total lookup of an integer three-site column matrix at natural coordinates. -/
def x2GetZ {p q r : ℕ} {ι : Type*} (V : Matrix (Fin p × Fin q × Fin r) ι ℤ) (i j k : ℕ)
    (c : ι) : ℤ :=
  if h : i < p ∧ j < q ∧ k < r then V (⟨i, h.1⟩, ⟨j, h.2.1⟩, ⟨k, h.2.2⟩) c else 0

/-- The image of an h key read at the frame indices of a type triple. -/
def x2ImageAt (D : X2Data) (τ : Fin 7 × Fin 7 × Fin 7) (b : x2Key 0) :
    Matrix (Fin (certificatePhysicalFrameSystem0.size τ.1 *
      (certificatePhysicalFrameSystem0.size τ.2.1 * certificatePhysicalFrameSystem0.size τ.2.2)))
      (x2Col 0 b) ℂ :=
  Matrix.of fun i c => ((x2GetZ (D.image 0 b) (finProdFinEquiv.symm i).1
    (finProdFinEquiv.symm (finProdFinEquiv.symm i).2).1
    (finProdFinEquiv.symm (finProdFinEquiv.symm i).2).2 c : ℤ) : ℂ)

theorem x2ImageAt_key (D : X2Data) (b : x2Key 0) :
    x2ImageAt D (x2KeyTau b) b = x2ImageFrame D b := by
  ext i c
  simp only [x2ImageAt, x2ImageFrame, Matrix.of_apply, x2GetZ]
  rw [dif_pos ⟨lt_of_lt_of_eq (finProdFinEquiv.symm i).1.isLt (x2_keyTau_size b 0),
    lt_of_lt_of_eq (finProdFinEquiv.symm (finProdFinEquiv.symm i).2).1.isLt (x2_keyTau_size b 1),
    lt_of_lt_of_eq (finProdFinEquiv.symm (finProdFinEquiv.symm i).2).2.isLt (x2_keyTau_size b 2)⟩]
  rfl

theorem x2_hblock_identity_at (D : X2Data)
    (hT0 : ∀ t : Fin 7, certificateLocalDecomposition0Compression certificateEndpointDiagramWeight t =
      Matrix.of fun i j => ((x2LocalTarget (Fin.castSucc t) (Fin.cast (x2_size0 t) i)
        (Fin.cast (x2_size0 t) j) : ℚ) : ℂ))
    (Nm : X2Blocks 1) (Na : X2Blocks 2) (hNm : ∀ k, (Nm k)ᵀ = Nm k) (hNa : ∀ k, (Na k)ᵀ = Na k)
    (τ : Fin 7 × Fin 7 × Fin 7) (b : x2Key 0) (hb : x2KeyTau b = τ) :
    (x2ImageAt D τ b)ᴴ *
        (x2TargetQForm τ - x2TransferQForm D 1 Nm τ - x2TransferQForm D 2 Na τ) * x2ImageAt D τ b =
      x2Complex (x2Residual D Nm Na b) := by
  subst hb
  rw [x2ImageAt_key]
  exact x2_hblock_identity D hT0 Nm Na hNm hNa b

/-! ## Swap invariance on a pair-equal triple -/

theorem x2_tripleSourceAction_swap {n F T : Type*} [Fintype n] [Fintype F] [DecidableEq T]
    (s : CertificatePhysicalFrameSystem n F T)
    (A C : (t : T) → Matrix (Fin (s.size t)) (Fin (s.size t)) ℂ) (a c : T) :
    certificateTripleSourceAction s A A C (a, a, c) * x2SwapMat (s.size a) (s.size c) =
      x2SwapMat (s.size a) (s.size c) * certificateTripleSourceAction s A A C (a, a, c) := by
  unfold certificateTripleSourceAction certificateTensorSourceGram
  exact x2SwapMat_comm_kron (s.size a) (s.size c) (A a) (C c)

theorem x2_carrier_swap (a c : Fin 7) :
    certificateCarrierJointAction0 (a, a, c) *
        x2SwapMat (certificatePhysicalFrameSystem0.size a) (certificatePhysicalFrameSystem0.size c) =
      x2SwapMat (certificatePhysicalFrameSystem0.size a) (certificatePhysicalFrameSystem0.size c) *
        certificateCarrierJointAction0 (a, a, c) := by
  unfold certificateCarrierJointAction0
  rw [Finset.sum_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro p _
  rw [Matrix.smul_mul, Matrix.mul_smul, x2_tripleSourceAction_swap]

theorem x2_target_swap (a c : Fin 7) :
    x2TargetQForm (a, a, c) *
        x2SwapMat (certificatePhysicalFrameSystem0.size a) (certificatePhysicalFrameSystem0.size c) =
      x2SwapMat (certificatePhysicalFrameSystem0.size a) (certificatePhysicalFrameSystem0.size c) *
        x2TargetQForm (a, a, c) := by
  unfold x2TargetQForm certificateThreeSiteFrameSystem0
  rw [x2_metric_tripleSourceAction]
  exact x2_tripleSourceAction_swap certificatePhysicalFrameSystem0 _ _ a c

/-- The source tensor is symmetric under swapping its first two unit arguments. -/
theorem x2FmVec_swap01 (D : X2Data) (s : Fin 3) (N : X2Blocks s) (x : X2U s × X2U s × X2U s) :
    x2FmVec D s N (x.2.1, x.1, x.2.2) = x2FmVec D s N x := by
  have h := x2FullTensor_perm D s N 2 ![x.1.1, x.2.1.1, x.2.2.1]
    ![(x.1.2.1 : ℕ), x.2.1.2.1, x.2.2.2.1] ![(x.1.2.2 : ℕ), x.2.1.2.2, x.2.2.2.2]
  have e1 : (![x.1.1, x.2.1.1, x.2.2.1] ∘ x2Perm3 2) = ![x.2.1.1, x.1.1, x.2.2.1] := by
    funext i
    fin_cases i <;> rfl
  have e2 : (![(x.1.2.1 : ℕ), x.2.1.2.1, x.2.2.2.1] ∘ x2Perm3 2) =
      ![(x.2.1.2.1 : ℕ), x.1.2.1, x.2.2.2.1] := by
    funext i
    fin_cases i <;> rfl
  have e3 : (![(x.1.2.2 : ℕ), x.2.1.2.2, x.2.2.2.2] ∘ x2Perm3 2) =
      ![(x.2.1.2.2 : ℕ), x.1.2.2, x.2.2.2.2] := by
    funext i
    fin_cases i <;> rfl
  rw [e1, e2, e3] at h
  exact h

/-- The transferred tensor is symmetric under swapping its first two unit arguments. -/
theorem x2_transferVec_swap01 (D : X2Data) (s : Fin 3) (N : X2Blocks s) (u v w : X2U 0) :
    ((x2Qu D s ⊗ₖ (x2Qu D s ⊗ₖ x2Qu D s)) *ᵥ x2FmVec D s N) (v, u, w) =
      ((x2Qu D s ⊗ₖ (x2Qu D s ⊗ₖ x2Qu D s)) *ᵥ x2FmVec D s N) (u, v, w) := by
  simp only [Matrix.mulVec, dotProduct, Matrix.kroneckerMap_apply]
  let e : (X2U s × X2U s × X2U s) ≃ (X2U s × X2U s × X2U s) :=
    { toFun := fun x => (x.2.1, x.1, x.2.2), invFun := fun x => (x.2.1, x.1, x.2.2),
      left_inv := fun _ => rfl, right_inv := fun _ => rfl }
  refine Fintype.sum_equiv e _ _ (fun x => ?_)
  show x2Qu D s v x.1 * (x2Qu D s u x.2.1 * x2Qu D s w x.2.2) * x2FmVec D s N x =
    x2Qu D s u x.2.1 * (x2Qu D s v x.1 * x2Qu D s w x.2.2) * x2FmVec D s N (x.2.1, x.1, x.2.2)
  rw [x2FmVec_swap01]
  ring

theorem x2_transferQForm_swap (D : X2Data) (s : Fin 3) (N : X2Blocks s) (a c : Fin 7) :
    x2TransferQForm D s N (a, a, c) *
        x2SwapMat (certificatePhysicalFrameSystem0.size a) (certificatePhysicalFrameSystem0.size c) =
      x2SwapMat (certificatePhysicalFrameSystem0.size a) (certificatePhysicalFrameSystem0.size c) *
        x2TransferQForm D s N (a, a, c) := by
  apply x2SwapMat_comm
  intro i j
  simp only [x2TransferQForm, Matrix.of_apply, x2SwapFirstFun, Equiv.symm_apply_apply]
  rw [x2_transferVec_swap01]

/-! ## Two keys on a pair-equal triple -/

theorem x2_hres_pair2 (D : X2Data)
    (hT0 : ∀ t : Fin 7, certificateLocalDecomposition0Compression certificateEndpointDiagramWeight t =
      Matrix.of fun i j => ((x2LocalTarget (Fin.castSucc t) (Fin.cast (x2_size0 t) i)
        (Fin.cast (x2_size0 t) j) : ℚ) : ℂ))
    (Nm : X2Blocks 1) (Na : X2Blocks 2)
    (hNm : ∀ k, (x2Complex (Nm k)).PosSemidef) (hNa : ∀ k, (x2Complex (Na k)).PosSemidef)
    (a c : Fin 7) (b0 b1 : x2Key 0) (hb0 : x2KeyTau b0 = (a, a, c)) (hb1 : x2KeyTau b1 = (a, a, c))
    (hfix : ∀ k : Bool, certificateCarrierJointAction0 (a, a, c) *
        x2InvolutionPart (x2SwapMat (certificatePhysicalFrameSystem0.size a)
          (certificatePhysicalFrameSystem0.size c)) k * x2ImageAt D (a, a, c) (cond k b1 b0) =
        x2ImageAt D (a, a, c) (cond k b1 b0))
    (hdet : ∀ k : Bool, ((x2ImageAt D (a, a, c) (cond k b1 b0))ᴴ *
        certificateThreeSiteFrameSystem0.metric (a, a, c) * x2ImageAt D (a, a, c) (cond k b1 b0)).det ≠ 0)
    (htr : ∀ k : Bool, (certificateCarrierJointAction0 (a, a, c) *
        x2InvolutionPart (x2SwapMat (certificatePhysicalFrameSystem0.size a)
          (certificatePhysicalFrameSystem0.size c)) k).trace = (x2KeySize 0 (cond k b1 b0) : ℂ))
    (hres : ∀ k : Bool, (x2Complex (x2Residual D Nm Na (cond k b1 b0))).PosSemidef) :
    ((certificateCarrierJointAction0 (a, a, c))ᴴ *
      (x2TargetQForm (a, a, c) - x2TransferQForm D 1 Nm (a, a, c) -
        x2TransferQForm D 2 Na (a, a, c)) * certificateCarrierJointAction0 (a, a, c)).PosSemidef := by
  have hfS : (x2TargetQForm (a, a, c) - x2TransferQForm D 1 Nm (a, a, c) -
        x2TransferQForm D 2 Na (a, a, c)) *
      x2SwapMat (certificatePhysicalFrameSystem0.size a) (certificatePhysicalFrameSystem0.size c) =
      x2SwapMat (certificatePhysicalFrameSystem0.size a) (certificatePhysicalFrameSystem0.size c) *
        (x2TargetQForm (a, a, c) - x2TransferQForm D 1 Nm (a, a, c) -
          x2TransferQForm D 2 Na (a, a, c)) := by
    rw [Matrix.sub_mul, Matrix.sub_mul, Matrix.mul_sub, Matrix.mul_sub, x2_target_swap,
      x2_transferQForm_swap, x2_transferQForm_swap]
  refine x2_posSemidef_of_parts_complex (certificateCarrierJointAction0 (a, a, c))
    (x2TargetQForm (a, a, c) - x2TransferQForm D 1 Nm (a, a, c) - x2TransferQForm D 2 Na (a, a, c))
    (certificateThreeSiteFrameSystem0.metric (a, a, c))
    (x2InvolutionPart (x2SwapMat (certificatePhysicalFrameSystem0.size a)
      (certificatePhysicalFrameSystem0.size c)))
    (x2InvolutionPart_sum _) (certificateCarrierJointAction0_idempotent _)
    (fun k => x2InvolutionPart_comm _ _ (x2_carrier_swap a c) k)
    (x2InvolutionPart_mul _ (x2SwapMat_mul_self _ _))
    (x2InvolutionPart_conjTranspose _ (x2SwapMat_conjTranspose _ _))
    (fun k => x2InvolutionPart_comm _ _ hfS k)
    (fun k => x2ImageAt D (a, a, c) (cond k b1 b0)) hfix hdet
    (fun k => by rw [htr k]; simp) ?_
  intro k
  show ((x2ImageAt D (a, a, c) (cond k b1 b0))ᴴ * (x2TargetQForm (a, a, c) -
    x2TransferQForm D 1 Nm (a, a, c) - x2TransferQForm D 2 Na (a, a, c)) *
      x2ImageAt D (a, a, c) (cond k b1 b0)).PosSemidef
  rw [x2_hblock_identity_at D hT0 Nm Na (fun k => x2_transpose_eq_of_posSemidef _ (hNm k))
    (fun k => x2_transpose_eq_of_posSemidef _ (hNa k)) (a, a, c) (cond k b1 b0)
    (by cases k <;> assumption)]
  exact hres k

end ThreeCopyQutritWerner

end
