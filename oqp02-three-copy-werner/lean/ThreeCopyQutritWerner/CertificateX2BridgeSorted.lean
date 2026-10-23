module

public import ThreeCopyQutritWerner.CertificateX2BridgeCovariance
public import ThreeCopyQutritWerner.CertificateX2BridgeKeyFacts
public import ThreeCopyQutritWerner.CertificateX2BridgeSwapLast

@[expose] public section


/-!
# The h-side form on a sorted type triple from its keys

`x2_hform_of_parts`: on a type triple `τ`, given parts `P k` of the identity (orthogonal
self-adjoint idempotents commuting with the carrier action and the form) and, for each part,
either a key `b` of the triple whose image the carrier part fixes (nondegenerate metric, trace
= number of columns) or nothing (trace zero), the h-side form is positive semidefinite as soon
as the keys' reduced residuals `x2Residual` are.

`x2_hform_distinct`: the case of three distinct types (one part, the identity).
-/

noncomputable section

open scoped BigOperators Matrix Kronecker ComplexOrder

namespace ThreeCopyQutritWerner

/-- Columns of a part: a key's columns, or none. -/
def x2PartCols : Option (x2Key 0) → Type
  | some b => x2Col 0 b
  | none => Fin 0

instance x2PartCols_fintype : (o : Option (x2Key 0)) → Fintype (x2PartCols o)
  | some b => inferInstanceAs (Fintype (x2Col 0 b))
  | none => inferInstanceAs (Fintype (Fin 0))

instance x2PartCols_decEq : (o : Option (x2Key 0)) → DecidableEq (x2PartCols o)
  | some b => inferInstanceAs (DecidableEq (x2Col 0 b))
  | none => inferInstanceAs (DecidableEq (Fin 0))

instance x2PartCols_none_isEmpty : IsEmpty (x2PartCols none) :=
  inferInstanceAs (IsEmpty (Fin 0))

/-- The image of a part's key at a type triple (empty without a key). -/
def x2PartImage (D : X2Data) (τ : Fin 7 × Fin 7 × Fin 7) :
    (o : Option (x2Key 0)) → Matrix (Fin (certificatePhysicalFrameSystem0.size τ.1 *
      (certificatePhysicalFrameSystem0.size τ.2.1 * certificatePhysicalFrameSystem0.size τ.2.2)))
      (x2PartCols o) ℂ
  | some b => x2ImageAt D τ b
  | none => 0

/-- Number of columns of a part. -/
def x2PartSize : Option (x2Key 0) → ℕ
  | some b => x2KeySize 0 b
  | none => 0

theorem x2PartCols_card (o : Option (x2Key 0)) : Fintype.card (x2PartCols o) = x2PartSize o := by
  cases o with
  | none => exact Fintype.card_fin 0
  | some b => exact Fintype.card_fin _

/-- PARTS ON A TYPE TRIPLE: positivity of the h-side form from keyed parts. -/
theorem x2_hform_of_parts (D : X2Data)
    (hT0 : ∀ t : Fin 7, certificateLocalDecomposition0Compression certificateEndpointDiagramWeight t =
      Matrix.of fun i j => ((x2LocalTarget (Fin.castSucc t) (Fin.cast (x2_size0 t) i)
        (Fin.cast (x2_size0 t) j) : ℚ) : ℂ))
    (Nm : X2Blocks 1) (Na : X2Blocks 2)
    (hNm : ∀ k, (x2Complex (Nm k)).PosSemidef) (hNa : ∀ k, (x2Complex (Na k)).PosSemidef)
    (τ : Fin 7 × Fin 7 × Fin 7) {κ : Type} [Fintype κ] [DecidableEq κ]
    (P : κ → Matrix (Fin (certificatePhysicalFrameSystem0.size τ.1 *
      (certificatePhysicalFrameSystem0.size τ.2.1 * certificatePhysicalFrameSystem0.size τ.2.2)))
      (Fin (certificatePhysicalFrameSystem0.size τ.1 *
      (certificatePhysicalFrameSystem0.size τ.2.1 * certificatePhysicalFrameSystem0.size τ.2.2))) ℂ)
    (hsum : ∑ k, P k = 1)
    (hπP : ∀ k, certificateCarrierJointAction0 τ * P k = P k * certificateCarrierJointAction0 τ)
    (hPP : ∀ k l, P k * P l = if k = l then P k else 0) (hPt : ∀ k, (P k)ᴴ = P k)
    (hfP : ∀ k, (x2TargetQForm τ - x2TransferQForm D 1 Nm τ - x2TransferQForm D 2 Na τ) * P k =
      P k * (x2TargetQForm τ - x2TransferQForm D 1 Nm τ - x2TransferQForm D 2 Na τ))
    (keyOf : κ → Option (x2Key 0)) (hkey : ∀ k b, keyOf k = some b → x2KeyTau b = τ)
    (hfix : ∀ k b, keyOf k = some b →
      certificateCarrierJointAction0 τ * P k * x2ImageAt D τ b = x2ImageAt D τ b)
    (hdet : ∀ k b, keyOf k = some b →
      ((x2ImageAt D τ b)ᴴ * certificateThreeSiteFrameSystem0.metric τ * x2ImageAt D τ b).det ≠ 0)
    (htr : ∀ k, (certificateCarrierJointAction0 τ * P k).trace = (x2PartSize (keyOf k) : ℂ))
    (hres : ∀ b, (x2Complex (x2Residual D Nm Na b)).PosSemidef) :
    (x2HForm D Nm Na τ).PosSemidef := by
  refine x2_posSemidef_of_parts_complex (certificateCarrierJointAction0 τ)
    (x2TargetQForm τ - x2TransferQForm D 1 Nm τ - x2TransferQForm D 2 Na τ)
    (certificateThreeSiteFrameSystem0.metric τ) P hsum (certificateCarrierJointAction0_idempotent _)
    hπP hPP hPt hfP (fun k => x2PartImage D τ (keyOf k)) ?_ ?_ ?_ ?_
  · intro k
    show certificateCarrierJointAction0 τ * P k * x2PartImage D τ (keyOf k) = x2PartImage D τ (keyOf k)
    generalize ho : keyOf k = o
    cases o with
    | none => simp only [x2PartImage, Matrix.mul_zero]
    | some b => exact hfix k b ho
  · intro k
    show ((x2PartImage D τ (keyOf k))ᴴ * certificateThreeSiteFrameSystem0.metric τ *
      x2PartImage D τ (keyOf k)).det ≠ 0
    generalize ho : keyOf k = o
    cases o with
    | none => rw [Matrix.det_isEmpty]; exact one_ne_zero
    | some b => exact hdet k b ho
  · intro k
    rw [htr k, x2PartCols_card]
  · intro k
    show ((x2PartImage D τ (keyOf k))ᴴ * (x2TargetQForm τ - x2TransferQForm D 1 Nm τ -
      x2TransferQForm D 2 Na τ) * x2PartImage D τ (keyOf k)).PosSemidef
    generalize ho : keyOf k = o
    cases o with
    | none =>
        have : ((x2PartImage D τ none)ᴴ * (x2TargetQForm τ - x2TransferQForm D 1 Nm τ -
            x2TransferQForm D 2 Na τ) * x2PartImage D τ none) = 0 := by
          ext i j
          exact isEmptyElim i
        rw [this]
        exact Matrix.PosSemidef.zero
    | some b =>
        show ((x2ImageAt D τ b)ᴴ * (x2TargetQForm τ - x2TransferQForm D 1 Nm τ -
          x2TransferQForm D 2 Na τ) * x2ImageAt D τ b).PosSemidef
        rw [x2_hblock_identity_at D hT0 Nm Na (fun k => x2_transpose_eq_of_posSemidef _ (hNm k))
          (fun k => x2_transpose_eq_of_posSemidef _ (hNa k)) τ b (hkey k b ho)]
        exact hres b

/-- Three distinct types: one part (the identity), carried by the triple's key or by nothing. -/
theorem x2_hform_distinct (D : X2Data)
    (hT0 : ∀ t : Fin 7, certificateLocalDecomposition0Compression certificateEndpointDiagramWeight t =
      Matrix.of fun i j => ((x2LocalTarget (Fin.castSucc t) (Fin.cast (x2_size0 t) i)
        (Fin.cast (x2_size0 t) j) : ℚ) : ℂ))
    (Nm : X2Blocks 1) (Na : X2Blocks 2)
    (hNm : ∀ k, (x2Complex (Nm k)).PosSemidef) (hNa : ∀ k, (x2Complex (Na k)).PosSemidef)
    (τ : Fin 7 × Fin 7 × Fin 7) (o : Option (x2Key 0))
    (hkey : ∀ b, o = some b → x2KeyTau b = τ)
    (hfix : ∀ b, o = some b →
      certificateCarrierJointAction0 τ * x2ImageAt D τ b = x2ImageAt D τ b)
    (hdet : ∀ b, o = some b →
      ((x2ImageAt D τ b)ᴴ * certificateThreeSiteFrameSystem0.metric τ * x2ImageAt D τ b).det ≠ 0)
    (htr : (certificateCarrierJointAction0 τ).trace = (x2PartSize o : ℂ))
    (hres : ∀ b, (x2Complex (x2Residual D Nm Na b)).PosSemidef) :
    (x2HForm D Nm Na τ).PosSemidef :=
  x2_hform_of_parts D hT0 Nm Na hNm hNa τ (κ := Unit) (fun _ => 1) (by simp) (fun _ => by simp)
    (fun _ _ => by simp) (fun _ => by simp) (fun _ => by simp) (fun _ => o)
    (fun _ b h => hkey b h) (fun _ b h => by simpa only [Matrix.mul_one] using hfix b h)
    (fun _ b h => hdet b h) (fun _ => by simpa only [Matrix.mul_one] using htr) hres

/-! ## Two equal leading sites -/

theorem x2FrameCoords_injective (τ : Fin 7 × Fin 7 × Fin 7)
    (i j : Fin (certificatePhysicalFrameSystem0.size τ.1 *
      (certificatePhysicalFrameSystem0.size τ.2.1 * certificatePhysicalFrameSystem0.size τ.2.2)))
    (h : x2FrameCoords τ i = x2FrameCoords τ j) : i = j := by
  have h0 : ((finProdFinEquiv.symm i).1 : ℕ) = ((finProdFinEquiv.symm j).1 : ℕ) := congrFun h 0
  have h1 : ((finProdFinEquiv.symm (finProdFinEquiv.symm i).2).1 : ℕ) =
      ((finProdFinEquiv.symm (finProdFinEquiv.symm j).2).1 : ℕ) := congrFun h 1
  have h2 : ((finProdFinEquiv.symm (finProdFinEquiv.symm i).2).2 : ℕ) =
      ((finProdFinEquiv.symm (finProdFinEquiv.symm j).2).2 : ℕ) := congrFun h 2
  apply finProdFinEquiv.symm.injective
  apply Prod.ext (Fin.ext h0)
  apply finProdFinEquiv.symm.injective
  exact Prod.ext (Fin.ext h1) (Fin.ext h2)

theorem x2SlotPermFrame_swap01_eq (a c : Fin 7) :
    x2SlotPermFrame (a, a, c) x2Swap01Idx =
      x2SwapMat (certificatePhysicalFrameSystem0.size a) (certificatePhysicalFrameSystem0.size c) := by
  ext i j
  simp only [x2SlotPermFrame, x2SwapMat, Matrix.of_apply]
  have hcoords : x2FrameCoords (a, a, c) (x2SwapFirstFun _ _ i) =
      x2FrameCoords (a, a, c) i ∘ x2Perm3 x2Swap01Idx := by
    funext k
    fin_cases k <;> simp [x2FrameCoords, x2SwapFirstFun, x2Swap01Idx, x2Perm3]
  by_cases h : x2SwapFirstFun _ _ i = j
  · rw [if_pos h, if_pos (by rw [← h, hcoords])]
  · rw [if_neg h, if_neg]
    intro h'
    apply h
    exact x2FrameCoords_injective _ _ _ (by rw [hcoords, h'])

theorem x2KindProjFrame_pair01 (a c : Fin 7) (hac : a ≠ c) (b : Bool) :
    x2KindProjFrame (a, a, c) (if b then 1 else 0) =
      x2InvolutionPart (x2SwapMat (certificatePhysicalFrameSystem0.size a)
        (certificatePhysicalFrameSystem0.size c)) b := by
  unfold x2KindProjFrame x2InvolutionPart
  simp only [hac, and_false, if_false, if_true, x2SlotPermFrame_swap01_eq]
  cases b <;> simp

/-- Two equal leading sites `(a, a, c)`, `a ≠ c`: the symmetric and alternating parts, each
carried by the triple's key of that kind or by nothing. -/
theorem x2_hform_pair01 (D : X2Data)
    (hT0 : ∀ t : Fin 7, certificateLocalDecomposition0Compression certificateEndpointDiagramWeight t =
      Matrix.of fun i j => ((x2LocalTarget (Fin.castSucc t) (Fin.cast (x2_size0 t) i)
        (Fin.cast (x2_size0 t) j) : ℚ) : ℂ))
    (Nm : X2Blocks 1) (Na : X2Blocks 2)
    (hNm : ∀ k, (x2Complex (Nm k)).PosSemidef) (hNa : ∀ k, (x2Complex (Na k)).PosSemidef)
    (a c : Fin 7) (hac : a ≠ c) (keyOf : Bool → Option (x2Key 0))
    (hkey : ∀ k b, keyOf k = some b → x2KeyTau b = (a, a, c))
    (hcar : ∀ k b, keyOf k = some b →
      certificateCarrierJointAction0 (a, a, c) * x2ImageAt D (a, a, c) b = x2ImageAt D (a, a, c) b)
    (hkind : ∀ k b, keyOf k = some b →
      x2KindProjFrame (a, a, c) (if k then 1 else 0) * x2ImageAt D (a, a, c) b = x2ImageAt D (a, a, c) b)
    (hdet : ∀ k b, keyOf k = some b → ((x2ImageAt D (a, a, c) b)ᴴ *
      certificateThreeSiteFrameSystem0.metric (a, a, c) * x2ImageAt D (a, a, c) b).det ≠ 0)
    (htr : ∀ k, (certificateCarrierJointAction0 (a, a, c) *
      x2KindProjFrame (a, a, c) (if k then 1 else 0)).trace = (x2PartSize (keyOf k) : ℂ))
    (hres : ∀ b, (x2Complex (x2Residual D Nm Na b)).PosSemidef) :
    (x2HForm D Nm Na (a, a, c)).PosSemidef := by
  have hS := x2SwapMat_mul_self (certificatePhysicalFrameSystem0.size a) (certificatePhysicalFrameSystem0.size c)
  have hSt := x2SwapMat_conjTranspose (certificatePhysicalFrameSystem0.size a)
    (certificatePhysicalFrameSystem0.size c)
  have hfS : (x2TargetQForm (a, a, c) - x2TransferQForm D 1 Nm (a, a, c) -
        x2TransferQForm D 2 Na (a, a, c)) *
      x2SwapMat (certificatePhysicalFrameSystem0.size a) (certificatePhysicalFrameSystem0.size c) =
      x2SwapMat (certificatePhysicalFrameSystem0.size a) (certificatePhysicalFrameSystem0.size c) *
        (x2TargetQForm (a, a, c) - x2TransferQForm D 1 Nm (a, a, c) -
          x2TransferQForm D 2 Na (a, a, c)) := by
    rw [Matrix.sub_mul, Matrix.sub_mul, Matrix.mul_sub, Matrix.mul_sub, x2_target_swap,
      x2_transferQForm_swap, x2_transferQForm_swap]
  refine x2_hform_of_parts D hT0 Nm Na hNm hNa (a, a, c)
    (fun k : Bool => x2KindProjFrame (a, a, c) (if k then 1 else 0)) ?_ ?_ ?_ ?_ ?_ keyOf hkey ?_ hdet
    htr hres
  · simp only [x2KindProjFrame_pair01 a c hac]
    exact x2InvolutionPart_sum _
  · intro k
    simp only [x2KindProjFrame_pair01 a c hac]
    exact x2InvolutionPart_comm _ _ (x2_carrier_swap a c) k
  · intro k l
    simp only [x2KindProjFrame_pair01 a c hac]
    exact x2InvolutionPart_mul _ hS k l
  · intro k
    simp only [x2KindProjFrame_pair01 a c hac]
    exact x2InvolutionPart_conjTranspose _ hSt k
  · intro k
    simp only [x2KindProjFrame_pair01 a c hac]
    exact x2InvolutionPart_comm _ _ hfS k
  · intro k b h
    rw [Matrix.mul_assoc, hkind k b h, hcar k b h]

/-! ## Two equal trailing sites -/

theorem x2_tripleSourceAction_swapLast {n F T : Type*} [Fintype n] [Fintype F] [DecidableEq T]
    (s : CertificatePhysicalFrameSystem n F T)
    (A C : (t : T) → Matrix (Fin (s.size t)) (Fin (s.size t)) ℂ) (a c : T) :
    certificateTripleSourceAction s A C C (a, c, c) * x2SwapLastMat (s.size a) (s.size c) =
      x2SwapLastMat (s.size a) (s.size c) * certificateTripleSourceAction s A C C (a, c, c) := by
  unfold certificateTripleSourceAction certificateTensorSourceGram
  exact x2SwapLastMat_comm_kron (s.size a) (s.size c) (A a) (C c)

theorem x2_carrier_swapLast (a c : Fin 7) :
    certificateCarrierJointAction0 (a, c, c) *
        x2SwapLastMat (certificatePhysicalFrameSystem0.size a) (certificatePhysicalFrameSystem0.size c) =
      x2SwapLastMat (certificatePhysicalFrameSystem0.size a) (certificatePhysicalFrameSystem0.size c) *
        certificateCarrierJointAction0 (a, c, c) := by
  unfold certificateCarrierJointAction0
  rw [Finset.sum_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro p _
  rw [Matrix.smul_mul, Matrix.mul_smul, x2_tripleSourceAction_swapLast]

theorem x2_target_swapLast (a c : Fin 7) :
    x2TargetQForm (a, c, c) *
        x2SwapLastMat (certificatePhysicalFrameSystem0.size a) (certificatePhysicalFrameSystem0.size c) =
      x2SwapLastMat (certificatePhysicalFrameSystem0.size a) (certificatePhysicalFrameSystem0.size c) *
        x2TargetQForm (a, c, c) := by
  unfold x2TargetQForm certificateThreeSiteFrameSystem0
  rw [x2_metric_tripleSourceAction]
  exact x2_tripleSourceAction_swapLast certificatePhysicalFrameSystem0 _ _ a c

theorem x2_transferQForm_swapLast (D : X2Data) (s : Fin 3) (N : X2Blocks s) (a c : Fin 7) :
    x2TransferQForm D s N (a, c, c) *
        x2SwapLastMat (certificatePhysicalFrameSystem0.size a) (certificatePhysicalFrameSystem0.size c) =
      x2SwapLastMat (certificatePhysicalFrameSystem0.size a) (certificatePhysicalFrameSystem0.size c) *
        x2TransferQForm D s N (a, c, c) := by
  apply x2SwapLastMat_comm
  intro i j
  simp only [x2TransferQForm, Matrix.of_apply, x2SwapLastFun, Equiv.symm_apply_apply]
  rw [x2_transferVec_swap12]

theorem x2SlotPermFrame_swap12_eq (a c : Fin 7) :
    x2SlotPermFrame (a, c, c) x2Swap12Idx =
      x2SwapLastMat (certificatePhysicalFrameSystem0.size a) (certificatePhysicalFrameSystem0.size c) := by
  ext i j
  simp only [x2SlotPermFrame, x2SwapLastMat, Matrix.of_apply]
  have hcoords : x2FrameCoords (a, c, c) (x2SwapLastFun _ _ i) =
      x2FrameCoords (a, c, c) i ∘ x2Perm3 x2Swap12Idx := by
    funext k
    fin_cases k <;> simp [x2FrameCoords, x2SwapLastFun, x2Swap12Idx, x2Perm3]
  by_cases h : x2SwapLastFun _ _ i = j
  · rw [if_pos h, if_pos (by rw [← h, hcoords])]
  · rw [if_neg h, if_neg]
    intro h'
    apply h
    exact x2FrameCoords_injective _ _ _ (by rw [hcoords, h'])

theorem x2KindProjFrame_pair12 (a c : Fin 7) (hac : a ≠ c) (b : Bool) :
    x2KindProjFrame (a, c, c) (if b then 1 else 0) =
      x2InvolutionPart (x2SwapLastMat (certificatePhysicalFrameSystem0.size a)
        (certificatePhysicalFrameSystem0.size c)) b := by
  unfold x2KindProjFrame x2InvolutionPart
  simp only [hac, false_and, if_false, if_true, x2SlotPermFrame_swap12_eq]
  cases b <;> simp

/-- Two equal trailing sites `(a, c, c)`, `a ≠ c`. -/
theorem x2_hform_pair12 (D : X2Data)
    (hT0 : ∀ t : Fin 7, certificateLocalDecomposition0Compression certificateEndpointDiagramWeight t =
      Matrix.of fun i j => ((x2LocalTarget (Fin.castSucc t) (Fin.cast (x2_size0 t) i)
        (Fin.cast (x2_size0 t) j) : ℚ) : ℂ))
    (Nm : X2Blocks 1) (Na : X2Blocks 2)
    (hNm : ∀ k, (x2Complex (Nm k)).PosSemidef) (hNa : ∀ k, (x2Complex (Na k)).PosSemidef)
    (a c : Fin 7) (hac : a ≠ c) (keyOf : Bool → Option (x2Key 0))
    (hkey : ∀ k b, keyOf k = some b → x2KeyTau b = (a, c, c))
    (hcar : ∀ k b, keyOf k = some b →
      certificateCarrierJointAction0 (a, c, c) * x2ImageAt D (a, c, c) b = x2ImageAt D (a, c, c) b)
    (hkind : ∀ k b, keyOf k = some b →
      x2KindProjFrame (a, c, c) (if k then 1 else 0) * x2ImageAt D (a, c, c) b = x2ImageAt D (a, c, c) b)
    (hdet : ∀ k b, keyOf k = some b → ((x2ImageAt D (a, c, c) b)ᴴ *
      certificateThreeSiteFrameSystem0.metric (a, c, c) * x2ImageAt D (a, c, c) b).det ≠ 0)
    (htr : ∀ k, (certificateCarrierJointAction0 (a, c, c) *
      x2KindProjFrame (a, c, c) (if k then 1 else 0)).trace = (x2PartSize (keyOf k) : ℂ))
    (hres : ∀ b, (x2Complex (x2Residual D Nm Na b)).PosSemidef) :
    (x2HForm D Nm Na (a, c, c)).PosSemidef := by
  have hS := x2SwapLastMat_mul_self (certificatePhysicalFrameSystem0.size a)
    (certificatePhysicalFrameSystem0.size c)
  have hSt := x2SwapLastMat_conjTranspose (certificatePhysicalFrameSystem0.size a)
    (certificatePhysicalFrameSystem0.size c)
  have hfS : (x2TargetQForm (a, c, c) - x2TransferQForm D 1 Nm (a, c, c) -
        x2TransferQForm D 2 Na (a, c, c)) *
      x2SwapLastMat (certificatePhysicalFrameSystem0.size a) (certificatePhysicalFrameSystem0.size c) =
      x2SwapLastMat (certificatePhysicalFrameSystem0.size a) (certificatePhysicalFrameSystem0.size c) *
        (x2TargetQForm (a, c, c) - x2TransferQForm D 1 Nm (a, c, c) -
          x2TransferQForm D 2 Na (a, c, c)) := by
    rw [Matrix.sub_mul, Matrix.sub_mul, Matrix.mul_sub, Matrix.mul_sub, x2_target_swapLast,
      x2_transferQForm_swapLast, x2_transferQForm_swapLast]
  refine x2_hform_of_parts D hT0 Nm Na hNm hNa (a, c, c)
    (fun k : Bool => x2KindProjFrame (a, c, c) (if k then 1 else 0)) ?_ ?_ ?_ ?_ ?_ keyOf hkey ?_ hdet
    htr hres
  · simp only [x2KindProjFrame_pair12 a c hac]
    exact x2InvolutionPart_sum _
  · intro k
    simp only [x2KindProjFrame_pair12 a c hac]
    exact x2InvolutionPart_comm _ _ (x2_carrier_swapLast a c) k
  · intro k l
    simp only [x2KindProjFrame_pair12 a c hac]
    exact x2InvolutionPart_mul _ hS k l
  · intro k
    simp only [x2KindProjFrame_pair12 a c hac]
    exact x2InvolutionPart_conjTranspose _ hSt k
  · intro k
    simp only [x2KindProjFrame_pair12 a c hac]
    exact x2InvolutionPart_comm _ _ hfS k
  · intro k b h
    rw [Matrix.mul_assoc, hkind k b h, hcar k b h]

end ThreeCopyQutritWerner

end
