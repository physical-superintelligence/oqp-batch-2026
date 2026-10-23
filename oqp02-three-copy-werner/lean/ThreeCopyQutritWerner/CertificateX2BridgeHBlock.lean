module

public import ThreeCopyQutritWerner.CertificateX2BridgeMain
public import ThreeCopyQutritWerner.CertificateX2BridgeHSideC

@[expose] public section


/-!
# The h-side forms on the image of an h key are the reduced residual blocks

For an h key `b` with type triple `τ_b`, read the image `J_b` in frame coordinates of `τ_b`
(`x2ImageFrame`; a frame index is the row-major ambient index). Then the compressed h-side form of
`x2_qutritEndpointInequality_of_hside` on `J_b` is exactly the published reduced residual block:

`J_bᴴ (T_τ - Q₁_τ - Q₂_τ) J_b = x2Residual D Nm Na b` (`x2_hblock_identity`),

given the per-site target identity (the original-frame compression of the endpoint weight is
`x2LocalTarget`, a finite fact) and symmetric source blocks (implied by their positivity,
`x2_transpose_eq_of_posSemidef`).
-/

noncomputable section

open scoped BigOperators Matrix Kronecker ComplexOrder

namespace ThreeCopyQutritWerner

theorem x2_keyTypes_lt7 : ∀ b : x2Key 0, ∀ i : Fin 3, (x2KeyTypes 0 b i : ℕ) < 7 := by
  decide +kernel

/-- The h type triple of an h key. -/
def x2KeyTau (b : x2Key 0) : Fin 7 × Fin 7 × Fin 7 :=
  (⟨x2KeyTypes 0 b 0, x2_keyTypes_lt7 b 0⟩, ⟨x2KeyTypes 0 b 1, x2_keyTypes_lt7 b 1⟩,
    ⟨x2KeyTypes 0 b 2, x2_keyTypes_lt7 b 2⟩)

theorem x2_keyTau_size (b : x2Key 0) (i : Fin 3) :
    certificatePhysicalFrameSystem0.size (⟨x2KeyTypes 0 b i, x2_keyTypes_lt7 b i⟩ : Fin 7) =
      x2KeyMult 0 b i := by
  have h := x2_size0 ⟨x2KeyTypes 0 b i, x2_keyTypes_lt7 b i⟩
  have hc : (Fin.castSucc (⟨x2KeyTypes 0 b i, x2_keyTypes_lt7 b i⟩ : Fin 7) : Fin 8) =
      x2KeyTypes 0 b i := Fin.ext rfl
  rw [hc] at h
  exact h

/-- Frame indices of a key's type triple are its ambient coordinates (row-major). -/
def x2DecKey (b : x2Key 0) :
    Fin (certificatePhysicalFrameSystem0.size (x2KeyTau b).1 *
      (certificatePhysicalFrameSystem0.size (x2KeyTau b).2.1 *
        certificatePhysicalFrameSystem0.size (x2KeyTau b).2.2)) ≃ x2Amb 0 b :=
  (finProdFinEquiv.symm.trans ((Equiv.refl _).prodCongr finProdFinEquiv.symm)).trans
    ((finCongr (x2_keyTau_size b 0)).prodCongr
      ((finCongr (x2_keyTau_size b 1)).prodCongr (finCongr (x2_keyTau_size b 2))))

/-- The image of an h key in frame coordinates. -/
def x2ImageFrame (D : X2Data) (b : x2Key 0) :
    Matrix (Fin (certificatePhysicalFrameSystem0.size (x2KeyTau b).1 *
      (certificatePhysicalFrameSystem0.size (x2KeyTau b).2.1 *
        certificatePhysicalFrameSystem0.size (x2KeyTau b).2.2))) (x2Col 0 b) ℂ :=
  Matrix.of fun i c => ((D.image 0 b (x2DecKey b i) c : ℤ) : ℂ)

/-- Positive semidefinite rational blocks are symmetric. -/
theorem x2_transpose_eq_of_posSemidef {n : Type*} [Fintype n] (M : Matrix n n ℚ)
    (h : (x2Complex M).PosSemidef) : Mᵀ = M := by
  have hh := h.isHermitian
  ext i j
  have e := congrFun (congrFun hh.eq i) j
  have e2 := congrArg Complex.re e
  simp only [x2Complex, Matrix.conjTranspose_apply, Matrix.map_apply, RCLike.star_def,
    Complex.conj_re, Complex.ratCast_re] at e2
  rw [Matrix.transpose_apply]
  exact Rat.cast_injective e2

/-- Congruence by a reindexed integer image is the reindexed congruence. -/
theorem x2_reindex_congr {n n' r : Type*} [Fintype n] [Fintype n'] [Fintype r] [DecidableEq n]
    (e : n' ≃ n) (J : Matrix n r ℤ) (F : Matrix n n ℚ) :
    (Matrix.of fun i c => ((J (e i) c : ℤ) : ℂ))ᴴ * (x2Complex F).submatrix e e *
        (Matrix.of fun i c => ((J (e i) c : ℤ) : ℂ)) =
      x2Complex ((J.map (Int.cast : ℤ → ℚ))ᵀ * F * J.map (Int.cast : ℤ → ℚ)) := by
  ext a c
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.of_apply,
    Matrix.submatrix_apply, x2Complex, Matrix.map_apply, Matrix.transpose_apply]
  push_cast
  try simp only [star_intCast]
  rw [← Equiv.sum_comp e]
  apply Finset.sum_congr rfl
  intro x _
  congr 1
  rw [← Equiv.sum_comp e]

/-- The transferred h form on a key's type triple is the key's raw block, reindexed. -/
theorem x2_transferQForm_key (D : X2Data) (s : Fin 3) (N : X2Blocks s)
    (hN : ∀ k, (N k)ᵀ = N k) (b : x2Key 0) :
    x2TransferQForm D s N (x2KeyTau b) =
      (x2Complex (x2RawH (x2TransferS D s N) (x2TransferA D s N) b)).submatrix
        (x2DecKey b) (x2DecKey b) := by
  ext i j
  simp only [Matrix.submatrix_apply, x2Complex, Matrix.map_apply]
  rw [x2RawH_eq_unitTransfer D s N hN b]
  rfl

/-- THE H-BLOCK IDENTITY: on the image of an h key, the h-side form is the reduced residual. -/
theorem x2_hblock_identity (D : X2Data)
    (hT0 : ∀ t : Fin 7, certificateLocalDecomposition0Compression certificateEndpointDiagramWeight t =
      Matrix.of fun i j => ((x2LocalTarget (Fin.castSucc t) (Fin.cast (x2_size0 t) i)
        (Fin.cast (x2_size0 t) j) : ℚ) : ℂ))
    (Nm : X2Blocks 1) (Na : X2Blocks 2) (hNm : ∀ k, (Nm k)ᵀ = Nm k) (hNa : ∀ k, (Na k)ᵀ = Na k)
    (b : x2Key 0) :
    (x2ImageFrame D b)ᴴ *
        (x2TargetQForm (x2KeyTau b) - x2TransferQForm D 1 Nm (x2KeyTau b) -
          x2TransferQForm D 2 Na (x2KeyTau b)) * x2ImageFrame D b =
      x2Complex (x2Residual D Nm Na b) := by
  have hT0' : ∀ t : Fin 7, certificatePhysicalFrameSystem0.metric t *
      certificateLocalDecomposition0Action certificateEndpointDiagramWeight t =
      Matrix.of fun i j => ((x2LocalTarget (Fin.castSucc t) (Fin.cast (x2_size0 t) i)
        (Fin.cast (x2_size0 t) j) : ℚ) : ℂ) :=
    fun t => (certificateLocalDecomposition0metric_action _ t).trans (hT0 t)
  have hT : x2TargetQForm (x2KeyTau b) =
      (x2Complex (x2LocalTarget (x2KeyTypes 0 b 0) ⊗ₖ (x2LocalTarget (x2KeyTypes 0 b 1) ⊗ₖ
        x2LocalTarget (x2KeyTypes 0 b 2)))).submatrix (x2DecKey b) (x2DecKey b) := by
    unfold x2TargetQForm certificateThreeSiteFrameSystem0
    rw [x2_metric_tripleSourceAction]
    simp only [hT0']
    ext i j
    rw [x2_tripleSourceAction_apply]
    simp only [Matrix.of_apply, Matrix.submatrix_apply, x2Complex, Matrix.map_apply,
      Matrix.kroneckerMap_apply]
    push_cast
    rfl
  have hsub : (x2Complex (x2LocalTarget (x2KeyTypes 0 b 0) ⊗ₖ (x2LocalTarget (x2KeyTypes 0 b 1) ⊗ₖ
        x2LocalTarget (x2KeyTypes 0 b 2)))).submatrix (x2DecKey b) (x2DecKey b) -
      (x2Complex (x2RawH (x2TransferS D 1 Nm) (x2TransferA D 1 Nm) b)).submatrix
        (x2DecKey b) (x2DecKey b) -
      (x2Complex (x2RawH (x2TransferS D 2 Na) (x2TransferA D 2 Na) b)).submatrix
        (x2DecKey b) (x2DecKey b) =
      (x2Complex (x2LocalTarget (x2KeyTypes 0 b 0) ⊗ₖ (x2LocalTarget (x2KeyTypes 0 b 1) ⊗ₖ
        x2LocalTarget (x2KeyTypes 0 b 2)) - x2RawH (x2TransferS D 1 Nm) (x2TransferA D 1 Nm) b -
          x2RawH (x2TransferS D 2 Na) (x2TransferA D 2 Na) b)).submatrix
        (x2DecKey b) (x2DecKey b) := by
    ext i j
    simp only [Matrix.sub_apply, Matrix.submatrix_apply, x2Complex, Matrix.map_apply]
    push_cast
    ring
  rw [hT, x2_transferQForm_key D 1 Nm hNm b, x2_transferQForm_key D 2 Na hNa b, hsub]
  unfold x2ImageFrame
  rw [x2_reindex_congr (x2DecKey b) (D.image 0 b)]
  congr 1
  unfold x2Residual x2Target x2Out
  simp only [Matrix.mul_sub, Matrix.sub_mul]
  try rfl

/-- The h-side form vanishes on a type triple where the carrier acts by zero. -/
theorem x2_hres_of_zero (D : X2Data) (Nm : X2Blocks 1) (Na : X2Blocks 2)
    (τ : Fin 7 × Fin 7 × Fin 7) (h : certificateCarrierJointAction0 τ = 0) :
    ((certificateCarrierJointAction0 τ)ᴴ *
      (x2TargetQForm τ - x2TransferQForm D 1 Nm τ - x2TransferQForm D 2 Na τ) *
        certificateCarrierJointAction0 τ).PosSemidef := by
  rw [h, Matrix.mul_zero]
  exact Matrix.PosSemidef.zero

/-- A type triple carried by a single key (one part, the whole carrier range): the h-side form is
positive semidefinite when the key's reduced residual is, given the key's image facts (the
carrier fixes the image, nondegenerate metric, trace of the carrier = number of columns). -/
theorem x2_hres_single (D : X2Data)
    (hT0 : ∀ t : Fin 7, certificateLocalDecomposition0Compression certificateEndpointDiagramWeight t =
      Matrix.of fun i j => ((x2LocalTarget (Fin.castSucc t) (Fin.cast (x2_size0 t) i)
        (Fin.cast (x2_size0 t) j) : ℚ) : ℂ))
    (Nm : X2Blocks 1) (Na : X2Blocks 2)
    (hNm : ∀ k, (x2Complex (Nm k)).PosSemidef) (hNa : ∀ k, (x2Complex (Na k)).PosSemidef)
    (b : x2Key 0)
    (hfix : certificateCarrierJointAction0 (x2KeyTau b) * x2ImageFrame D b = x2ImageFrame D b)
    (hdet : ((x2ImageFrame D b)ᴴ * certificateThreeSiteFrameSystem0.metric (x2KeyTau b) *
      x2ImageFrame D b).det ≠ 0)
    (htr : (certificateCarrierJointAction0 (x2KeyTau b)).trace = (x2KeySize 0 b : ℂ))
    (hres : (x2Complex (x2Residual D Nm Na b)).PosSemidef) :
    ((certificateCarrierJointAction0 (x2KeyTau b))ᴴ *
      (x2TargetQForm (x2KeyTau b) - x2TransferQForm D 1 Nm (x2KeyTau b) -
        x2TransferQForm D 2 Na (x2KeyTau b)) * certificateCarrierJointAction0 (x2KeyTau b)).PosSemidef := by
  have hid := x2_hblock_identity D hT0 Nm Na (fun k => x2_transpose_eq_of_posSemidef _ (hNm k))
    (fun k => x2_transpose_eq_of_posSemidef _ (hNa k)) b
  refine x2_posSemidef_of_parts_complex (certificateCarrierJointAction0 (x2KeyTau b))
    (x2TargetQForm (x2KeyTau b) - x2TransferQForm D 1 Nm (x2KeyTau b) -
      x2TransferQForm D 2 Na (x2KeyTau b))
    (certificateThreeSiteFrameSystem0.metric (x2KeyTau b)) (fun _ : Unit => 1)
    (by simp) (certificateCarrierJointAction0_idempotent _) (fun _ => by simp)
    (fun _ _ => by simp) (fun _ => by simp) (fun _ => by simp)
    (fun _ : Unit => x2ImageFrame D b) (fun _ => by simpa only [Matrix.mul_one] using hfix)
    (fun _ => hdet) (fun _ => by simp only [Matrix.mul_one]; rw [htr]; simp)
    (fun _ => by rw [hid]; exact hres)

end ThreeCopyQutritWerner

end
