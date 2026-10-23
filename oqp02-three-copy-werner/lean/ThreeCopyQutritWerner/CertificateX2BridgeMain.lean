module

public import ThreeCopyQutritWerner.CertificateX2BridgeTransfer
public import ThreeCopyQutritWerner.CertificateX2BridgeSourcePsd
public import ThreeCopyQutritWerner.CertificateEndpointDiagram
public import ThreeCopyQutritWerner.CertificateCarrierJointProjectors

@[expose] public section


/-!
# The endpoint inequality from the reduced transfer and the h-side residuals

The source Grams are built from per-site unit weights `wU` (diagram weights whose original-frame
compression in their own sector is the matrix unit `E_u`): `Gm = ∑_v F_m(v) X_{v₀} ⊗ X_{v₁} ⊗ X_{v₂}`
with `F_m = x2FmVec D 1 Nm` the source Q-form tensor of the reduced statement, and the same for
`Ga`. Then

* `Gm`, `Ga` are positive semidefinite when the source blocks `Nm`, `Na` are
  (`x2_sourceGram1_qform`, `x2SourceBlock_posSemidef`);
* with the per-site dictionary `Compression₀ (wU u) = ∑_{u'} Q_s[u', u] E_{u'}`, the Q-form of
  `Γ₃₄ Gm` on an h type triple `τ` is the transferred tensor `(Q ⊗ Q ⊗ Q) F_m` read on `τ`
  (`x2TransferQForm`, `x2_transfer_qform`): exactly the published pipeline
  (`x2RawH_eq_unitTransfer`);
* by the carrier's metric self-adjointness, the residual's Q-form on `τ` is
  `πᴴ (T_τ - Q₁_τ - Q₂_τ) π`.

`x2_qutritEndpointInequality_of_hside` proves T2.1a from the per-site unit/dictionary identities,
positive source blocks and positivity of these h-side forms on every h type triple. The per-site
identities are finite facts about the certificate's frames; the h-side positivity is what the
reduced residual blocks `x2Residual` provide through the image facts (CertificateX2BridgeHSide).
-/

noncomputable section

open scoped BigOperators Matrix Kronecker ComplexOrder

namespace ThreeCopyQutritWerner

theorem x2_size0 : ∀ t : Fin 7, certificateDescendantFrames2SourceSize t = x2Mult 0 (Fin.castSucc t) := by
  decide +kernel

theorem x2_size1 : ∀ t : Fin 8, certificateDescendantFrames1SourceSize t = x2Mult 1 t := by
  decide +kernel

theorem x2_size2 : ∀ t : Fin 7, certificateDescendantFrames2SourceSize t = x2Mult 2 (Fin.castSucc t) := by
  decide +kernel

/-- Decode an m frame index into the reduced ambient. -/
def x2Dec1 (t : Fin 8 × Fin 8 × Fin 8)
    (i : Fin (certificatePhysicalFrameSystem1.size t.1 *
      (certificatePhysicalFrameSystem1.size t.2.1 * certificatePhysicalFrameSystem1.size t.2.2))) :
    Fin (x2Mult 1 t.1) × Fin (x2Mult 1 t.2.1) × Fin (x2Mult 1 t.2.2) :=
  (Fin.cast (x2_size1 t.1) (finProdFinEquiv.symm i).1,
    Fin.cast (x2_size1 t.2.1) (finProdFinEquiv.symm (finProdFinEquiv.symm i).2).1,
    Fin.cast (x2_size1 t.2.2) (finProdFinEquiv.symm (finProdFinEquiv.symm i).2).2)

/-- Decode an a frame index into the reduced ambient. -/
def x2Dec2 (t : Fin 7 × Fin 7 × Fin 7)
    (i : Fin (certificatePhysicalFrameSystem2.size t.1 *
      (certificatePhysicalFrameSystem2.size t.2.1 * certificatePhysicalFrameSystem2.size t.2.2))) :
    Fin (x2Mult 2 (Fin.castSucc t.1)) × Fin (x2Mult 2 (Fin.castSucc t.2.1)) ×
      Fin (x2Mult 2 (Fin.castSucc t.2.2)) :=
  (Fin.cast (x2_size2 t.1) (finProdFinEquiv.symm i).1,
    Fin.cast (x2_size2 t.2.1) (finProdFinEquiv.symm (finProdFinEquiv.symm i).2).1,
    Fin.cast (x2_size2 t.2.2) (finProdFinEquiv.symm (finProdFinEquiv.symm i).2).2)

/-! ## Source Grams -/

/-- The m source Gram: units tensored with the source Q-form tensor as coefficients. -/
def x2SourceGram1 (D : X2Data) (wU : X2U 1 → Equiv.Perm (Fin 6) → ℂ) (Nm : X2Blocks 1) :
    Matrix SixRegisters SixRegisters ℂ :=
  certificateGlobalDiagramCombination {3, 4, 5}
    (fun v : X2U 1 × X2U 1 × X2U 1 => ((x2FmVec D 1 Nm v : ℚ) : ℂ))
    (fun v => wU v.1) (fun v => wU v.2.1) (fun v => wU v.2.2)

/-- The a source Gram. -/
def x2SourceGram2 (D : X2Data) (wU : X2U 2 → Equiv.Perm (Fin 6) → ℂ) (Na : X2Blocks 2) :
    Matrix SixRegisters SixRegisters ℂ :=
  certificateGlobalDiagramCombination {1, 2, 3, 4, 5}
    (fun v : X2U 2 × X2U 2 × X2U 2 => ((x2FmVec D 2 Na v : ℚ) : ℂ))
    (fun v => wU v.1) (fun v => wU v.2.1) (fun v => wU v.2.2)

theorem x2_sourceGram1_qform (D : X2Data) (wU : X2U 1 → Equiv.Perm (Fin 6) → ℂ)
    (hU : ∀ u t, certificateLocalDecomposition1Compression (wU u) t =
      x2UnitMatrix 1 certificatePhysicalFrameSystem1.size (fun t : Fin 8 => (t : ℕ)) u t)
    (Nm : X2Blocks 1) (t : Fin 8 × Fin 8 × Fin 8) :
    certificateThreeSiteFrameSystem1.metric t *
      ∑ v : X2U 1 × X2U 1 × X2U 1, ((x2FmVec D 1 Nm v : ℚ) : ℂ) •
        certificateTripleSourceAction certificatePhysicalFrameSystem1
          (certificateLocalDecomposition1Action (wU v.1))
          (certificateLocalDecomposition1Action (wU v.2.1))
          (certificateLocalDecomposition1Action (wU v.2.2)) t =
      (x2Complex (x2SourceBlock D 1 Nm ![t.1, t.2.1, t.2.2])).submatrix (x2Dec1 t) (x2Dec1 t) := by
  rw [Matrix.mul_sum]
  have hmet : ∀ v : X2U 1 × X2U 1 × X2U 1, certificateThreeSiteFrameSystem1.metric t *
      (((x2FmVec D 1 Nm v : ℚ) : ℂ) • certificateTripleSourceAction certificatePhysicalFrameSystem1
          (certificateLocalDecomposition1Action (wU v.1))
          (certificateLocalDecomposition1Action (wU v.2.1))
          (certificateLocalDecomposition1Action (wU v.2.2)) t) =
      ((x2FmVec D 1 Nm v : ℚ) : ℂ) • certificateTripleSourceAction certificatePhysicalFrameSystem1
          (x2UnitMatrix 1 certificatePhysicalFrameSystem1.size (fun t : Fin 8 => (t : ℕ)) v.1)
          (x2UnitMatrix 1 certificatePhysicalFrameSystem1.size (fun t : Fin 8 => (t : ℕ)) v.2.1)
          (x2UnitMatrix 1 certificatePhysicalFrameSystem1.size (fun t : Fin 8 => (t : ℕ)) v.2.2) t := by
    intro v
    rw [Matrix.mul_smul]
    congr 1
    unfold certificateThreeSiteFrameSystem1
    rw [x2_metric_tripleSourceAction]
    congr 1 <;> funext t' <;> rw [← hU] <;>
      exact certificateLocalDecomposition1metric_action _ t'
  simp only [hmet]
  ext i j
  rw [x2_tripleUnits_sum certificatePhysicalFrameSystem1 1 (fun t => t) x2_size1]
  rfl

theorem x2_sourceGram2_qform (D : X2Data) (wU : X2U 2 → Equiv.Perm (Fin 6) → ℂ)
    (hU : ∀ u t, certificateLocalDecomposition2Compression (wU u) t =
      x2UnitMatrix 2 certificatePhysicalFrameSystem2.size
        (fun t : Fin 7 => ((Fin.castSucc t : Fin 8) : ℕ)) u t)
    (Na : X2Blocks 2) (t : Fin 7 × Fin 7 × Fin 7) :
    certificateThreeSiteFrameSystem2.metric t *
      ∑ v : X2U 2 × X2U 2 × X2U 2, ((x2FmVec D 2 Na v : ℚ) : ℂ) •
        certificateTripleSourceAction certificatePhysicalFrameSystem2
          (certificateLocalDecomposition2Action (wU v.1))
          (certificateLocalDecomposition2Action (wU v.2.1))
          (certificateLocalDecomposition2Action (wU v.2.2)) t =
      (x2Complex (x2SourceBlock D 2 Na
        ![Fin.castSucc t.1, Fin.castSucc t.2.1, Fin.castSucc t.2.2])).submatrix
          (x2Dec2 t) (x2Dec2 t) := by
  rw [Matrix.mul_sum]
  have hmet : ∀ v : X2U 2 × X2U 2 × X2U 2, certificateThreeSiteFrameSystem2.metric t *
      (((x2FmVec D 2 Na v : ℚ) : ℂ) • certificateTripleSourceAction certificatePhysicalFrameSystem2
          (certificateLocalDecomposition2Action (wU v.1))
          (certificateLocalDecomposition2Action (wU v.2.1))
          (certificateLocalDecomposition2Action (wU v.2.2)) t) =
      ((x2FmVec D 2 Na v : ℚ) : ℂ) • certificateTripleSourceAction certificatePhysicalFrameSystem2
          (x2UnitMatrix 2 certificatePhysicalFrameSystem2.size
            (fun t : Fin 7 => ((Fin.castSucc t : Fin 8) : ℕ)) v.1)
          (x2UnitMatrix 2 certificatePhysicalFrameSystem2.size
            (fun t : Fin 7 => ((Fin.castSucc t : Fin 8) : ℕ)) v.2.1)
          (x2UnitMatrix 2 certificatePhysicalFrameSystem2.size
            (fun t : Fin 7 => ((Fin.castSucc t : Fin 8) : ℕ)) v.2.2) t := by
    intro v
    rw [Matrix.mul_smul]
    congr 1
    unfold certificateThreeSiteFrameSystem2
    rw [x2_metric_tripleSourceAction]
    congr 1 <;> funext t' <;> rw [← hU] <;>
      exact certificateLocalDecomposition2metric_action _ t'
  simp only [hmet]
  ext i j
  rw [x2_tripleUnits_sum certificatePhysicalFrameSystem2 2 Fin.castSucc x2_size2]
  rfl

theorem x2_sourceGram1_posSemidef (D : X2Data) (wU : X2U 1 → Equiv.Perm (Fin 6) → ℂ)
    (hU : ∀ u t, certificateLocalDecomposition1Compression (wU u) t =
      x2UnitMatrix 1 certificatePhysicalFrameSystem1.size (fun t : Fin 8 => (t : ℕ)) u t)
    (Nm : X2Blocks 1) (hNm : ∀ b, (x2Complex (Nm b)).PosSemidef) :
    (x2SourceGram1 D wU Nm).PosSemidef := by
  apply x2_global1_posSemidef
  intro t
  rw [x2_sourceGram1_qform D wU hU Nm t]
  exact (x2SourceBlock_posSemidef D 1 Nm hNm _).submatrix _

theorem x2_sourceGram2_posSemidef (D : X2Data) (wU : X2U 2 → Equiv.Perm (Fin 6) → ℂ)
    (hU : ∀ u t, certificateLocalDecomposition2Compression (wU u) t =
      x2UnitMatrix 2 certificatePhysicalFrameSystem2.size
        (fun t : Fin 7 => ((Fin.castSucc t : Fin 8) : ℕ)) u t)
    (Na : X2Blocks 2) (hNa : ∀ b, (x2Complex (Na b)).PosSemidef) :
    (x2SourceGram2 D wU Na).PosSemidef := by
  apply x2_global2_posSemidef
  intro t
  rw [x2_sourceGram2_qform D wU hU Na t]
  exact (x2SourceBlock_posSemidef D 2 Na hNa _).submatrix _

/-! ## The transferred Q-forms on h type triples -/

/-- The transferred tensor `(Q ⊗ Q ⊗ Q) F` read on an h type triple, in frame coordinates. -/
def x2TransferQForm (D : X2Data) (s : Fin 3) (N : X2Blocks s) (τ : Fin 7 × Fin 7 × Fin 7) :
    Matrix (Fin (certificatePhysicalFrameSystem0.size τ.1 *
        (certificatePhysicalFrameSystem0.size τ.2.1 * certificatePhysicalFrameSystem0.size τ.2.2)))
      (Fin (certificatePhysicalFrameSystem0.size τ.1 *
        (certificatePhysicalFrameSystem0.size τ.2.1 * certificatePhysicalFrameSystem0.size τ.2.2))) ℂ :=
  Matrix.of fun i j => ((((x2Qu D s ⊗ₖ (x2Qu D s ⊗ₖ x2Qu D s)) *ᵥ x2FmVec D s N)
    (x2UnitAt 0 certificatePhysicalFrameSystem0.size Fin.castSucc x2_size0 τ.1
        (finProdFinEquiv.symm i).1 (finProdFinEquiv.symm j).1,
      x2UnitAt 0 certificatePhysicalFrameSystem0.size Fin.castSucc x2_size0 τ.2.1
        (finProdFinEquiv.symm (finProdFinEquiv.symm i).2).1
        (finProdFinEquiv.symm (finProdFinEquiv.symm j).2).1,
      x2UnitAt 0 certificatePhysicalFrameSystem0.size Fin.castSucc x2_size0 τ.2.2
        (finProdFinEquiv.symm (finProdFinEquiv.symm i).2).2
        (finProdFinEquiv.symm (finProdFinEquiv.symm j).2).2) : ℚ) : ℂ)

/-- One dictionary entry: the h compression of a unit weight is the column of `Q`. -/
theorem x2_dict_entry (D : X2Data) (s : Fin 3) (wU : X2U s → Equiv.Perm (Fin 6) → ℂ)
    (hD : ∀ u t, certificateLocalDecomposition0Compression (wU u) t =
      ∑ u' : X2U 0, ((x2Qu D s u' u : ℚ) : ℂ) • x2UnitMatrix 0 certificatePhysicalFrameSystem0.size
        (fun t : Fin 7 => ((Fin.castSucc t : Fin 8) : ℕ)) u' t)
    (u : X2U s) (t : Fin 7) (a b : Fin (certificatePhysicalFrameSystem0.size t)) :
    (certificatePhysicalFrameSystem0.metric t * certificateLocalDecomposition0Action (wU u) t) a b =
      ((x2Qu D s (x2UnitAt 0 certificatePhysicalFrameSystem0.size Fin.castSucc x2_size0 t a b) u
        : ℚ) : ℂ) := by
  have hm : certificatePhysicalFrameSystem0.metric t * certificateLocalDecomposition0Action (wU u) t =
      certificateLocalDecomposition0Compression (wU u) t :=
    certificateLocalDecomposition0metric_action _ t
  rw [hm, hD, Matrix.sum_apply]
  simp only [Matrix.smul_apply, smul_eq_mul,
    x2UnitMatrix_apply_eq 0 certificatePhysicalFrameSystem0.size Fin.castSucc x2_size0,
    mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true]

theorem x2_transfer_qform (D : X2Data) (s : Fin 3) (wU : X2U s → Equiv.Perm (Fin 6) → ℂ)
    (hD : ∀ u t, certificateLocalDecomposition0Compression (wU u) t =
      ∑ u' : X2U 0, ((x2Qu D s u' u : ℚ) : ℂ) • x2UnitMatrix 0 certificatePhysicalFrameSystem0.size
        (fun t : Fin 7 => ((Fin.castSucc t : Fin 8) : ℕ)) u' t)
    (N : X2Blocks s) (τ : Fin 7 × Fin 7 × Fin 7) :
    certificateThreeSiteFrameSystem0.metric τ *
      ∑ v : X2U s × X2U s × X2U s, ((x2FmVec D s N v : ℚ) : ℂ) •
        certificateTripleSourceAction certificatePhysicalFrameSystem0
          (certificateLocalDecomposition0Action (wU v.1))
          (certificateLocalDecomposition0Action (wU v.2.1))
          (certificateLocalDecomposition0Action (wU v.2.2)) τ =
      x2TransferQForm D s N τ := by
  rw [Matrix.mul_sum]
  simp only [Matrix.mul_smul]
  unfold certificateThreeSiteFrameSystem0
  simp only [x2_metric_tripleSourceAction certificatePhysicalFrameSystem0]
  ext i j
  rw [Matrix.sum_apply]
  simp only [Matrix.smul_apply, smul_eq_mul, x2_tripleSourceAction_apply,
    x2_dict_entry D s wU hD]
  unfold x2TransferQForm
  rw [Matrix.of_apply, Matrix.mulVec, dotProduct]
  push_cast
  apply Finset.sum_congr rfl
  intro v _
  simp only [Matrix.kroneckerMap_apply]
  push_cast
  ring

/-! ## The endpoint inequality from the h-side forms -/

/-- The endpoint target's Q-form on an h type triple. -/
def x2TargetQForm (τ : Fin 7 × Fin 7 × Fin 7) :
    Matrix (Fin (certificatePhysicalFrameSystem0.size τ.1 *
        (certificatePhysicalFrameSystem0.size τ.2.1 * certificatePhysicalFrameSystem0.size τ.2.2)))
      (Fin (certificatePhysicalFrameSystem0.size τ.1 *
        (certificatePhysicalFrameSystem0.size τ.2.1 * certificatePhysicalFrameSystem0.size τ.2.2))) ℂ :=
  certificateThreeSiteFrameSystem0.metric τ *
    certificateTripleSourceAction certificatePhysicalFrameSystem0
      (certificateLocalDecomposition0Action certificateEndpointDiagramWeight)
      (certificateLocalDecomposition0Action certificateEndpointDiagramWeight)
      (certificateLocalDecomposition0Action certificateEndpointDiagramWeight) τ

/-- MAIN REDUCTION: T2.1a from the per-site unit and dictionary identities, positive source
blocks, and positivity of the compressed h-side forms `πᴴ (T - Q₁ - Q₂) π` on every h type
triple. -/
theorem x2_qutritEndpointInequality_of_hside (D : X2Data)
    (wU1 : X2U 1 → Equiv.Perm (Fin 6) → ℂ) (wU2 : X2U 2 → Equiv.Perm (Fin 6) → ℂ)
    (hU1 : ∀ u t, certificateLocalDecomposition1Compression (wU1 u) t =
      x2UnitMatrix 1 certificatePhysicalFrameSystem1.size (fun t : Fin 8 => (t : ℕ)) u t)
    (hU2 : ∀ u t, certificateLocalDecomposition2Compression (wU2 u) t =
      x2UnitMatrix 2 certificatePhysicalFrameSystem2.size
        (fun t : Fin 7 => ((Fin.castSucc t : Fin 8) : ℕ)) u t)
    (hD1 : ∀ u t, certificateLocalDecomposition0Compression (wU1 u) t =
      ∑ u' : X2U 0, ((x2Qu D 1 u' u : ℚ) : ℂ) • x2UnitMatrix 0 certificatePhysicalFrameSystem0.size
        (fun t : Fin 7 => ((Fin.castSucc t : Fin 8) : ℕ)) u' t)
    (hD2 : ∀ u t, certificateLocalDecomposition0Compression (wU2 u) t =
      ∑ u' : X2U 0, ((x2Qu D 2 u' u : ℚ) : ℂ) • x2UnitMatrix 0 certificatePhysicalFrameSystem0.size
        (fun t : Fin 7 => ((Fin.castSucc t : Fin 8) : ℕ)) u' t)
    (Nm : X2Blocks 1) (Na : X2Blocks 2)
    (hNm : ∀ b, (x2Complex (Nm b)).PosSemidef) (hNa : ∀ b, (x2Complex (Na b)).PosSemidef)
    (hres : ∀ τ : Fin 7 × Fin 7 × Fin 7, ((certificateCarrierJointAction0 τ)ᴴ *
      (x2TargetQForm τ - x2TransferQForm D 1 Nm τ - x2TransferQForm D 2 Na τ) *
        certificateCarrierJointAction0 τ).PosSemidef) :
    QutritEndpointInequality := by
  refine x2_qutritEndpointInequality_of_actions certificateThreeSiteFrameSystem0.size
    certificateThreeSiteFrameSystem0.type certificateThreeSiteFrameSystem0.pivot
    certificateThreeSiteFrameSystem0.basis certificateThreeSiteFrameSystem0.metric
    certificateThreeSiteFrameSystem0.scalar certificateThreeSiteFrameSystem0.basis_bijective
    certificateThreeSiteFrameSystem0.metric_posDef certificateThreeSiteFrameSystem0.gram
    certificateThreeSiteFrameSystem0.scalar_off_type
    (x2SourceGram1 D wU1 Nm) (x2SourceGram2 D wU2 Na)
    (x2_sourceGram1_posSemidef D wU1 hU1 Nm hNm) (x2_sourceGram2_posSemidef D wU2 hU2 Na hNa)
    certificateCarrierJointAction0
    (fun τ => certificateTripleSourceAction certificatePhysicalFrameSystem0
      (certificateLocalDecomposition0Action certificateEndpointDiagramWeight)
      (certificateLocalDecomposition0Action certificateEndpointDiagramWeight)
      (certificateLocalDecomposition0Action certificateEndpointDiagramWeight) τ)
    (fun τ => ∑ v : X2U 1 × X2U 1 × X2U 1, ((x2FmVec D 1 Nm v : ℚ) : ℂ) •
        certificateTripleSourceAction certificatePhysicalFrameSystem0
          (certificateLocalDecomposition0Action (wU1 v.1))
          (certificateLocalDecomposition0Action (wU1 v.2.1))
          (certificateLocalDecomposition0Action (wU1 v.2.2)) τ)
    (fun τ => ∑ v : X2U 2 × X2U 2 × X2U 2, ((x2FmVec D 2 Na v : ℚ) : ℂ) •
        certificateTripleSourceAction certificatePhysicalFrameSystem0
          (certificateLocalDecomposition0Action (wU2 v.1))
          (certificateLocalDecomposition0Action (wU2 v.2.1))
          (certificateLocalDecomposition0Action (wU2 v.2.2)) τ)
    certificateCarrierJointAction0_physical certificateSixRegisterOperator_source_action
    (x2_transfer1_acts _ _ _ _) (x2_transfer2_acts _ _ _ _) ?_
  intro τ
  try dsimp only
  have hsa := certificateCarrierJointAction0_gram_selfadjoint τ
  have hT : certificateThreeSiteFrameSystem0.metric τ *
      certificateTripleSourceAction certificatePhysicalFrameSystem0
        (certificateLocalDecomposition0Action certificateEndpointDiagramWeight)
        (certificateLocalDecomposition0Action certificateEndpointDiagramWeight)
        (certificateLocalDecomposition0Action certificateEndpointDiagramWeight) τ =
      x2TargetQForm τ := rfl
  rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, hsa, Matrix.mul_assoc _ _ (_ - _ - _),
    Matrix.mul_sub (certificateThreeSiteFrameSystem0.metric τ),
    Matrix.mul_sub (certificateThreeSiteFrameSystem0.metric τ), hT,
    x2_transfer_qform D 1 wU1 hD1 Nm τ, x2_transfer_qform D 2 wU2 hD2 Na τ]
  exact hres τ

end ThreeCopyQutritWerner

end
