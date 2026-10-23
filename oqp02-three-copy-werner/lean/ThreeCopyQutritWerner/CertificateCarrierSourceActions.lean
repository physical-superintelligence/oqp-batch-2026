module

public import ThreeCopyQutritWerner.CertificateCarrierActionChecks
public import ThreeCopyQutritWerner.CertificateGlobalDiagramActions

@[expose] public section


/-!
# Actual ordinary carrier source actions on the complete local bases

Each coefficient matrix is the original integer source action, with
its existing physical binding. Signed-generator commutation transports that
same action through every selected descendant. No saved action premise remains.
-/

noncomputable section

open scoped BigOperators Matrix Kronecker

namespace ThreeCopyQutritWerner

/-- Exact scalar extension of the actual integer ordinary-permutation action. -/
theorem certificateOrdinarySourceAction_complex {m : Type*} [Fintype m]
    (U : Matrix CertificateLocalWord m ℤ) (A : Matrix m m ℤ)
    (σ : Equiv.Perm (Fin 6))
    (h : certificateLocalDiagram (R := ℤ) ∅ σ * U = U * A) :
    certificateLocalDiagram (R := ℂ) ∅ σ * U.map (Int.cast : ℤ → ℂ) =
      U.map (Int.cast : ℤ → ℂ) * A.map (Int.cast : ℤ → ℂ) := by
  have hc := congrArg (fun M : Matrix CertificateLocalWord m ℤ =>
    M.map (Int.castRingHom ℂ)) h
  simp only [Matrix.map_mul, certificateLocalDiagram_map] at hc
  simpa only [Int.coe_castRingHom] using hc

/-- A partition-preserving ordinary permutation commutes with both actual lowering matrices. -/
theorem certificateOrdinaryRegister_commutes_lowering
    (ket : Finset (Fin 6)) (σ : Equiv.Perm (Fin 6))
    (hσ : ∀ s, σ s ∈ ket ↔ s ∈ ket) (g : Fin 2) :
    certificateLocalDiagram (R := ℂ) ∅ σ *
        (certificateLocalLowering ket g).map (Int.cast : ℤ → ℂ) =
      (certificateLocalLowering ket g).map (Int.cast : ℤ → ℂ) *
        certificateLocalDiagram ∅ σ := by
  by_cases hg : g = 0
  · simpa only [certificateLocalLowering, hg, if_true] using
      certificateOrdinaryRegister_commutes_generator_complex ket σ hσ 1 0
  · simpa only [certificateLocalLowering, hg, if_false] using
      certificateOrdinaryRegister_commutes_generator_complex ket σ hσ 2 1

/-- Original source coefficient actions for all local types in sector 0. -/
def certificateCarrierSourceAction0 (p : Fin 120) :
    (t : Fin 7) → Matrix (Fin (certificateDescendantFrames2SourceSize t))
      (Fin (certificateDescendantFrames2SourceSize t)) ℂ := by
  exact
    Fin.cases ((certificateCarrierAction0_0 p).map (Int.cast : ℤ → ℂ)) <|
    Fin.cases ((certificateCarrierAction0_1 p).map (Int.cast : ℤ → ℂ)) <|
    Fin.cases ((certificateCarrierAction0_2 p).map (Int.cast : ℤ → ℂ)) <|
    Fin.cases ((certificateCarrierAction0_3 p).map (Int.cast : ℤ → ℂ)) <|
    Fin.cases ((certificateCarrierAction0_4 p).map (Int.cast : ℤ → ℂ)) <|
    Fin.cases ((certificateCarrierAction0_5 p).map (Int.cast : ℤ → ℂ)) <|
    Fin.cases ((certificateCarrierAction0_6 p).map (Int.cast : ℤ → ℂ)) <|
    Fin.rec0

/-- Every original highest frame has the literal checked coefficient action. -/
theorem certificateCarrierSourceAction0_physical (p : Fin 120) (t : Fin 7) :
    certificateLocalDiagram (R := ℂ) ∅ (certificateCarrierPerm0 p) *
        (certificateDescendantFrames0Source t).map (Int.cast : ℤ → ℂ) =
      (certificateDescendantFrames0Source t).map (Int.cast : ℤ → ℂ) *
        certificateCarrierSourceAction0 p t := by
  fin_cases t
  · exact certificateOrdinarySourceAction_complex _ _ _ (certificateCarrierAction0_0_physical p)
  · exact certificateOrdinarySourceAction_complex _ _ _ (certificateCarrierAction0_1_physical p)
  · exact certificateOrdinarySourceAction_complex _ _ _ (certificateCarrierAction0_2_physical p)
  · exact certificateOrdinarySourceAction_complex _ _ _ (certificateCarrierAction0_3_physical p)
  · exact certificateOrdinarySourceAction_complex _ _ _ (certificateCarrierAction0_4_physical p)
  · exact certificateOrdinarySourceAction_complex _ _ _ (certificateCarrierAction0_5_physical p)
  · exact certificateOrdinarySourceAction_complex _ _ _ (certificateCarrierAction0_6_physical p)

/-- The complete physical basis carries those same original source actions. -/
theorem certificateCarrierSourceAction0_intertwines (p : Fin 120) :
    certificateLocalDiagram (R := ℂ) ∅ (certificateCarrierPerm0 p) *
        certificatePhysicalFrameSystem0.basis = certificatePhysicalFrameSystem0.basis *
      Matrix.blockDiagonal'
        (m' := fun f => Fin (certificatePhysicalFrameSystem0.size (certificatePhysicalFrameSystem0.type f)))
        (n' := fun f => Fin (certificatePhysicalFrameSystem0.size (certificatePhysicalFrameSystem0.type f)))
        (fun f => certificateCarrierSourceAction0 p (certificatePhysicalFrameSystem0.type f)) :=
  certificateDescendantFrames0Matrix_intertwines _ _
    (certificateOrdinaryRegister_commutes_lowering {5} _ (certificateCarrierPerm0_preserves p))
    (certificateCarrierSourceAction0_physical p)

/-- All three sites act on the literal row-major tensor of original source coefficients. -/
theorem certificateCarrierSourceAction0_triple (p : Fin 120) :
    (certificateLocalDiagram (R := ℂ) ∅ (certificateCarrierPerm0 p) ⊗ₖ
      (certificateLocalDiagram (R := ℂ) ∅ (certificateCarrierPerm0 p) ⊗ₖ
        certificateLocalDiagram (R := ℂ) ∅ (certificateCarrierPerm0 p))) *
      certificateThreeSiteFrameSystem0.basis = certificateThreeSiteFrameSystem0.basis *
        Matrix.blockDiagonal' (fun f => certificateTripleSourceAction certificatePhysicalFrameSystem0
          (certificateCarrierSourceAction0 p) (certificateCarrierSourceAction0 p)
          (certificateCarrierSourceAction0 p) (certificateThreeSiteFrameSystem0.type f)) :=
  certificatePhysicalFrameTriple_intertwines certificatePhysicalFrameSystem0 _ _ _ _ _ _
    (certificateCarrierSourceAction0_intertwines p)
    (certificateCarrierSourceAction0_intertwines p)
    (certificateCarrierSourceAction0_intertwines p)

/-- Original source coefficient actions for all local types in sector 1. -/
def certificateCarrierSourceAction1 (p : Fin 12) :
    (t : Fin 8) → Matrix (Fin (certificateDescendantFrames1SourceSize t))
      (Fin (certificateDescendantFrames1SourceSize t)) ℂ := by
  exact
    Fin.cases ((certificateCarrierAction1_0 p).map (Int.cast : ℤ → ℂ)) <|
    Fin.cases ((certificateCarrierAction1_1 p).map (Int.cast : ℤ → ℂ)) <|
    Fin.cases ((certificateCarrierAction1_2 p).map (Int.cast : ℤ → ℂ)) <|
    Fin.cases ((certificateCarrierAction1_3 p).map (Int.cast : ℤ → ℂ)) <|
    Fin.cases ((certificateCarrierAction1_4 p).map (Int.cast : ℤ → ℂ)) <|
    Fin.cases ((certificateCarrierAction1_5 p).map (Int.cast : ℤ → ℂ)) <|
    Fin.cases ((certificateCarrierAction1_6 p).map (Int.cast : ℤ → ℂ)) <|
    Fin.cases ((certificateCarrierAction1_7 p).map (Int.cast : ℤ → ℂ)) <|
    Fin.rec0

/-- Every original highest frame has the literal checked coefficient action. -/
theorem certificateCarrierSourceAction1_physical (p : Fin 12) (t : Fin 8) :
    certificateLocalDiagram (R := ℂ) ∅ (certificateCarrierPerm1 p) *
        (certificateDescendantFrames1Source t).map (Int.cast : ℤ → ℂ) =
      (certificateDescendantFrames1Source t).map (Int.cast : ℤ → ℂ) *
        certificateCarrierSourceAction1 p t := by
  fin_cases t
  · exact certificateOrdinarySourceAction_complex _ _ _ (certificateCarrierAction1_0_physical p)
  · exact certificateOrdinarySourceAction_complex _ _ _ (certificateCarrierAction1_1_physical p)
  · exact certificateOrdinarySourceAction_complex _ _ _ (certificateCarrierAction1_2_physical p)
  · exact certificateOrdinarySourceAction_complex _ _ _ (certificateCarrierAction1_3_physical p)
  · exact certificateOrdinarySourceAction_complex _ _ _ (certificateCarrierAction1_4_physical p)
  · exact certificateOrdinarySourceAction_complex _ _ _ (certificateCarrierAction1_5_physical p)
  · exact certificateOrdinarySourceAction_complex _ _ _ (certificateCarrierAction1_6_physical p)
  · exact certificateOrdinarySourceAction_complex _ _ _ (certificateCarrierAction1_7_physical p)

/-- The complete physical basis carries those same original source actions. -/
theorem certificateCarrierSourceAction1_intertwines (p : Fin 12) :
    certificateLocalDiagram (R := ℂ) ∅ (certificateCarrierPerm1 p) *
        certificatePhysicalFrameSystem1.basis = certificatePhysicalFrameSystem1.basis *
      Matrix.blockDiagonal'
        (m' := fun f => Fin (certificatePhysicalFrameSystem1.size (certificatePhysicalFrameSystem1.type f)))
        (n' := fun f => Fin (certificatePhysicalFrameSystem1.size (certificatePhysicalFrameSystem1.type f)))
        (fun f => certificateCarrierSourceAction1 p (certificatePhysicalFrameSystem1.type f)) :=
  certificateDescendantFrames1Matrix_intertwines _ _
    (certificateOrdinaryRegister_commutes_lowering {0, 1, 2} _ (certificateCarrierPerm1_preserves p))
    (certificateCarrierSourceAction1_physical p)

/-- All three sites act on the literal row-major tensor of original source coefficients. -/
theorem certificateCarrierSourceAction1_triple (p : Fin 12) :
    (certificateLocalDiagram (R := ℂ) ∅ (certificateCarrierPerm1 p) ⊗ₖ
      (certificateLocalDiagram (R := ℂ) ∅ (certificateCarrierPerm1 p) ⊗ₖ
        certificateLocalDiagram (R := ℂ) ∅ (certificateCarrierPerm1 p))) *
      certificateThreeSiteFrameSystem1.basis = certificateThreeSiteFrameSystem1.basis *
        Matrix.blockDiagonal' (fun f => certificateTripleSourceAction certificatePhysicalFrameSystem1
          (certificateCarrierSourceAction1 p) (certificateCarrierSourceAction1 p)
          (certificateCarrierSourceAction1 p) (certificateThreeSiteFrameSystem1.type f)) :=
  certificatePhysicalFrameTriple_intertwines certificatePhysicalFrameSystem1 _ _ _ _ _ _
    (certificateCarrierSourceAction1_intertwines p)
    (certificateCarrierSourceAction1_intertwines p)
    (certificateCarrierSourceAction1_intertwines p)

/-- Original source coefficient actions for all local types in sector 2. -/
def certificateCarrierSourceAction2 (p : Fin 24) :
    (t : Fin 7) → Matrix (Fin (certificateDescendantFrames2SourceSize t))
      (Fin (certificateDescendantFrames2SourceSize t)) ℂ := by
  exact
    Fin.cases ((certificateCarrierAction2_0 p).map (Int.cast : ℤ → ℂ)) <|
    Fin.cases ((certificateCarrierAction2_1 p).map (Int.cast : ℤ → ℂ)) <|
    Fin.cases ((certificateCarrierAction2_2 p).map (Int.cast : ℤ → ℂ)) <|
    Fin.cases ((certificateCarrierAction2_3 p).map (Int.cast : ℤ → ℂ)) <|
    Fin.cases ((certificateCarrierAction2_4 p).map (Int.cast : ℤ → ℂ)) <|
    Fin.cases ((certificateCarrierAction2_5 p).map (Int.cast : ℤ → ℂ)) <|
    Fin.cases ((certificateCarrierAction2_6 p).map (Int.cast : ℤ → ℂ)) <|
    Fin.rec0

/-- Every original highest frame has the literal checked coefficient action. -/
theorem certificateCarrierSourceAction2_physical (p : Fin 24) (t : Fin 7) :
    certificateLocalDiagram (R := ℂ) ∅ (certificateCarrierPerm2 p) *
        (certificateDescendantFrames2Source t).map (Int.cast : ℤ → ℂ) =
      (certificateDescendantFrames2Source t).map (Int.cast : ℤ → ℂ) *
        certificateCarrierSourceAction2 p t := by
  fin_cases t
  · exact certificateOrdinarySourceAction_complex _ _ _ (certificateCarrierAction2_0_physical p)
  · exact certificateOrdinarySourceAction_complex _ _ _ (certificateCarrierAction2_1_physical p)
  · exact certificateOrdinarySourceAction_complex _ _ _ (certificateCarrierAction2_2_physical p)
  · exact certificateOrdinarySourceAction_complex _ _ _ (certificateCarrierAction2_3_physical p)
  · exact certificateOrdinarySourceAction_complex _ _ _ (certificateCarrierAction2_4_physical p)
  · exact certificateOrdinarySourceAction_complex _ _ _ (certificateCarrierAction2_5_physical p)
  · exact certificateOrdinarySourceAction_complex _ _ _ (certificateCarrierAction2_6_physical p)

/-- The complete physical basis carries those same original source actions. -/
theorem certificateCarrierSourceAction2_intertwines (p : Fin 24) :
    certificateLocalDiagram (R := ℂ) ∅ (certificateCarrierPerm2 p) *
        certificatePhysicalFrameSystem2.basis = certificatePhysicalFrameSystem2.basis *
      Matrix.blockDiagonal'
        (m' := fun f => Fin (certificatePhysicalFrameSystem2.size (certificatePhysicalFrameSystem2.type f)))
        (n' := fun f => Fin (certificatePhysicalFrameSystem2.size (certificatePhysicalFrameSystem2.type f)))
        (fun f => certificateCarrierSourceAction2 p (certificatePhysicalFrameSystem2.type f)) :=
  certificateDescendantFrames2Matrix_intertwines _ _
    (certificateOrdinaryRegister_commutes_lowering {0} _ (certificateCarrierPerm2_preserves p))
    (certificateCarrierSourceAction2_physical p)

/-- All three sites act on the literal row-major tensor of original source coefficients. -/
theorem certificateCarrierSourceAction2_triple (p : Fin 24) :
    (certificateLocalDiagram (R := ℂ) ∅ (certificateCarrierPerm2 p) ⊗ₖ
      (certificateLocalDiagram (R := ℂ) ∅ (certificateCarrierPerm2 p) ⊗ₖ
        certificateLocalDiagram (R := ℂ) ∅ (certificateCarrierPerm2 p))) *
      certificateThreeSiteFrameSystem2.basis = certificateThreeSiteFrameSystem2.basis *
        Matrix.blockDiagonal' (fun f => certificateTripleSourceAction certificatePhysicalFrameSystem2
          (certificateCarrierSourceAction2 p) (certificateCarrierSourceAction2 p)
          (certificateCarrierSourceAction2 p) (certificateThreeSiteFrameSystem2.type f)) :=
  certificatePhysicalFrameTriple_intertwines certificatePhysicalFrameSystem2 _ _ _ _ _ _
    (certificateCarrierSourceAction2_intertwines p)
    (certificateCarrierSourceAction2_intertwines p)
    (certificateCarrierSourceAction2_intertwines p)

end ThreeCopyQutritWerner
