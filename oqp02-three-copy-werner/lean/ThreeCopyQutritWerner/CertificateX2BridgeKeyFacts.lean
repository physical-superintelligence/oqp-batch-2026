module

public import ThreeCopyQutritWerner.CertificateX2BridgeHBlock
public import ThreeCopyQutritWerner.CertificateX2BridgeImages

@[expose] public section


/-!
# The finite facts the bridge consumes, as statements

Two structures collect every finite fact that the operator-level bridge takes as hypothesis.

* `X2SiteFacts D wU1 wU2`: per-site unit and dictionary identities of the unit
  weights, and the endpoint target's per-site compression. With them,
  `x2_qutritEndpointInequality_of_siteFacts` proves T2.1a from positive source blocks and positive
  h-side forms on every h type triple.
* `X2KeyFrameFacts D`: for every h key `b`, in the frame coordinates
  of its type triple `τ_b = x2KeyTau b` with `J = x2ImageFrame D b` (a frame index is the
  row-major ambient index): the carrier fixes `J`, the kind projector fixes `J`, the trace count,
  the metric determinant, the first-two-slot swap fixes standard images, the swap has trace zero
  on the carrier's standard component, and parts without a key carry nothing.

These are the frame-coordinate forms of `X2ImageFacts` (CertificateX2BridgeImages; the certificate's coordinates),
with the infrastructure's carrier action `certificateCarrierJointAction0` and metric
`certificateThreeSiteFrameSystem0.metric`. Slot permutations act by `(P_p v)(x) = v(x ∘ p)`
(entry `(i, j)` is `1` iff the coordinates of `j` are those of `i` composed with `x2Perm3 p`).
-/

noncomputable section

open scoped BigOperators Matrix ComplexOrder

namespace ThreeCopyQutritWerner

/-- Natural coordinates of a frame index of an h type triple. -/
def x2FrameCoords (τ : Fin 7 × Fin 7 × Fin 7)
    (i : Fin (certificatePhysicalFrameSystem0.size τ.1 *
      (certificatePhysicalFrameSystem0.size τ.2.1 * certificatePhysicalFrameSystem0.size τ.2.2))) :
    Fin 3 → ℕ :=
  ![((finProdFinEquiv.symm i).1 : ℕ), ((finProdFinEquiv.symm (finProdFinEquiv.symm i).2).1 : ℕ),
    ((finProdFinEquiv.symm (finProdFinEquiv.symm i).2).2 : ℕ)]

/-- Slot permutation in frame coordinates (frame version of `x2SlotPerm`). -/
def x2SlotPermFrame (τ : Fin 7 × Fin 7 × Fin 7) (p : Fin 6) :
    Matrix (Fin (certificatePhysicalFrameSystem0.size τ.1 *
        (certificatePhysicalFrameSystem0.size τ.2.1 * certificatePhysicalFrameSystem0.size τ.2.2)))
      (Fin (certificatePhysicalFrameSystem0.size τ.1 *
        (certificatePhysicalFrameSystem0.size τ.2.1 * certificatePhysicalFrameSystem0.size τ.2.2))) ℂ :=
  Matrix.of fun i j => if x2FrameCoords τ j = x2FrameCoords τ i ∘ x2Perm3 p then 1 else 0

/-- Kind projector in frame coordinates (frame version of `x2KindProj`): S3 isotypic projectors
for three equal types (kind 0 trivial, 1 sign, 2 standard), the symmetric (0) / alternating (1)
projector of two equal slots, the identity for distinct types. -/
def x2KindProjFrame (τ : Fin 7 × Fin 7 × Fin 7) (kind : ℕ) :
    Matrix (Fin (certificatePhysicalFrameSystem0.size τ.1 *
        (certificatePhysicalFrameSystem0.size τ.2.1 * certificatePhysicalFrameSystem0.size τ.2.2)))
      (Fin (certificatePhysicalFrameSystem0.size τ.1 *
        (certificatePhysicalFrameSystem0.size τ.2.1 * certificatePhysicalFrameSystem0.size τ.2.2))) ℂ :=
  let avg := (1 / 6 : ℂ) • ∑ p, x2SlotPermFrame τ p
  let alt := (1 / 6 : ℂ) • ∑ p, ((x2Perm3Sign p : ℚ) : ℂ) • x2SlotPermFrame τ p
  if τ.1 = τ.2.1 ∧ τ.2.1 = τ.2.2 then
    (if kind = 0 then avg else if kind = 1 then alt else 1 - avg - alt)
  else if τ.1 = τ.2.1 then
    (1 / 2 : ℂ) • (1 + (if kind = 0 then (1 : ℂ) else -1) • x2SlotPermFrame τ x2Swap01Idx)
  else if τ.2.1 = τ.2.2 then
    (1 / 2 : ℂ) • (1 + (if kind = 0 then (1 : ℂ) else -1) • x2SlotPermFrame τ x2Swap12Idx)
  else 1

/-- Number of stabilizer kinds of a sorted type triple. -/
def x2NumKinds (τ : Fin 7 × Fin 7 × Fin 7) : ℕ :=
  if τ.1 = τ.2.1 ∧ τ.2.1 = τ.2.2 then 3 else if τ.1 = τ.2.1 ∨ τ.2.1 = τ.2.2 then 2 else 1

/-- per-site unit and dictionary identities of the unit weights, and the endpoint target. -/
structure X2SiteFacts (D : X2Data) (wU1 : X2U 1 → Equiv.Perm (Fin 6) → ℂ)
    (wU2 : X2U 2 → Equiv.Perm (Fin 6) → ℂ) : Prop where
  unit1 : ∀ u t, certificateLocalDecomposition1Compression (wU1 u) t =
    x2UnitMatrix 1 certificatePhysicalFrameSystem1.size (fun t : Fin 8 => (t : ℕ)) u t
  unit2 : ∀ u t, certificateLocalDecomposition2Compression (wU2 u) t =
    x2UnitMatrix 2 certificatePhysicalFrameSystem2.size
      (fun t : Fin 7 => ((Fin.castSucc t : Fin 8) : ℕ)) u t
  dict1 : ∀ u t, certificateLocalDecomposition0Compression (wU1 u) t =
    ∑ u' : X2U 0, ((x2Qu D 1 u' u : ℚ) : ℂ) • x2UnitMatrix 0 certificatePhysicalFrameSystem0.size
      (fun t : Fin 7 => ((Fin.castSucc t : Fin 8) : ℕ)) u' t
  dict2 : ∀ u t, certificateLocalDecomposition0Compression (wU2 u) t =
    ∑ u' : X2U 0, ((x2Qu D 2 u' u : ℚ) : ℂ) • x2UnitMatrix 0 certificatePhysicalFrameSystem0.size
      (fun t : Fin 7 => ((Fin.castSucc t : Fin 8) : ℕ)) u' t
  target : ∀ t : Fin 7, certificateLocalDecomposition0Compression certificateEndpointDiagramWeight t =
    Matrix.of fun i j => ((x2LocalTarget (Fin.castSucc t) (Fin.cast (x2_size0 t) i)
      (Fin.cast (x2_size0 t) j) : ℚ) : ℂ)

/-- the image facts of every h key in frame coordinates, and empty parts. -/
structure X2KeyFrameFacts (D : X2Data) : Prop where
  carrier_fix : ∀ b : x2Key 0,
    certificateCarrierJointAction0 (x2KeyTau b) * x2ImageFrame D b = x2ImageFrame D b
  kind_fix : ∀ b : x2Key 0,
    x2KindProjFrame (x2KeyTau b) (x2KeyKind 0 b) * x2ImageFrame D b = x2ImageFrame D b
  trace_count : ∀ b : x2Key 0,
    (certificateCarrierJointAction0 (x2KeyTau b) * x2KindProjFrame (x2KeyTau b) (x2KeyKind 0 b)).trace =
      ((x2KeyDegree 0 b * x2KeySize 0 b : ℕ) : ℂ)
  metric_det : ∀ b : x2Key 0,
    ((x2ImageFrame D b)ᴴ * certificateThreeSiteFrameSystem0.metric (x2KeyTau b) *
      x2ImageFrame D b).det ≠ 0
  standard_swap : ∀ b : x2Key 0, x2KeyDegree 0 b = 2 →
    x2SlotPermFrame (x2KeyTau b) x2Swap01Idx * x2ImageFrame D b = x2ImageFrame D b
  standard_split : ∀ b : x2Key 0, x2KeyDegree 0 b = 2 →
    (certificateCarrierJointAction0 (x2KeyTau b) * x2KindProjFrame (x2KeyTau b) 2 *
      x2SlotPermFrame (x2KeyTau b) x2Swap01Idx).trace = 0
  empty_kinds : ∀ τ : Fin 7 × Fin 7 × Fin 7, τ.1 ≤ τ.2.1 → τ.2.1 ≤ τ.2.2 →
    ∀ k : ℕ, k < x2NumKinds τ → (∀ b : x2Key 0, x2KeyTau b = τ → x2KeyKind 0 b ≠ k) →
      (certificateCarrierJointAction0 τ * x2KindProjFrame τ k).trace = 0

/-- T2.1a from the site facts, positive source blocks and positive h-side forms. -/
theorem x2_qutritEndpointInequality_of_siteFacts (D : X2Data)
    (wU1 : X2U 1 → Equiv.Perm (Fin 6) → ℂ) (wU2 : X2U 2 → Equiv.Perm (Fin 6) → ℂ)
    (hS : X2SiteFacts D wU1 wU2) (Nm : X2Blocks 1) (Na : X2Blocks 2)
    (hNm : ∀ b, (x2Complex (Nm b)).PosSemidef) (hNa : ∀ b, (x2Complex (Na b)).PosSemidef)
    (hres : ∀ τ : Fin 7 × Fin 7 × Fin 7, ((certificateCarrierJointAction0 τ)ᴴ *
      (x2TargetQForm τ - x2TransferQForm D 1 Nm τ - x2TransferQForm D 2 Na τ) *
        certificateCarrierJointAction0 τ).PosSemidef) :
    QutritEndpointInequality :=
  x2_qutritEndpointInequality_of_hside D wU1 wU2 hS.unit1 hS.unit2 hS.dict1 hS.dict2 Nm Na
    hNm hNa hres

end ThreeCopyQutritWerner

end
