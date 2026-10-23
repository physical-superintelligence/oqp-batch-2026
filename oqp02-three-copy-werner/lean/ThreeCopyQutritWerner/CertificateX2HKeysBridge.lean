module

public import ThreeCopyQutritWerner.CertificateX2BridgeKeyFacts
public import ThreeCopyQutritWerner.CertificateX2HKeysFacts
public import ThreeCopyQutritWerner.CertificateX2HKeysCarrierRed
public import ThreeCopyQutritWerner.CertificateX2HKeysCarrierFixAll

@[expose] public section


/-!
# The per-key fields of the bridge's `X2KeyFrameFacts` for the concrete data

Fields `kind_fix`, `trace_count`, `metric_det`, `standard_swap`, `standard_split`, `empty_kinds` of
`X2KeyFrameFacts x2DataConcrete`, from the mirror-form results of CertificateX2HKeysFacts and
CertificateX2HKeysTrace (kernel checks over the 122 h keys). This module only identifies the
bridge's frame-coordinate objects with the mirrors (`x2ImageFrame_concrete`, `x2hCarrier_eq`).
`x2KeyFrameFacts_concrete : X2KeyFrameFacts x2DataConcrete` assembles all seven fields; `carrier_fix`
comes from `x2hCarrierFix_all` (CertificateX2HKeysCarrierFixAll: E = e_A e_[3,2] and the packed transposition
checks of every image column). `x2KeyFrameFacts_of_carrierFix` and `x2KeyFrameFacts_of_transp` are the
intermediate forms.
-/

set_option maxRecDepth 100000

open scoped BigOperators Matrix ComplexOrder

namespace ThreeCopyQutritWerner.X2Sites

open X2

/-- Row-major coordinates of a natural number recompose it. -/
theorem flat_arith (i S1 S2 : ℕ) :
    (i / (S1 * S2) * S1 + i % (S1 * S2) / S2) * S2 + i % (S1 * S2) % S2 = i := by
  have h1 := Nat.div_add_mod (i % (S1 * S2)) S2
  have h2 := Nat.div_add_mod i (S1 * S2)
  calc (i / (S1 * S2) * S1 + i % (S1 * S2) / S2) * S2 + i % (S1 * S2) % S2
      = S1 * S2 * (i / (S1 * S2)) + (S2 * (i % (S1 * S2) / S2) + i % (S1 * S2) % S2) := by ring
    _ = S1 * S2 * (i / (S1 * S2)) + i % (S1 * S2) := by rw [h1]
    _ = i := h2

theorem flat_arith' (i S1 S2 q r : ℕ) (hq : S1 = q) (hr : S2 = r) :
    (i / (S1 * S2) * q + i % (S1 * S2) / S2) * r + i % (S1 * S2) % S2 = i := by
  subst hq hr
  exact flat_arith i S1 S2

/-- The concrete image of an h key in frame coordinates is the packed image `J_b[i, c]`. -/
theorem x2ImageFrame_concrete (b : x2Key 0) : x2ImageFrame x2DataConcrete b = x2hImage b := by
  ext i c
  have h1 : certificatePhysicalFrameSystem0.size (x2KeyTau b).2.1 = x2KeyMult 0 b 1 := x2_keyTau_size b 1
  have h2 : certificatePhysicalFrameSystem0.size (x2KeyTau b).2.2 = x2KeyMult 0 b 2 := x2_keyTau_size b 2
  have hflat : x2FlatIndex (x2DecKey b i) = (i : ℕ) := by
    have e0 : ((x2DecKey b i).1 : ℕ) = (i : ℕ) / (certificatePhysicalFrameSystem0.size (x2KeyTau b).2.1 *
        certificatePhysicalFrameSystem0.size (x2KeyTau b).2.2) := rfl
    have e1 : ((x2DecKey b i).2.1 : ℕ) = (i : ℕ) % (certificatePhysicalFrameSystem0.size (x2KeyTau b).2.1 *
        certificatePhysicalFrameSystem0.size (x2KeyTau b).2.2) /
          certificatePhysicalFrameSystem0.size (x2KeyTau b).2.2 := rfl
    have e2 : ((x2DecKey b i).2.2 : ℕ) = (i : ℕ) % (certificatePhysicalFrameSystem0.size (x2KeyTau b).2.1 *
        certificatePhysicalFrameSystem0.size (x2KeyTau b).2.2) %
          certificatePhysicalFrameSystem0.size (x2KeyTau b).2.2 := rfl
    unfold x2FlatIndex
    rw [e0, e1, e2]
    exact flat_arith' _ _ _ _ _ h1 h2
  exact congrArg (fun n : ℕ => ((X2.x2JEntry (x2KeyGlobal 0 b) n c : ℤ) : ℂ)) hflat

/-- The infrastructure's sector-0 carrier is the mirror `x2hCarrier` (same bodies, literal data copies). -/
theorem x2hCarrier_eq (τ : Fin 7 × Fin 7 × Fin 7) : certificateCarrierJointAction0 τ = x2hCarrier τ := rfl

theorem x2KeyFrame_kind_fix (b : x2Key 0) :
    x2KindProjFrame (x2KeyTau b) (x2KeyKind 0 b) * x2ImageFrame x2DataConcrete b =
      x2ImageFrame x2DataConcrete b := by
  rw [x2ImageFrame_concrete]
  exact x2hKindFix b

theorem x2KeyFrame_trace_count (b : x2Key 0) :
    (certificateCarrierJointAction0 (x2KeyTau b) * x2KindProjFrame (x2KeyTau b) (x2KeyKind 0 b)).trace =
      ((x2KeyDegree 0 b * x2KeySize 0 b : ℕ) : ℂ) := by
  rw [x2hCarrier_eq]
  exact x2hTraceCount b

theorem x2KeyFrame_metric_det (b : x2Key 0) :
    ((x2ImageFrame x2DataConcrete b)ᴴ * certificateThreeSiteFrameSystem0.metric (x2KeyTau b) *
      x2ImageFrame x2DataConcrete b).det ≠ 0 := by
  rw [x2ImageFrame_concrete]
  have hpd := Matrix.PosDef.conjTranspose_mul_mul_same
    (certificateThreeSiteFrameSystem0.metric_posDef (x2KeyTau b)) (x2hImage_injective b)
  exact ((Matrix.isUnit_iff_isUnit_det _).mp hpd.isUnit).ne_zero

theorem x2KeyFrame_standard_swap (b : x2Key 0) (hb : x2KeyDegree 0 b = 2) :
    x2SlotPermFrame (x2KeyTau b) x2Swap01Idx * x2ImageFrame x2DataConcrete b =
      x2ImageFrame x2DataConcrete b := by
  rw [x2ImageFrame_concrete]
  exact x2hStdSwap b hb

theorem x2KeyFrame_standard_split (b : x2Key 0) (hb : x2KeyDegree 0 b = 2) :
    (certificateCarrierJointAction0 (x2KeyTau b) * x2KindProjFrame (x2KeyTau b) 2 *
      x2SlotPermFrame (x2KeyTau b) x2Swap01Idx).trace = 0 := by
  rw [x2hCarrier_eq]
  exact x2hStdSplit b hb

theorem x2KeyFrame_empty_kinds : ∀ τ : Fin 7 × Fin 7 × Fin 7, τ.1 ≤ τ.2.1 → τ.2.1 ≤ τ.2.2 →
    ∀ k : ℕ, k < x2NumKinds τ → (∀ b : x2Key 0, x2KeyTau b = τ → x2KeyKind 0 b ≠ k) →
      (certificateCarrierJointAction0 τ * x2KindProjFrame τ k).trace = 0 := by
  intro τ h1 h2 k hk hno
  rw [x2hCarrier_eq]
  exact x2hEmptyKinds τ h1 h2 k hk hno

/-- `X2KeyFrameFacts x2DataConcrete` from its field `carrier_fix`. -/
theorem x2KeyFrameFacts_of_carrierFix
    (hcar : ∀ b : x2Key 0, certificateCarrierJointAction0 (x2KeyTau b) * x2ImageFrame x2DataConcrete b =
      x2ImageFrame x2DataConcrete b) :
    X2KeyFrameFacts x2DataConcrete where
  carrier_fix := hcar
  kind_fix := x2KeyFrame_kind_fix
  trace_count := x2KeyFrame_trace_count
  metric_det := x2KeyFrame_metric_det
  standard_swap := x2KeyFrame_standard_swap
  standard_split := x2KeyFrame_standard_split
  empty_kinds := x2KeyFrame_empty_kinds

/-- `carrier_fix` for one key from its three transposition identities (CertificateX2HKeysCarrierRed). -/
theorem x2KeyFrame_carrier_fix_of_transp (b : x2Key 0)
    (h12 : rhoG (x2hTau b) (x2hSpecial 5) * x2hImage b = -x2hImage b)
    (h34 : rhoG (x2hTau b) (x2hSpecial 10) * x2hImage b = -x2hImage b)
    (hT : (∑ u : Fin 10, rhoG (x2hTau b) (x2hSpecial u.succ.castSucc)) * x2hImage b = (2 : ℂ) • x2hImage b) :
    certificateCarrierJointAction0 (x2KeyTau b) * x2ImageFrame x2DataConcrete b =
      x2ImageFrame x2DataConcrete b := by
  rw [x2hCarrier_eq, x2ImageFrame_concrete]
  exact x2hCarrierFix b h12 h34 hT

/-- `X2KeyFrameFacts x2DataConcrete` from three transposition identities per key. -/
theorem x2KeyFrameFacts_of_transp
    (htr : ∀ b : x2Key 0, rhoG (x2hTau b) (x2hSpecial 5) * x2hImage b = -x2hImage b ∧
      rhoG (x2hTau b) (x2hSpecial 10) * x2hImage b = -x2hImage b ∧
      (∑ u : Fin 10, rhoG (x2hTau b) (x2hSpecial u.succ.castSucc)) * x2hImage b = (2 : ℂ) • x2hImage b) :
    X2KeyFrameFacts x2DataConcrete :=
  x2KeyFrameFacts_of_carrierFix fun b =>
    x2KeyFrame_carrier_fix_of_transp b (htr b).1 (htr b).2.1 (htr b).2.2

/-- `carrier_fix` for the concrete data (all 122 h keys). -/
theorem x2KeyFrame_carrier_fix (b : x2Key 0) :
    certificateCarrierJointAction0 (x2KeyTau b) * x2ImageFrame x2DataConcrete b =
      x2ImageFrame x2DataConcrete b := by
  rw [x2hCarrier_eq, x2ImageFrame_concrete]
  exact x2hCarrierFix_all b

/-- The bridge's per-key facts for the concrete data. -/
theorem x2KeyFrameFacts_concrete : X2KeyFrameFacts x2DataConcrete :=
  x2KeyFrameFacts_of_carrierFix x2KeyFrame_carrier_fix

end ThreeCopyQutritWerner.X2Sites
