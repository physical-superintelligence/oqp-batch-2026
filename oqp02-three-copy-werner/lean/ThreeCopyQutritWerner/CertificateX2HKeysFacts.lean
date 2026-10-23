module

public import ThreeCopyQutritWerner.CertificateX2HKeysKindCheck0
public import ThreeCopyQutritWerner.CertificateX2HKeysKindCheck1
public import ThreeCopyQutritWerner.CertificateX2HKeysKindCheck2
public import ThreeCopyQutritWerner.CertificateX2HKeysKindCheck3
public import ThreeCopyQutritWerner.CertificateX2HKeysInjCheck0
public import ThreeCopyQutritWerner.CertificateX2HKeysKindSound

@[expose] public section


/-! Per-key facts of the 122 h keys, frame-coordinate mirrors:
the kind projector and (standard keys) the first-two-slot swap fix the image; the image is injective. -/

set_option maxRecDepth 100000

namespace ThreeCopyQutritWerner.X2Sites

open X2

theorem kindCheck_all (b : x2Key 0) : kindCheck b = true := by
  by_cases h0 : (b : ℕ) < 100
  · exact kindCheck_c0 b (by omega) h0
  by_cases h1 : (b : ℕ) < 101
  · exact kindCheck_c1 b (by omega) h1
  by_cases h2 : (b : ℕ) < 102
  · exact kindCheck_c2 b (by omega) h2
  by_cases h3 : (b : ℕ) < 103
  · exact kindCheck_c3 b (by omega) h3
  by_cases h4 : (b : ℕ) < 105
  · exact kindCheck_c4 b (by omega) h4
  by_cases h5 : (b : ℕ) < 107
  · exact kindCheck_c5 b (by omega) h5
  by_cases h6 : (b : ℕ) < 113
  · exact kindCheck_c6 b (by omega) h6
  by_cases h7 : (b : ℕ) < 119
  · exact kindCheck_c7 b (by omega) h7
  by_cases h8 : (b : ℕ) < 121
  · exact kindCheck_c8 b (by omega) h8
  · exact kindCheck_c9 b (by omega) b.isLt

theorem injCheck_all (b : x2Key 0) : injCheck b = true := by
  by_cases h0 : (b : ℕ) < 105
  · exact injCheck_c0 b (by omega) h0
  by_cases h1 : (b : ℕ) < 110
  · exact injCheck_c1 b (by omega) h1
  · exact injCheck_c2 b (by omega) b.isLt

/-- The kind projector of every h key fixes its image (mirror of the bridge's `kind_fix`). -/
theorem x2hKindFix (b : x2Key 0) : x2hKindProj (x2hTau b) (x2KeyKind 0 b) * x2hImage b = x2hImage b :=
  (kindCheck_sound b (kindCheck_all b)).1

/-- The first-two-slot swap fixes every standard image (mirror of `standard_swap`). -/
theorem x2hStdSwap (b : x2Key 0) (hb : x2KeyDegree 0 b = 2) :
    x2hSlotPerm (x2hTau b) x2Swap01Idx * x2hImage b = x2hImage b :=
  (kindCheck_sound b (kindCheck_all b)).2 hb

/-- Every h image is injective (for `metric_det`). -/
theorem x2hImage_injective (b : x2Key 0) : Function.Injective (x2hImage b).mulVec :=
  injCheck_sound b (injCheck_all b)

end ThreeCopyQutritWerner.X2Sites
