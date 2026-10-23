module

public import ThreeCopyQutritWerner.CertificateX2SitesWData
public import ThreeCopyQutritWerner.CertificateX2SitesCompData2
public import ThreeCopyQutritWerner.CertificateX2PackedNatAxpy

@[expose] public section


/-! Natural-axpy kernel checks (x2sUnit, sector 2), 64 units per declaration. -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option profiler true
set_option profiler.threshold 1000

namespace ThreeCopyQutritWerner.X2Sites

open X2

theorem x2sUnit2_check3 : ∀ u < 513, 192 ≤ u → u < 256 →
    natAxpyCheck 48 513 25 (x2sW2.getD u []) x2sComp2
      (offset 48 (48 - 1) 513 + 6350400 * 2 ^ (48 * u)) (natAxpyCorr 48 513 25 x2sComp2) = true := by
  decide +kernel

theorem x2sUnit2_check4 : ∀ u < 513, 256 ≤ u → u < 320 →
    natAxpyCheck 48 513 25 (x2sW2.getD u []) x2sComp2
      (offset 48 (48 - 1) 513 + 6350400 * 2 ^ (48 * u)) (natAxpyCorr 48 513 25 x2sComp2) = true := by
  decide +kernel

theorem x2sUnit2_check5 : ∀ u < 513, 320 ≤ u → u < 384 →
    natAxpyCheck 48 513 25 (x2sW2.getD u []) x2sComp2
      (offset 48 (48 - 1) 513 + 6350400 * 2 ^ (48 * u)) (natAxpyCorr 48 513 25 x2sComp2) = true := by
  decide +kernel

end ThreeCopyQutritWerner.X2Sites
