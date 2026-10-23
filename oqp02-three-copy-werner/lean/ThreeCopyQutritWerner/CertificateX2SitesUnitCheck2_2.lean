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

theorem x2sUnit2_check6 : ∀ u < 513, 384 ≤ u → u < 448 →
    natAxpyCheck 48 513 25 (x2sW2.getD u []) x2sComp2
      (offset 48 (48 - 1) 513 + 6350400 * 2 ^ (48 * u)) (natAxpyCorr 48 513 25 x2sComp2) = true := by
  decide +kernel

theorem x2sUnit2_check7 : ∀ u < 513, 448 ≤ u → u < 512 →
    natAxpyCheck 48 513 25 (x2sW2.getD u []) x2sComp2
      (offset 48 (48 - 1) 513 + 6350400 * 2 ^ (48 * u)) (natAxpyCorr 48 513 25 x2sComp2) = true := by
  decide +kernel

theorem x2sUnit2_check8 : ∀ u < 513, 512 ≤ u → u < 513 →
    natAxpyCheck 48 513 25 (x2sW2.getD u []) x2sComp2
      (offset 48 (48 - 1) 513 + 6350400 * 2 ^ (48 * u)) (natAxpyCorr 48 513 25 x2sComp2) = true := by
  decide +kernel

end ThreeCopyQutritWerner.X2Sites
