module

public import ThreeCopyQutritWerner.CertificateX2SitesDict

@[expose] public section


/-! Natural-axpy kernel checks (x2sDict, sector 1), 64 units per declaration. -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option profiler true
set_option profiler.threshold 1000

namespace ThreeCopyQutritWerner.X2Sites

open X2

theorem x2sDict1_check3 : ∀ u < 513, 192 ≤ u → u < 256 →
    natAxpyCheck 48 513 26 ((x2sW1.getD u []).map (fun x => 2 * x)) x2sComp0
      (qpackAux 1 u 513) (natAxpyCorr 48 513 26 x2sComp0) = true := by
  decide +kernel

theorem x2sDict1_check4 : ∀ u < 513, 256 ≤ u → u < 320 →
    natAxpyCheck 48 513 26 ((x2sW1.getD u []).map (fun x => 2 * x)) x2sComp0
      (qpackAux 1 u 513) (natAxpyCorr 48 513 26 x2sComp0) = true := by
  decide +kernel

theorem x2sDict1_check5 : ∀ u < 513, 320 ≤ u → u < 384 →
    natAxpyCheck 48 513 26 ((x2sW1.getD u []).map (fun x => 2 * x)) x2sComp0
      (qpackAux 1 u 513) (natAxpyCorr 48 513 26 x2sComp0) = true := by
  decide +kernel

end ThreeCopyQutritWerner.X2Sites
