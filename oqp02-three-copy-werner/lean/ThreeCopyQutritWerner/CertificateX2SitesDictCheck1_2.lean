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

theorem x2sDict1_check6 : ∀ u < 513, 384 ≤ u → u < 448 →
    natAxpyCheck 48 513 26 ((x2sW1.getD u []).map (fun x => 2 * x)) x2sComp0
      (qpackAux 1 u 513) (natAxpyCorr 48 513 26 x2sComp0) = true := by
  decide +kernel

theorem x2sDict1_check7 : ∀ u < 513, 448 ≤ u → u < 512 →
    natAxpyCheck 48 513 26 ((x2sW1.getD u []).map (fun x => 2 * x)) x2sComp0
      (qpackAux 1 u 513) (natAxpyCorr 48 513 26 x2sComp0) = true := by
  decide +kernel

theorem x2sDict1_check8 : ∀ u < 513, 512 ≤ u → u < 513 →
    natAxpyCheck 48 513 26 ((x2sW1.getD u []).map (fun x => 2 * x)) x2sComp0
      (qpackAux 1 u 513) (natAxpyCorr 48 513 26 x2sComp0) = true := by
  decide +kernel

end ThreeCopyQutritWerner.X2Sites
