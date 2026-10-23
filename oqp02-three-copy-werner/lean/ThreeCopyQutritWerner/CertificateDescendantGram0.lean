module

public import ThreeCopyQutritWerner.CertificateDescendantGram2
public import ThreeCopyQutritWerner.CertificateDescendantFrames0

@[expose] public section


/-! Sector 0 has the same scalar descendant metric through the exact physical
endpoint-register swap. Its source metric is still the original sector-0 G. -/

noncomputable section

set_option maxRecDepth 100000
set_option maxHeartbeats 100000000

open scoped Matrix

namespace ThreeCopyQutritWerner

def certificateDescendantGram0G : (t : Fin 7) →
    Matrix (Fin (certificateDescendantFrames2SourceSize t))
      (Fin (certificateDescendantFrames2SourceSize t)) ℤ := by
  exact
    Fin.cases (certificateLocalGram0_0) <|
    Fin.cases (certificateLocalGram0_1) <|
    Fin.cases (certificateLocalGram0_2) <|
    Fin.cases (certificateLocalGram0_3) <|
    Fin.cases (certificateLocalGram0_4) <|
    Fin.cases (certificateLocalGram0_5) <|
    Fin.cases (certificateLocalGram0_6) <|
    Fin.rec0

theorem certificateDescendantGram0G_eq : certificateDescendantGram0G = certificateDescendantGram2G := by
  funext t
  fin_cases t <;> decide +kernel

def certificateDescendantGram0Metric : Matrix CertificateDescendantFramesIndex2
    CertificateDescendantFramesIndex2 ℤ :=
  certificateRepeatedFrameMetric certificateDescendantFrames2SourceSize
    certificateDescendantFrames2Type certificateDescendantGram0G certificateDescendantGram2K

theorem certificateDescendantGram0Metric_eq :
    certificateDescendantGram0Metric = certificateDescendantGram2Metric := by
  unfold certificateDescendantGram0Metric
  rw [certificateDescendantGram0G_eq]
  rfl

theorem certificateDescendantGram0_physical :
    certificateDescendantFrames0Matrixᵀ * certificateDescendantFrames0Matrix =
      certificateDescendantGram0Metric := by
  have hS : certificateDescendantFrames0Matrix =
      certificateDescendantFrames2Matrix.submatrix certificateFlipEnds id := by
    ext w ⟨f, j⟩
    exact certificateDescendantFrames0Frame_flip f w j
  rw [hS, certificateDescendantGram0Metric_eq]
  calc
    (certificateDescendantFrames2Matrix.submatrix certificateFlipEnds id)ᵀ *
        certificateDescendantFrames2Matrix.submatrix certificateFlipEnds id =
        certificateDescendantFrames2Matrixᵀ * certificateDescendantFrames2Matrix := by
      exact (Matrix.submatrix_mul certificateDescendantFrames2Matrixᵀ
        certificateDescendantFrames2Matrix id certificateFlipEnds id
        certificateFlipEnds.bijective).symm
    _ = _ := certificateDescendantGram2_physical

end ThreeCopyQutritWerner
