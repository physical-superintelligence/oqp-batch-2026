module

public import ThreeCopyQutritWerner.CertificateX2SitesWData
public import ThreeCopyQutritWerner.CertificateX2SitesFiberOK

@[expose] public section


/-! The sector-2 unit-weight rows have length 513 and entries below `2^26`
(kernel, 64 rows per declaration). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option profiler true
set_option profiler.threshold 1000

namespace ThreeCopyQutritWerner.X2Sites

open X2

theorem x2sW2_rows0 : ∀ u < 513, 0 ≤ u → u < 64 → rowOK (x2sW2.getD u []) = true := by
  decide +kernel

theorem x2sW2_rows1 : ∀ u < 513, 64 ≤ u → u < 128 → rowOK (x2sW2.getD u []) = true := by
  decide +kernel

theorem x2sW2_rows2 : ∀ u < 513, 128 ≤ u → u < 192 → rowOK (x2sW2.getD u []) = true := by
  decide +kernel

theorem x2sW2_rows3 : ∀ u < 513, 192 ≤ u → u < 256 → rowOK (x2sW2.getD u []) = true := by
  decide +kernel

theorem x2sW2_rows4 : ∀ u < 513, 256 ≤ u → u < 320 → rowOK (x2sW2.getD u []) = true := by
  decide +kernel

theorem x2sW2_rows5 : ∀ u < 513, 320 ≤ u → u < 384 → rowOK (x2sW2.getD u []) = true := by
  decide +kernel

theorem x2sW2_rows6 : ∀ u < 513, 384 ≤ u → u < 448 → rowOK (x2sW2.getD u []) = true := by
  decide +kernel

theorem x2sW2_rows7 : ∀ u < 513, 448 ≤ u → u < 512 → rowOK (x2sW2.getD u []) = true := by
  decide +kernel

theorem x2sW2_rows8 : ∀ u < 513, 512 ≤ u → u < 513 → rowOK (x2sW2.getD u []) = true := by
  decide +kernel

theorem x2sW2_shape : ∀ u < 513, rowOK (x2sW2.getD u []) = true := by
  intro u hu
  by_cases h0 : u < 64
  · exact x2sW2_rows0 u hu (by omega) h0
  by_cases h1 : u < 128
  · exact x2sW2_rows1 u hu (by omega) h1
  by_cases h2 : u < 192
  · exact x2sW2_rows2 u hu (by omega) h2
  by_cases h3 : u < 256
  · exact x2sW2_rows3 u hu (by omega) h3
  by_cases h4 : u < 320
  · exact x2sW2_rows4 u hu (by omega) h4
  by_cases h5 : u < 384
  · exact x2sW2_rows5 u hu (by omega) h5
  by_cases h6 : u < 448
  · exact x2sW2_rows6 u hu (by omega) h6
  by_cases h7 : u < 512
  · exact x2sW2_rows7 u hu (by omega) h7
  · exact x2sW2_rows8 u hu (by omega) hu

end ThreeCopyQutritWerner.X2Sites
