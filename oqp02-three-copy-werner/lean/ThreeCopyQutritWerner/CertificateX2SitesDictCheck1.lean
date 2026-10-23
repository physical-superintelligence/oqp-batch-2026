module

public import ThreeCopyQutritWerner.CertificateX2SitesDictCheck1_0
public import ThreeCopyQutritWerner.CertificateX2SitesDictCheck1_1
public import ThreeCopyQutritWerner.CertificateX2SitesDictCheck1_2

@[expose] public section


/-! `∑_p 2 Wnum_1[p, u] · C_0(piv p) = qpack 1 u` for every unit (dispatch over chunks). -/

namespace ThreeCopyQutritWerner.X2Sites

open X2

theorem x2sDict1_check (u : ℕ) (hu : u < 513) :
    natAxpyCheck 48 513 26 ((x2sW1.getD u []).map (fun x => 2 * x)) x2sComp0
      (qpackAux 1 u 513) (natAxpyCorr 48 513 26 x2sComp0) = true := by
  by_cases h0 : u < 64
  · exact x2sDict1_check0 u hu (by omega) h0
  by_cases h1 : u < 128
  · exact x2sDict1_check1 u hu (by omega) h1
  by_cases h2 : u < 192
  · exact x2sDict1_check2 u hu (by omega) h2
  by_cases h3 : u < 256
  · exact x2sDict1_check3 u hu (by omega) h3
  by_cases h4 : u < 320
  · exact x2sDict1_check4 u hu (by omega) h4
  by_cases h5 : u < 384
  · exact x2sDict1_check5 u hu (by omega) h5
  by_cases h6 : u < 448
  · exact x2sDict1_check6 u hu (by omega) h6
  by_cases h7 : u < 512
  · exact x2sDict1_check7 u hu (by omega) h7
  · exact x2sDict1_check8 u hu (by omega) hu

end ThreeCopyQutritWerner.X2Sites
