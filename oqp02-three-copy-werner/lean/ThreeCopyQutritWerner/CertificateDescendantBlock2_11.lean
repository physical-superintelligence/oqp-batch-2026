module

public import ThreeCopyQutritWerner.CertificateDescendantBlock2_11BoundedData
public import ThreeCopyQutritWerner.CertificateDescendantBlock2_11Check00
public import ThreeCopyQutritWerner.CertificateDescendantBlock2_11Check01
public import ThreeCopyQutritWerner.CertificateDescendantBlock2_11Check02
public import ThreeCopyQutritWerner.CertificateDescendantBlock2_11Check03
public import ThreeCopyQutritWerner.CertificateDescendantBlock2_11Check04
public import ThreeCopyQutritWerner.CertificateDescendantBlock2_11Check05
public import ThreeCopyQutritWerner.CertificateDescendantBlock2_11Check06
public import ThreeCopyQutritWerner.CertificateDescendantBlock2_11Check07
public import ThreeCopyQutritWerner.CertificateDescendantBlock2_11Check08
public import ThreeCopyQutritWerner.CertificateDescendantBlock2_11Check09
public import ThreeCopyQutritWerner.CertificateDescendantBlock2_11Check10
public import ThreeCopyQutritWerner.CertificateDescendantBlock2_11Check11
public import ThreeCopyQutritWerner.CertificateDescendantBlock2_11Check12
public import ThreeCopyQutritWerner.CertificateDescendantBlock2_11Check13
public import ThreeCopyQutritWerner.CertificateDescendantBlock2_11Check14
public import ThreeCopyQutritWerner.CertificateDescendantBlock2_11Check15
public import ThreeCopyQutritWerner.CertificateDescendantBlock2_11Check16
public import ThreeCopyQutritWerner.CertificateDescendantBlock2_11Check17
public import ThreeCopyQutritWerner.CertificateDescendantBlock2_11Check18
public import ThreeCopyQutritWerner.CertificateDescendantBlock2_11Check19
public import ThreeCopyQutritWerner.CertificateDescendantBlock2_11Check20
public import ThreeCopyQutritWerner.CertificateDescendantBlock2_11Check21
public import ThreeCopyQutritWerner.CertificateDescendantBlock2_11Check22
public import ThreeCopyQutritWerner.CertificateDescendantBlock2_11Check23
public import ThreeCopyQutritWerner.CertificateDescendantBlock2_11Check24
public import ThreeCopyQutritWerner.CertificateDescendantBlock2_11Check25
public import ThreeCopyQutritWerner.CertificateDescendantBlock2_11Check26
public import ThreeCopyQutritWerner.CertificateDescendantBlock2_11Check27
public import ThreeCopyQutritWerner.CertificateDescendantBlock2_11Check28
public import ThreeCopyQutritWerner.CertificateDescendantBlock2_11Check29
public import ThreeCopyQutritWerner.CertificateDescendantBlock2_11Check30
public import ThreeCopyQutritWerner.CertificateDescendantBlock2_11Check31
public import ThreeCopyQutritWerner.CertificateDescendantBlock2_11Check32
public import ThreeCopyQutritWerner.CertificateDescendantBlock2_11Check33
public import ThreeCopyQutritWerner.CertificateDescendantBlock2_11Check34
public import ThreeCopyQutritWerner.CertificateDescendantBlock2_11Check35
public import ThreeCopyQutritWerner.CertificateDescendantBlock2_11Check36
public import ThreeCopyQutritWerner.CertificateDescendantBlock2_11Check37
public import ThreeCopyQutritWerner.CertificateDescendantBlock2_11Check38
public import ThreeCopyQutritWerner.CertificateDescendantBlock2_11Check39
public import ThreeCopyQutritWerner.CertificateMatrixLiteral
public import ThreeCopyQutritWerner.CertificateDescendantData

@[expose] public section


set_option maxRecDepth 100000
set_option maxHeartbeats 100000000

open scoped Matrix

namespace ThreeCopyQutritWerner

/-- Exact integer inverse certificate for signed physical weight [-2, -1, -1]. -/
theorem certificateDescendantBlock2_11_inverse :
    certificateDescendantBlockA2_11 * certificateDescendantBlockW2_11 =
      (15120 : ℤ) • (1 : Matrix (Fin 80) (Fin 80) ℤ) := by
  apply Matrix.ext
  intro i j
  fin_cases i
  · exact certificateDescendantBlock2_11Check00_inverse 0 j
  · exact certificateDescendantBlock2_11Check00_inverse 1 j
  · exact certificateDescendantBlock2_11Check01_inverse 0 j
  · exact certificateDescendantBlock2_11Check01_inverse 1 j
  · exact certificateDescendantBlock2_11Check02_inverse 0 j
  · exact certificateDescendantBlock2_11Check02_inverse 1 j
  · exact certificateDescendantBlock2_11Check03_inverse 0 j
  · exact certificateDescendantBlock2_11Check03_inverse 1 j
  · exact certificateDescendantBlock2_11Check04_inverse 0 j
  · exact certificateDescendantBlock2_11Check04_inverse 1 j
  · exact certificateDescendantBlock2_11Check05_inverse 0 j
  · exact certificateDescendantBlock2_11Check05_inverse 1 j
  · exact certificateDescendantBlock2_11Check06_inverse 0 j
  · exact certificateDescendantBlock2_11Check06_inverse 1 j
  · exact certificateDescendantBlock2_11Check07_inverse 0 j
  · exact certificateDescendantBlock2_11Check07_inverse 1 j
  · exact certificateDescendantBlock2_11Check08_inverse 0 j
  · exact certificateDescendantBlock2_11Check08_inverse 1 j
  · exact certificateDescendantBlock2_11Check09_inverse 0 j
  · exact certificateDescendantBlock2_11Check09_inverse 1 j
  · exact certificateDescendantBlock2_11Check10_inverse 0 j
  · exact certificateDescendantBlock2_11Check10_inverse 1 j
  · exact certificateDescendantBlock2_11Check11_inverse 0 j
  · exact certificateDescendantBlock2_11Check11_inverse 1 j
  · exact certificateDescendantBlock2_11Check12_inverse 0 j
  · exact certificateDescendantBlock2_11Check12_inverse 1 j
  · exact certificateDescendantBlock2_11Check13_inverse 0 j
  · exact certificateDescendantBlock2_11Check13_inverse 1 j
  · exact certificateDescendantBlock2_11Check14_inverse 0 j
  · exact certificateDescendantBlock2_11Check14_inverse 1 j
  · exact certificateDescendantBlock2_11Check15_inverse 0 j
  · exact certificateDescendantBlock2_11Check15_inverse 1 j
  · exact certificateDescendantBlock2_11Check16_inverse 0 j
  · exact certificateDescendantBlock2_11Check16_inverse 1 j
  · exact certificateDescendantBlock2_11Check17_inverse 0 j
  · exact certificateDescendantBlock2_11Check17_inverse 1 j
  · exact certificateDescendantBlock2_11Check18_inverse 0 j
  · exact certificateDescendantBlock2_11Check18_inverse 1 j
  · exact certificateDescendantBlock2_11Check19_inverse 0 j
  · exact certificateDescendantBlock2_11Check19_inverse 1 j
  · exact certificateDescendantBlock2_11Check20_inverse 0 j
  · exact certificateDescendantBlock2_11Check20_inverse 1 j
  · exact certificateDescendantBlock2_11Check21_inverse 0 j
  · exact certificateDescendantBlock2_11Check21_inverse 1 j
  · exact certificateDescendantBlock2_11Check22_inverse 0 j
  · exact certificateDescendantBlock2_11Check22_inverse 1 j
  · exact certificateDescendantBlock2_11Check23_inverse 0 j
  · exact certificateDescendantBlock2_11Check23_inverse 1 j
  · exact certificateDescendantBlock2_11Check24_inverse 0 j
  · exact certificateDescendantBlock2_11Check24_inverse 1 j
  · exact certificateDescendantBlock2_11Check25_inverse 0 j
  · exact certificateDescendantBlock2_11Check25_inverse 1 j
  · exact certificateDescendantBlock2_11Check26_inverse 0 j
  · exact certificateDescendantBlock2_11Check26_inverse 1 j
  · exact certificateDescendantBlock2_11Check27_inverse 0 j
  · exact certificateDescendantBlock2_11Check27_inverse 1 j
  · exact certificateDescendantBlock2_11Check28_inverse 0 j
  · exact certificateDescendantBlock2_11Check28_inverse 1 j
  · exact certificateDescendantBlock2_11Check29_inverse 0 j
  · exact certificateDescendantBlock2_11Check29_inverse 1 j
  · exact certificateDescendantBlock2_11Check30_inverse 0 j
  · exact certificateDescendantBlock2_11Check30_inverse 1 j
  · exact certificateDescendantBlock2_11Check31_inverse 0 j
  · exact certificateDescendantBlock2_11Check31_inverse 1 j
  · exact certificateDescendantBlock2_11Check32_inverse 0 j
  · exact certificateDescendantBlock2_11Check32_inverse 1 j
  · exact certificateDescendantBlock2_11Check33_inverse 0 j
  · exact certificateDescendantBlock2_11Check33_inverse 1 j
  · exact certificateDescendantBlock2_11Check34_inverse 0 j
  · exact certificateDescendantBlock2_11Check34_inverse 1 j
  · exact certificateDescendantBlock2_11Check35_inverse 0 j
  · exact certificateDescendantBlock2_11Check35_inverse 1 j
  · exact certificateDescendantBlock2_11Check36_inverse 0 j
  · exact certificateDescendantBlock2_11Check36_inverse 1 j
  · exact certificateDescendantBlock2_11Check37_inverse 0 j
  · exact certificateDescendantBlock2_11Check37_inverse 1 j
  · exact certificateDescendantBlock2_11Check38_inverse 0 j
  · exact certificateDescendantBlock2_11Check38_inverse 1 j
  · exact certificateDescendantBlock2_11Check39_inverse 0 j
  · exact certificateDescendantBlock2_11Check39_inverse 1 j

theorem certificateDescendantBlock2_11_rows_injective :
    Function.Injective (certificateDescendantBlockRows2 11) := by
  decide +kernel

theorem certificateDescendantBlock2_11_row_weight (i : Fin 80) :
    (fun r => certificateLocalWeight {0} (certificateDescendantBlockRows2 11 i) r) =
      certificateDescendantWeights2 11 := by
  revert i
  decide +kernel

theorem certificateDescendantBlock2_11_column_weight (j : Fin 80) :
    List.Forall (fun a => (fun r => certificateLocalWeight {0} a.1 r) =
      certificateDescendantWeights2 11)
      (certificateDescendantColumns2 (certificateDescendantBlockColumns2 11 j)) := by
  revert j
  decide +kernel

theorem certificateDescendantBlock2_11_physical (i j : Fin 80) :
    certificateSparseVector
      (certificateDescendantColumns2 (certificateDescendantBlockColumns2 11 j))
      (certificateDescendantBlockRows2 11 i) = certificateDescendantBlockA2_11 i j := by
  fin_cases i
  · exact certificateDescendantBlock2_11Check00_physical 0 j
  · exact certificateDescendantBlock2_11Check00_physical 1 j
  · exact certificateDescendantBlock2_11Check01_physical 0 j
  · exact certificateDescendantBlock2_11Check01_physical 1 j
  · exact certificateDescendantBlock2_11Check02_physical 0 j
  · exact certificateDescendantBlock2_11Check02_physical 1 j
  · exact certificateDescendantBlock2_11Check03_physical 0 j
  · exact certificateDescendantBlock2_11Check03_physical 1 j
  · exact certificateDescendantBlock2_11Check04_physical 0 j
  · exact certificateDescendantBlock2_11Check04_physical 1 j
  · exact certificateDescendantBlock2_11Check05_physical 0 j
  · exact certificateDescendantBlock2_11Check05_physical 1 j
  · exact certificateDescendantBlock2_11Check06_physical 0 j
  · exact certificateDescendantBlock2_11Check06_physical 1 j
  · exact certificateDescendantBlock2_11Check07_physical 0 j
  · exact certificateDescendantBlock2_11Check07_physical 1 j
  · exact certificateDescendantBlock2_11Check08_physical 0 j
  · exact certificateDescendantBlock2_11Check08_physical 1 j
  · exact certificateDescendantBlock2_11Check09_physical 0 j
  · exact certificateDescendantBlock2_11Check09_physical 1 j
  · exact certificateDescendantBlock2_11Check10_physical 0 j
  · exact certificateDescendantBlock2_11Check10_physical 1 j
  · exact certificateDescendantBlock2_11Check11_physical 0 j
  · exact certificateDescendantBlock2_11Check11_physical 1 j
  · exact certificateDescendantBlock2_11Check12_physical 0 j
  · exact certificateDescendantBlock2_11Check12_physical 1 j
  · exact certificateDescendantBlock2_11Check13_physical 0 j
  · exact certificateDescendantBlock2_11Check13_physical 1 j
  · exact certificateDescendantBlock2_11Check14_physical 0 j
  · exact certificateDescendantBlock2_11Check14_physical 1 j
  · exact certificateDescendantBlock2_11Check15_physical 0 j
  · exact certificateDescendantBlock2_11Check15_physical 1 j
  · exact certificateDescendantBlock2_11Check16_physical 0 j
  · exact certificateDescendantBlock2_11Check16_physical 1 j
  · exact certificateDescendantBlock2_11Check17_physical 0 j
  · exact certificateDescendantBlock2_11Check17_physical 1 j
  · exact certificateDescendantBlock2_11Check18_physical 0 j
  · exact certificateDescendantBlock2_11Check18_physical 1 j
  · exact certificateDescendantBlock2_11Check19_physical 0 j
  · exact certificateDescendantBlock2_11Check19_physical 1 j
  · exact certificateDescendantBlock2_11Check20_physical 0 j
  · exact certificateDescendantBlock2_11Check20_physical 1 j
  · exact certificateDescendantBlock2_11Check21_physical 0 j
  · exact certificateDescendantBlock2_11Check21_physical 1 j
  · exact certificateDescendantBlock2_11Check22_physical 0 j
  · exact certificateDescendantBlock2_11Check22_physical 1 j
  · exact certificateDescendantBlock2_11Check23_physical 0 j
  · exact certificateDescendantBlock2_11Check23_physical 1 j
  · exact certificateDescendantBlock2_11Check24_physical 0 j
  · exact certificateDescendantBlock2_11Check24_physical 1 j
  · exact certificateDescendantBlock2_11Check25_physical 0 j
  · exact certificateDescendantBlock2_11Check25_physical 1 j
  · exact certificateDescendantBlock2_11Check26_physical 0 j
  · exact certificateDescendantBlock2_11Check26_physical 1 j
  · exact certificateDescendantBlock2_11Check27_physical 0 j
  · exact certificateDescendantBlock2_11Check27_physical 1 j
  · exact certificateDescendantBlock2_11Check28_physical 0 j
  · exact certificateDescendantBlock2_11Check28_physical 1 j
  · exact certificateDescendantBlock2_11Check29_physical 0 j
  · exact certificateDescendantBlock2_11Check29_physical 1 j
  · exact certificateDescendantBlock2_11Check30_physical 0 j
  · exact certificateDescendantBlock2_11Check30_physical 1 j
  · exact certificateDescendantBlock2_11Check31_physical 0 j
  · exact certificateDescendantBlock2_11Check31_physical 1 j
  · exact certificateDescendantBlock2_11Check32_physical 0 j
  · exact certificateDescendantBlock2_11Check32_physical 1 j
  · exact certificateDescendantBlock2_11Check33_physical 0 j
  · exact certificateDescendantBlock2_11Check33_physical 1 j
  · exact certificateDescendantBlock2_11Check34_physical 0 j
  · exact certificateDescendantBlock2_11Check34_physical 1 j
  · exact certificateDescendantBlock2_11Check35_physical 0 j
  · exact certificateDescendantBlock2_11Check35_physical 1 j
  · exact certificateDescendantBlock2_11Check36_physical 0 j
  · exact certificateDescendantBlock2_11Check36_physical 1 j
  · exact certificateDescendantBlock2_11Check37_physical 0 j
  · exact certificateDescendantBlock2_11Check37_physical 1 j
  · exact certificateDescendantBlock2_11Check38_physical 0 j
  · exact certificateDescendantBlock2_11Check38_physical 1 j
  · exact certificateDescendantBlock2_11Check39_physical 0 j
  · exact certificateDescendantBlock2_11Check39_physical 1 j

end ThreeCopyQutritWerner
