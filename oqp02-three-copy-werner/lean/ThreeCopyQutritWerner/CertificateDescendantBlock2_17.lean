module

public import ThreeCopyQutritWerner.CertificateDescendantBlock2_17BoundedData
public import ThreeCopyQutritWerner.CertificateDescendantBlock2_17Check00
public import ThreeCopyQutritWerner.CertificateDescendantBlock2_17Check01
public import ThreeCopyQutritWerner.CertificateDescendantBlock2_17Check02
public import ThreeCopyQutritWerner.CertificateDescendantBlock2_17Check03
public import ThreeCopyQutritWerner.CertificateDescendantBlock2_17Check04
public import ThreeCopyQutritWerner.CertificateDescendantBlock2_17Check05
public import ThreeCopyQutritWerner.CertificateDescendantBlock2_17Check06
public import ThreeCopyQutritWerner.CertificateDescendantBlock2_17Check07
public import ThreeCopyQutritWerner.CertificateDescendantBlock2_17Check08
public import ThreeCopyQutritWerner.CertificateDescendantBlock2_17Check09
public import ThreeCopyQutritWerner.CertificateDescendantBlock2_17Check10
public import ThreeCopyQutritWerner.CertificateDescendantBlock2_17Check11
public import ThreeCopyQutritWerner.CertificateDescendantBlock2_17Check12
public import ThreeCopyQutritWerner.CertificateDescendantBlock2_17Check13
public import ThreeCopyQutritWerner.CertificateDescendantBlock2_17Check14
public import ThreeCopyQutritWerner.CertificateDescendantBlock2_17Check15
public import ThreeCopyQutritWerner.CertificateDescendantBlock2_17Check16
public import ThreeCopyQutritWerner.CertificateDescendantBlock2_17Check17
public import ThreeCopyQutritWerner.CertificateDescendantBlock2_17Check18
public import ThreeCopyQutritWerner.CertificateDescendantBlock2_17Check19
public import ThreeCopyQutritWerner.CertificateDescendantBlock2_17Check20
public import ThreeCopyQutritWerner.CertificateDescendantBlock2_17Check21
public import ThreeCopyQutritWerner.CertificateDescendantBlock2_17Check22
public import ThreeCopyQutritWerner.CertificateDescendantBlock2_17Check23
public import ThreeCopyQutritWerner.CertificateDescendantBlock2_17Check24
public import ThreeCopyQutritWerner.CertificateDescendantBlock2_17Check25
public import ThreeCopyQutritWerner.CertificateDescendantBlock2_17Check26
public import ThreeCopyQutritWerner.CertificateDescendantBlock2_17Check27
public import ThreeCopyQutritWerner.CertificateDescendantBlock2_17Check28
public import ThreeCopyQutritWerner.CertificateDescendantBlock2_17Check29
public import ThreeCopyQutritWerner.CertificateDescendantBlock2_17Check30
public import ThreeCopyQutritWerner.CertificateDescendantBlock2_17Check31
public import ThreeCopyQutritWerner.CertificateDescendantBlock2_17Check32
public import ThreeCopyQutritWerner.CertificateDescendantBlock2_17Check33
public import ThreeCopyQutritWerner.CertificateDescendantBlock2_17Check34
public import ThreeCopyQutritWerner.CertificateDescendantBlock2_17Check35
public import ThreeCopyQutritWerner.CertificateDescendantBlock2_17Check36
public import ThreeCopyQutritWerner.CertificateDescendantBlock2_17Check37
public import ThreeCopyQutritWerner.CertificateDescendantBlock2_17Check38
public import ThreeCopyQutritWerner.CertificateDescendantBlock2_17Check39
public import ThreeCopyQutritWerner.CertificateMatrixLiteral
public import ThreeCopyQutritWerner.CertificateDescendantData

@[expose] public section


set_option maxRecDepth 100000
set_option maxHeartbeats 100000000

open scoped Matrix

namespace ThreeCopyQutritWerner

/-- Exact integer inverse certificate for signed physical weight [-1, -1, -2]. -/
theorem certificateDescendantBlock2_17_inverse :
    certificateDescendantBlockA2_17 * certificateDescendantBlockW2_17 =
      (2520 : ℤ) • (1 : Matrix (Fin 80) (Fin 80) ℤ) := by
  apply Matrix.ext
  intro i j
  fin_cases i
  · exact certificateDescendantBlock2_17Check00_inverse 0 j
  · exact certificateDescendantBlock2_17Check00_inverse 1 j
  · exact certificateDescendantBlock2_17Check01_inverse 0 j
  · exact certificateDescendantBlock2_17Check01_inverse 1 j
  · exact certificateDescendantBlock2_17Check02_inverse 0 j
  · exact certificateDescendantBlock2_17Check02_inverse 1 j
  · exact certificateDescendantBlock2_17Check03_inverse 0 j
  · exact certificateDescendantBlock2_17Check03_inverse 1 j
  · exact certificateDescendantBlock2_17Check04_inverse 0 j
  · exact certificateDescendantBlock2_17Check04_inverse 1 j
  · exact certificateDescendantBlock2_17Check05_inverse 0 j
  · exact certificateDescendantBlock2_17Check05_inverse 1 j
  · exact certificateDescendantBlock2_17Check06_inverse 0 j
  · exact certificateDescendantBlock2_17Check06_inverse 1 j
  · exact certificateDescendantBlock2_17Check07_inverse 0 j
  · exact certificateDescendantBlock2_17Check07_inverse 1 j
  · exact certificateDescendantBlock2_17Check08_inverse 0 j
  · exact certificateDescendantBlock2_17Check08_inverse 1 j
  · exact certificateDescendantBlock2_17Check09_inverse 0 j
  · exact certificateDescendantBlock2_17Check09_inverse 1 j
  · exact certificateDescendantBlock2_17Check10_inverse 0 j
  · exact certificateDescendantBlock2_17Check10_inverse 1 j
  · exact certificateDescendantBlock2_17Check11_inverse 0 j
  · exact certificateDescendantBlock2_17Check11_inverse 1 j
  · exact certificateDescendantBlock2_17Check12_inverse 0 j
  · exact certificateDescendantBlock2_17Check12_inverse 1 j
  · exact certificateDescendantBlock2_17Check13_inverse 0 j
  · exact certificateDescendantBlock2_17Check13_inverse 1 j
  · exact certificateDescendantBlock2_17Check14_inverse 0 j
  · exact certificateDescendantBlock2_17Check14_inverse 1 j
  · exact certificateDescendantBlock2_17Check15_inverse 0 j
  · exact certificateDescendantBlock2_17Check15_inverse 1 j
  · exact certificateDescendantBlock2_17Check16_inverse 0 j
  · exact certificateDescendantBlock2_17Check16_inverse 1 j
  · exact certificateDescendantBlock2_17Check17_inverse 0 j
  · exact certificateDescendantBlock2_17Check17_inverse 1 j
  · exact certificateDescendantBlock2_17Check18_inverse 0 j
  · exact certificateDescendantBlock2_17Check18_inverse 1 j
  · exact certificateDescendantBlock2_17Check19_inverse 0 j
  · exact certificateDescendantBlock2_17Check19_inverse 1 j
  · exact certificateDescendantBlock2_17Check20_inverse 0 j
  · exact certificateDescendantBlock2_17Check20_inverse 1 j
  · exact certificateDescendantBlock2_17Check21_inverse 0 j
  · exact certificateDescendantBlock2_17Check21_inverse 1 j
  · exact certificateDescendantBlock2_17Check22_inverse 0 j
  · exact certificateDescendantBlock2_17Check22_inverse 1 j
  · exact certificateDescendantBlock2_17Check23_inverse 0 j
  · exact certificateDescendantBlock2_17Check23_inverse 1 j
  · exact certificateDescendantBlock2_17Check24_inverse 0 j
  · exact certificateDescendantBlock2_17Check24_inverse 1 j
  · exact certificateDescendantBlock2_17Check25_inverse 0 j
  · exact certificateDescendantBlock2_17Check25_inverse 1 j
  · exact certificateDescendantBlock2_17Check26_inverse 0 j
  · exact certificateDescendantBlock2_17Check26_inverse 1 j
  · exact certificateDescendantBlock2_17Check27_inverse 0 j
  · exact certificateDescendantBlock2_17Check27_inverse 1 j
  · exact certificateDescendantBlock2_17Check28_inverse 0 j
  · exact certificateDescendantBlock2_17Check28_inverse 1 j
  · exact certificateDescendantBlock2_17Check29_inverse 0 j
  · exact certificateDescendantBlock2_17Check29_inverse 1 j
  · exact certificateDescendantBlock2_17Check30_inverse 0 j
  · exact certificateDescendantBlock2_17Check30_inverse 1 j
  · exact certificateDescendantBlock2_17Check31_inverse 0 j
  · exact certificateDescendantBlock2_17Check31_inverse 1 j
  · exact certificateDescendantBlock2_17Check32_inverse 0 j
  · exact certificateDescendantBlock2_17Check32_inverse 1 j
  · exact certificateDescendantBlock2_17Check33_inverse 0 j
  · exact certificateDescendantBlock2_17Check33_inverse 1 j
  · exact certificateDescendantBlock2_17Check34_inverse 0 j
  · exact certificateDescendantBlock2_17Check34_inverse 1 j
  · exact certificateDescendantBlock2_17Check35_inverse 0 j
  · exact certificateDescendantBlock2_17Check35_inverse 1 j
  · exact certificateDescendantBlock2_17Check36_inverse 0 j
  · exact certificateDescendantBlock2_17Check36_inverse 1 j
  · exact certificateDescendantBlock2_17Check37_inverse 0 j
  · exact certificateDescendantBlock2_17Check37_inverse 1 j
  · exact certificateDescendantBlock2_17Check38_inverse 0 j
  · exact certificateDescendantBlock2_17Check38_inverse 1 j
  · exact certificateDescendantBlock2_17Check39_inverse 0 j
  · exact certificateDescendantBlock2_17Check39_inverse 1 j

theorem certificateDescendantBlock2_17_rows_injective :
    Function.Injective (certificateDescendantBlockRows2 17) := by
  decide +kernel

theorem certificateDescendantBlock2_17_row_weight (i : Fin 80) :
    (fun r => certificateLocalWeight {0} (certificateDescendantBlockRows2 17 i) r) =
      certificateDescendantWeights2 17 := by
  revert i
  decide +kernel

theorem certificateDescendantBlock2_17_column_weight (j : Fin 80) :
    List.Forall (fun a => (fun r => certificateLocalWeight {0} a.1 r) =
      certificateDescendantWeights2 17)
      (certificateDescendantColumns2 (certificateDescendantBlockColumns2 17 j)) := by
  revert j
  decide +kernel

theorem certificateDescendantBlock2_17_physical (i j : Fin 80) :
    certificateSparseVector
      (certificateDescendantColumns2 (certificateDescendantBlockColumns2 17 j))
      (certificateDescendantBlockRows2 17 i) = certificateDescendantBlockA2_17 i j := by
  fin_cases i
  · exact certificateDescendantBlock2_17Check00_physical 0 j
  · exact certificateDescendantBlock2_17Check00_physical 1 j
  · exact certificateDescendantBlock2_17Check01_physical 0 j
  · exact certificateDescendantBlock2_17Check01_physical 1 j
  · exact certificateDescendantBlock2_17Check02_physical 0 j
  · exact certificateDescendantBlock2_17Check02_physical 1 j
  · exact certificateDescendantBlock2_17Check03_physical 0 j
  · exact certificateDescendantBlock2_17Check03_physical 1 j
  · exact certificateDescendantBlock2_17Check04_physical 0 j
  · exact certificateDescendantBlock2_17Check04_physical 1 j
  · exact certificateDescendantBlock2_17Check05_physical 0 j
  · exact certificateDescendantBlock2_17Check05_physical 1 j
  · exact certificateDescendantBlock2_17Check06_physical 0 j
  · exact certificateDescendantBlock2_17Check06_physical 1 j
  · exact certificateDescendantBlock2_17Check07_physical 0 j
  · exact certificateDescendantBlock2_17Check07_physical 1 j
  · exact certificateDescendantBlock2_17Check08_physical 0 j
  · exact certificateDescendantBlock2_17Check08_physical 1 j
  · exact certificateDescendantBlock2_17Check09_physical 0 j
  · exact certificateDescendantBlock2_17Check09_physical 1 j
  · exact certificateDescendantBlock2_17Check10_physical 0 j
  · exact certificateDescendantBlock2_17Check10_physical 1 j
  · exact certificateDescendantBlock2_17Check11_physical 0 j
  · exact certificateDescendantBlock2_17Check11_physical 1 j
  · exact certificateDescendantBlock2_17Check12_physical 0 j
  · exact certificateDescendantBlock2_17Check12_physical 1 j
  · exact certificateDescendantBlock2_17Check13_physical 0 j
  · exact certificateDescendantBlock2_17Check13_physical 1 j
  · exact certificateDescendantBlock2_17Check14_physical 0 j
  · exact certificateDescendantBlock2_17Check14_physical 1 j
  · exact certificateDescendantBlock2_17Check15_physical 0 j
  · exact certificateDescendantBlock2_17Check15_physical 1 j
  · exact certificateDescendantBlock2_17Check16_physical 0 j
  · exact certificateDescendantBlock2_17Check16_physical 1 j
  · exact certificateDescendantBlock2_17Check17_physical 0 j
  · exact certificateDescendantBlock2_17Check17_physical 1 j
  · exact certificateDescendantBlock2_17Check18_physical 0 j
  · exact certificateDescendantBlock2_17Check18_physical 1 j
  · exact certificateDescendantBlock2_17Check19_physical 0 j
  · exact certificateDescendantBlock2_17Check19_physical 1 j
  · exact certificateDescendantBlock2_17Check20_physical 0 j
  · exact certificateDescendantBlock2_17Check20_physical 1 j
  · exact certificateDescendantBlock2_17Check21_physical 0 j
  · exact certificateDescendantBlock2_17Check21_physical 1 j
  · exact certificateDescendantBlock2_17Check22_physical 0 j
  · exact certificateDescendantBlock2_17Check22_physical 1 j
  · exact certificateDescendantBlock2_17Check23_physical 0 j
  · exact certificateDescendantBlock2_17Check23_physical 1 j
  · exact certificateDescendantBlock2_17Check24_physical 0 j
  · exact certificateDescendantBlock2_17Check24_physical 1 j
  · exact certificateDescendantBlock2_17Check25_physical 0 j
  · exact certificateDescendantBlock2_17Check25_physical 1 j
  · exact certificateDescendantBlock2_17Check26_physical 0 j
  · exact certificateDescendantBlock2_17Check26_physical 1 j
  · exact certificateDescendantBlock2_17Check27_physical 0 j
  · exact certificateDescendantBlock2_17Check27_physical 1 j
  · exact certificateDescendantBlock2_17Check28_physical 0 j
  · exact certificateDescendantBlock2_17Check28_physical 1 j
  · exact certificateDescendantBlock2_17Check29_physical 0 j
  · exact certificateDescendantBlock2_17Check29_physical 1 j
  · exact certificateDescendantBlock2_17Check30_physical 0 j
  · exact certificateDescendantBlock2_17Check30_physical 1 j
  · exact certificateDescendantBlock2_17Check31_physical 0 j
  · exact certificateDescendantBlock2_17Check31_physical 1 j
  · exact certificateDescendantBlock2_17Check32_physical 0 j
  · exact certificateDescendantBlock2_17Check32_physical 1 j
  · exact certificateDescendantBlock2_17Check33_physical 0 j
  · exact certificateDescendantBlock2_17Check33_physical 1 j
  · exact certificateDescendantBlock2_17Check34_physical 0 j
  · exact certificateDescendantBlock2_17Check34_physical 1 j
  · exact certificateDescendantBlock2_17Check35_physical 0 j
  · exact certificateDescendantBlock2_17Check35_physical 1 j
  · exact certificateDescendantBlock2_17Check36_physical 0 j
  · exact certificateDescendantBlock2_17Check36_physical 1 j
  · exact certificateDescendantBlock2_17Check37_physical 0 j
  · exact certificateDescendantBlock2_17Check37_physical 1 j
  · exact certificateDescendantBlock2_17Check38_physical 0 j
  · exact certificateDescendantBlock2_17Check38_physical 1 j
  · exact certificateDescendantBlock2_17Check39_physical 0 j
  · exact certificateDescendantBlock2_17Check39_physical 1 j

end ThreeCopyQutritWerner
