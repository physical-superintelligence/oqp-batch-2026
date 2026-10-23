module

public import ThreeCopyQutritWerner.CertificateDescendantBlock2_16BoundedData
public import ThreeCopyQutritWerner.CertificateDescendantBlock2_16Check00
public import ThreeCopyQutritWerner.CertificateDescendantBlock2_16Check01
public import ThreeCopyQutritWerner.CertificateDescendantBlock2_16Check02
public import ThreeCopyQutritWerner.CertificateDescendantBlock2_16Check03
public import ThreeCopyQutritWerner.CertificateDescendantBlock2_16Check04
public import ThreeCopyQutritWerner.CertificateDescendantBlock2_16Check05
public import ThreeCopyQutritWerner.CertificateDescendantBlock2_16Check06
public import ThreeCopyQutritWerner.CertificateDescendantBlock2_16Check07
public import ThreeCopyQutritWerner.CertificateDescendantBlock2_16Check08
public import ThreeCopyQutritWerner.CertificateDescendantBlock2_16Check09
public import ThreeCopyQutritWerner.CertificateDescendantBlock2_16Check10
public import ThreeCopyQutritWerner.CertificateDescendantBlock2_16Check11
public import ThreeCopyQutritWerner.CertificateDescendantBlock2_16Check12
public import ThreeCopyQutritWerner.CertificateDescendantBlock2_16Check13
public import ThreeCopyQutritWerner.CertificateDescendantBlock2_16Check14
public import ThreeCopyQutritWerner.CertificateDescendantBlock2_16Check15
public import ThreeCopyQutritWerner.CertificateDescendantBlock2_16Check16
public import ThreeCopyQutritWerner.CertificateDescendantBlock2_16Check17
public import ThreeCopyQutritWerner.CertificateDescendantBlock2_16Check18
public import ThreeCopyQutritWerner.CertificateDescendantBlock2_16Check19
public import ThreeCopyQutritWerner.CertificateDescendantBlock2_16Check20
public import ThreeCopyQutritWerner.CertificateDescendantBlock2_16Check21
public import ThreeCopyQutritWerner.CertificateDescendantBlock2_16Check22
public import ThreeCopyQutritWerner.CertificateDescendantBlock2_16Check23
public import ThreeCopyQutritWerner.CertificateDescendantBlock2_16Check24
public import ThreeCopyQutritWerner.CertificateDescendantBlock2_16Check25
public import ThreeCopyQutritWerner.CertificateDescendantBlock2_16Check26
public import ThreeCopyQutritWerner.CertificateDescendantBlock2_16Check27
public import ThreeCopyQutritWerner.CertificateDescendantBlock2_16Check28
public import ThreeCopyQutritWerner.CertificateDescendantBlock2_16Check29
public import ThreeCopyQutritWerner.CertificateDescendantBlock2_16Check30
public import ThreeCopyQutritWerner.CertificateDescendantBlock2_16Check31
public import ThreeCopyQutritWerner.CertificateDescendantBlock2_16Check32
public import ThreeCopyQutritWerner.CertificateDescendantBlock2_16Check33
public import ThreeCopyQutritWerner.CertificateDescendantBlock2_16Check34
public import ThreeCopyQutritWerner.CertificateDescendantBlock2_16Check35
public import ThreeCopyQutritWerner.CertificateDescendantBlock2_16Check36
public import ThreeCopyQutritWerner.CertificateDescendantBlock2_16Check37
public import ThreeCopyQutritWerner.CertificateDescendantBlock2_16Check38
public import ThreeCopyQutritWerner.CertificateDescendantBlock2_16Check39
public import ThreeCopyQutritWerner.CertificateMatrixLiteral
public import ThreeCopyQutritWerner.CertificateDescendantData

@[expose] public section


set_option maxRecDepth 100000
set_option maxHeartbeats 100000000

open scoped Matrix

namespace ThreeCopyQutritWerner

/-- Exact integer inverse certificate for signed physical weight [-1, -2, -1]. -/
theorem certificateDescendantBlock2_16_inverse :
    certificateDescendantBlockA2_16 * certificateDescendantBlockW2_16 =
      (5040 : ℤ) • (1 : Matrix (Fin 80) (Fin 80) ℤ) := by
  apply Matrix.ext
  intro i j
  fin_cases i
  · exact certificateDescendantBlock2_16Check00_inverse 0 j
  · exact certificateDescendantBlock2_16Check00_inverse 1 j
  · exact certificateDescendantBlock2_16Check01_inverse 0 j
  · exact certificateDescendantBlock2_16Check01_inverse 1 j
  · exact certificateDescendantBlock2_16Check02_inverse 0 j
  · exact certificateDescendantBlock2_16Check02_inverse 1 j
  · exact certificateDescendantBlock2_16Check03_inverse 0 j
  · exact certificateDescendantBlock2_16Check03_inverse 1 j
  · exact certificateDescendantBlock2_16Check04_inverse 0 j
  · exact certificateDescendantBlock2_16Check04_inverse 1 j
  · exact certificateDescendantBlock2_16Check05_inverse 0 j
  · exact certificateDescendantBlock2_16Check05_inverse 1 j
  · exact certificateDescendantBlock2_16Check06_inverse 0 j
  · exact certificateDescendantBlock2_16Check06_inverse 1 j
  · exact certificateDescendantBlock2_16Check07_inverse 0 j
  · exact certificateDescendantBlock2_16Check07_inverse 1 j
  · exact certificateDescendantBlock2_16Check08_inverse 0 j
  · exact certificateDescendantBlock2_16Check08_inverse 1 j
  · exact certificateDescendantBlock2_16Check09_inverse 0 j
  · exact certificateDescendantBlock2_16Check09_inverse 1 j
  · exact certificateDescendantBlock2_16Check10_inverse 0 j
  · exact certificateDescendantBlock2_16Check10_inverse 1 j
  · exact certificateDescendantBlock2_16Check11_inverse 0 j
  · exact certificateDescendantBlock2_16Check11_inverse 1 j
  · exact certificateDescendantBlock2_16Check12_inverse 0 j
  · exact certificateDescendantBlock2_16Check12_inverse 1 j
  · exact certificateDescendantBlock2_16Check13_inverse 0 j
  · exact certificateDescendantBlock2_16Check13_inverse 1 j
  · exact certificateDescendantBlock2_16Check14_inverse 0 j
  · exact certificateDescendantBlock2_16Check14_inverse 1 j
  · exact certificateDescendantBlock2_16Check15_inverse 0 j
  · exact certificateDescendantBlock2_16Check15_inverse 1 j
  · exact certificateDescendantBlock2_16Check16_inverse 0 j
  · exact certificateDescendantBlock2_16Check16_inverse 1 j
  · exact certificateDescendantBlock2_16Check17_inverse 0 j
  · exact certificateDescendantBlock2_16Check17_inverse 1 j
  · exact certificateDescendantBlock2_16Check18_inverse 0 j
  · exact certificateDescendantBlock2_16Check18_inverse 1 j
  · exact certificateDescendantBlock2_16Check19_inverse 0 j
  · exact certificateDescendantBlock2_16Check19_inverse 1 j
  · exact certificateDescendantBlock2_16Check20_inverse 0 j
  · exact certificateDescendantBlock2_16Check20_inverse 1 j
  · exact certificateDescendantBlock2_16Check21_inverse 0 j
  · exact certificateDescendantBlock2_16Check21_inverse 1 j
  · exact certificateDescendantBlock2_16Check22_inverse 0 j
  · exact certificateDescendantBlock2_16Check22_inverse 1 j
  · exact certificateDescendantBlock2_16Check23_inverse 0 j
  · exact certificateDescendantBlock2_16Check23_inverse 1 j
  · exact certificateDescendantBlock2_16Check24_inverse 0 j
  · exact certificateDescendantBlock2_16Check24_inverse 1 j
  · exact certificateDescendantBlock2_16Check25_inverse 0 j
  · exact certificateDescendantBlock2_16Check25_inverse 1 j
  · exact certificateDescendantBlock2_16Check26_inverse 0 j
  · exact certificateDescendantBlock2_16Check26_inverse 1 j
  · exact certificateDescendantBlock2_16Check27_inverse 0 j
  · exact certificateDescendantBlock2_16Check27_inverse 1 j
  · exact certificateDescendantBlock2_16Check28_inverse 0 j
  · exact certificateDescendantBlock2_16Check28_inverse 1 j
  · exact certificateDescendantBlock2_16Check29_inverse 0 j
  · exact certificateDescendantBlock2_16Check29_inverse 1 j
  · exact certificateDescendantBlock2_16Check30_inverse 0 j
  · exact certificateDescendantBlock2_16Check30_inverse 1 j
  · exact certificateDescendantBlock2_16Check31_inverse 0 j
  · exact certificateDescendantBlock2_16Check31_inverse 1 j
  · exact certificateDescendantBlock2_16Check32_inverse 0 j
  · exact certificateDescendantBlock2_16Check32_inverse 1 j
  · exact certificateDescendantBlock2_16Check33_inverse 0 j
  · exact certificateDescendantBlock2_16Check33_inverse 1 j
  · exact certificateDescendantBlock2_16Check34_inverse 0 j
  · exact certificateDescendantBlock2_16Check34_inverse 1 j
  · exact certificateDescendantBlock2_16Check35_inverse 0 j
  · exact certificateDescendantBlock2_16Check35_inverse 1 j
  · exact certificateDescendantBlock2_16Check36_inverse 0 j
  · exact certificateDescendantBlock2_16Check36_inverse 1 j
  · exact certificateDescendantBlock2_16Check37_inverse 0 j
  · exact certificateDescendantBlock2_16Check37_inverse 1 j
  · exact certificateDescendantBlock2_16Check38_inverse 0 j
  · exact certificateDescendantBlock2_16Check38_inverse 1 j
  · exact certificateDescendantBlock2_16Check39_inverse 0 j
  · exact certificateDescendantBlock2_16Check39_inverse 1 j

theorem certificateDescendantBlock2_16_rows_injective :
    Function.Injective (certificateDescendantBlockRows2 16) := by
  decide +kernel

theorem certificateDescendantBlock2_16_row_weight (i : Fin 80) :
    (fun r => certificateLocalWeight {0} (certificateDescendantBlockRows2 16 i) r) =
      certificateDescendantWeights2 16 := by
  revert i
  decide +kernel

theorem certificateDescendantBlock2_16_column_weight (j : Fin 80) :
    List.Forall (fun a => (fun r => certificateLocalWeight {0} a.1 r) =
      certificateDescendantWeights2 16)
      (certificateDescendantColumns2 (certificateDescendantBlockColumns2 16 j)) := by
  revert j
  decide +kernel

theorem certificateDescendantBlock2_16_physical (i j : Fin 80) :
    certificateSparseVector
      (certificateDescendantColumns2 (certificateDescendantBlockColumns2 16 j))
      (certificateDescendantBlockRows2 16 i) = certificateDescendantBlockA2_16 i j := by
  fin_cases i
  · exact certificateDescendantBlock2_16Check00_physical 0 j
  · exact certificateDescendantBlock2_16Check00_physical 1 j
  · exact certificateDescendantBlock2_16Check01_physical 0 j
  · exact certificateDescendantBlock2_16Check01_physical 1 j
  · exact certificateDescendantBlock2_16Check02_physical 0 j
  · exact certificateDescendantBlock2_16Check02_physical 1 j
  · exact certificateDescendantBlock2_16Check03_physical 0 j
  · exact certificateDescendantBlock2_16Check03_physical 1 j
  · exact certificateDescendantBlock2_16Check04_physical 0 j
  · exact certificateDescendantBlock2_16Check04_physical 1 j
  · exact certificateDescendantBlock2_16Check05_physical 0 j
  · exact certificateDescendantBlock2_16Check05_physical 1 j
  · exact certificateDescendantBlock2_16Check06_physical 0 j
  · exact certificateDescendantBlock2_16Check06_physical 1 j
  · exact certificateDescendantBlock2_16Check07_physical 0 j
  · exact certificateDescendantBlock2_16Check07_physical 1 j
  · exact certificateDescendantBlock2_16Check08_physical 0 j
  · exact certificateDescendantBlock2_16Check08_physical 1 j
  · exact certificateDescendantBlock2_16Check09_physical 0 j
  · exact certificateDescendantBlock2_16Check09_physical 1 j
  · exact certificateDescendantBlock2_16Check10_physical 0 j
  · exact certificateDescendantBlock2_16Check10_physical 1 j
  · exact certificateDescendantBlock2_16Check11_physical 0 j
  · exact certificateDescendantBlock2_16Check11_physical 1 j
  · exact certificateDescendantBlock2_16Check12_physical 0 j
  · exact certificateDescendantBlock2_16Check12_physical 1 j
  · exact certificateDescendantBlock2_16Check13_physical 0 j
  · exact certificateDescendantBlock2_16Check13_physical 1 j
  · exact certificateDescendantBlock2_16Check14_physical 0 j
  · exact certificateDescendantBlock2_16Check14_physical 1 j
  · exact certificateDescendantBlock2_16Check15_physical 0 j
  · exact certificateDescendantBlock2_16Check15_physical 1 j
  · exact certificateDescendantBlock2_16Check16_physical 0 j
  · exact certificateDescendantBlock2_16Check16_physical 1 j
  · exact certificateDescendantBlock2_16Check17_physical 0 j
  · exact certificateDescendantBlock2_16Check17_physical 1 j
  · exact certificateDescendantBlock2_16Check18_physical 0 j
  · exact certificateDescendantBlock2_16Check18_physical 1 j
  · exact certificateDescendantBlock2_16Check19_physical 0 j
  · exact certificateDescendantBlock2_16Check19_physical 1 j
  · exact certificateDescendantBlock2_16Check20_physical 0 j
  · exact certificateDescendantBlock2_16Check20_physical 1 j
  · exact certificateDescendantBlock2_16Check21_physical 0 j
  · exact certificateDescendantBlock2_16Check21_physical 1 j
  · exact certificateDescendantBlock2_16Check22_physical 0 j
  · exact certificateDescendantBlock2_16Check22_physical 1 j
  · exact certificateDescendantBlock2_16Check23_physical 0 j
  · exact certificateDescendantBlock2_16Check23_physical 1 j
  · exact certificateDescendantBlock2_16Check24_physical 0 j
  · exact certificateDescendantBlock2_16Check24_physical 1 j
  · exact certificateDescendantBlock2_16Check25_physical 0 j
  · exact certificateDescendantBlock2_16Check25_physical 1 j
  · exact certificateDescendantBlock2_16Check26_physical 0 j
  · exact certificateDescendantBlock2_16Check26_physical 1 j
  · exact certificateDescendantBlock2_16Check27_physical 0 j
  · exact certificateDescendantBlock2_16Check27_physical 1 j
  · exact certificateDescendantBlock2_16Check28_physical 0 j
  · exact certificateDescendantBlock2_16Check28_physical 1 j
  · exact certificateDescendantBlock2_16Check29_physical 0 j
  · exact certificateDescendantBlock2_16Check29_physical 1 j
  · exact certificateDescendantBlock2_16Check30_physical 0 j
  · exact certificateDescendantBlock2_16Check30_physical 1 j
  · exact certificateDescendantBlock2_16Check31_physical 0 j
  · exact certificateDescendantBlock2_16Check31_physical 1 j
  · exact certificateDescendantBlock2_16Check32_physical 0 j
  · exact certificateDescendantBlock2_16Check32_physical 1 j
  · exact certificateDescendantBlock2_16Check33_physical 0 j
  · exact certificateDescendantBlock2_16Check33_physical 1 j
  · exact certificateDescendantBlock2_16Check34_physical 0 j
  · exact certificateDescendantBlock2_16Check34_physical 1 j
  · exact certificateDescendantBlock2_16Check35_physical 0 j
  · exact certificateDescendantBlock2_16Check35_physical 1 j
  · exact certificateDescendantBlock2_16Check36_physical 0 j
  · exact certificateDescendantBlock2_16Check36_physical 1 j
  · exact certificateDescendantBlock2_16Check37_physical 0 j
  · exact certificateDescendantBlock2_16Check37_physical 1 j
  · exact certificateDescendantBlock2_16Check38_physical 0 j
  · exact certificateDescendantBlock2_16Check38_physical 1 j
  · exact certificateDescendantBlock2_16Check39_physical 0 j
  · exact certificateDescendantBlock2_16Check39_physical 1 j

end ThreeCopyQutritWerner
