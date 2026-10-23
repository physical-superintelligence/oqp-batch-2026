module

public import ThreeCopyQutritWerner.CertificateHighestKernelData1_4

@[expose] public section


/-! Physical source binding and exact scaled kernel reconstruction.
These are ordinary kernel checks, not imported arithmetic assumptions. -/

set_option maxRecDepth 100000
set_option maxHeartbeats 100000000

open scoped BigOperators Matrix

namespace ThreeCopyQutritWerner

theorem certificateHighestKernel1_4Rows_injective : Function.Injective certificateHighestKernel1_4Rows := by
  decide

theorem certificateHighestKernel1_4Rows_weight : ∀ i,
    certificateLocalWeight {0, 1, 2} (certificateHighestKernel1_4Rows i) = certificateHighestKernel1_4Weight := by
  decide

/-- Every physical word of the specified weight is retained. -/
theorem certificateHighestKernel1_4Rows_cover : ∀ w : CertificateLocalWord,
    certificateLocalWeight {0, 1, 2} w = certificateHighestKernel1_4Weight → ∃ i, certificateHighestKernel1_4Rows i = w := by
  decide

theorem certificateHighestKernel1_4Pivots_bound (i : Fin 7) :
    certificateHighestKernel1_4Rows (certificateHighestKernel1_4Pivots i) = certificateLocalPivots1_4 i := by
  fin_cases i <;> decide

/-- U is the literal archive frame restricted to the exhaustive weight rows. -/
theorem certificateHighestKernel1_4U_bound :
    certificateLocalFrame1_4.submatrix certificateHighestKernel1_4Rows id = certificateHighestKernel1_4U := by
  ext i j
  fin_cases i <;> fin_cases j <;> decide

/-- Each selected equation is an actual output coordinate of E01 or E12. -/
theorem certificateHighestKernel1_4R_bound (a : Fin 17) (b : Fin 24) :
    certificateHighestKernel1_4R a b =
      (if (certificateHighestKernel1_4Tests a).1 = 0 then certificateLocalGenerator {0, 1, 2} 0 1
        else certificateLocalGenerator {0, 1, 2} 1 2) (certificateHighestKernel1_4Tests a).2 (certificateHighestKernel1_4Rows b) := by
  fin_cases a <;> fin_cases b <;> decide

theorem certificateHighestKernel1_4denominator_ne_zero : certificateHighestKernel1_4denominator ≠ 0 := by decide

/-- The full finite reconstruction is checked at every matrix entry. -/
theorem certificateHighestKernel1_4reconstruction :
    certificateHighestKernel1_4denominator • (1 - certificateHighestKernel1_4U * certificateHighestKernel1_4P) = certificateHighestKernel1_4W * certificateHighestKernel1_4R := by
  ext i j
  fin_cases i <;> fin_cases j <;> decide

end ThreeCopyQutritWerner
