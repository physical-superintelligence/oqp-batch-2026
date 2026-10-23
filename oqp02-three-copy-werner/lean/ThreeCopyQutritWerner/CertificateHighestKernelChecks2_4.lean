module

public import ThreeCopyQutritWerner.CertificateHighestKernelData2_4

@[expose] public section


/-! Physical source binding and exact scaled kernel reconstruction.
These are ordinary kernel checks, not imported arithmetic assumptions. -/

set_option maxRecDepth 100000
set_option maxHeartbeats 100000000

open scoped BigOperators Matrix

namespace ThreeCopyQutritWerner

theorem certificateHighestKernel2_4Rows_injective : Function.Injective certificateHighestKernel2_4Rows := by
  decide

theorem certificateHighestKernel2_4Rows_weight : ∀ i,
    certificateLocalWeight {0} (certificateHighestKernel2_4Rows i) = certificateHighestKernel2_4Weight := by
  decide

/-- Every physical word of the specified weight is retained. -/
theorem certificateHighestKernel2_4Rows_cover : ∀ w : CertificateLocalWord,
    certificateLocalWeight {0} w = certificateHighestKernel2_4Weight → ∃ i, certificateHighestKernel2_4Rows i = w := by
  decide

theorem certificateHighestKernel2_4Pivots_bound (i : Fin 15) :
    certificateHighestKernel2_4Rows (certificateHighestKernel2_4Pivots i) = certificateLocalPivots2_4 i := by
  fin_cases i <;> decide

/-- U is the literal archive frame restricted to the exhaustive weight rows. -/
theorem certificateHighestKernel2_4U_bound :
    certificateLocalFrame2_4.submatrix certificateHighestKernel2_4Rows id = certificateHighestKernel2_4U := by
  ext i j
  fin_cases i <;> fin_cases j <;> decide

/-- Each selected equation is an actual output coordinate of E01 or E12. -/
theorem certificateHighestKernel2_4R_bound (a : Fin 20) (b : Fin 35) :
    certificateHighestKernel2_4R a b =
      (if (certificateHighestKernel2_4Tests a).1 = 0 then certificateLocalGenerator {0} 0 1
        else certificateLocalGenerator {0} 1 2) (certificateHighestKernel2_4Tests a).2 (certificateHighestKernel2_4Rows b) := by
  fin_cases a <;> fin_cases b <;> decide

theorem certificateHighestKernel2_4denominator_ne_zero : certificateHighestKernel2_4denominator ≠ 0 := by decide

/-- The full finite reconstruction is checked at every matrix entry. -/
theorem certificateHighestKernel2_4reconstruction :
    certificateHighestKernel2_4denominator • (1 - certificateHighestKernel2_4U * certificateHighestKernel2_4P) = certificateHighestKernel2_4W * certificateHighestKernel2_4R := by
  ext i j
  fin_cases i <;> fin_cases j <;> decide

end ThreeCopyQutritWerner
