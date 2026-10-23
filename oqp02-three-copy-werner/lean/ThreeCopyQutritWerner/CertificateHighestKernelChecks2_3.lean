module

public import ThreeCopyQutritWerner.CertificateHighestKernelData2_3

@[expose] public section


/-! Physical source binding and exact scaled kernel reconstruction.
These are ordinary kernel checks, not imported arithmetic assumptions. -/

set_option maxRecDepth 100000
set_option maxHeartbeats 100000000

open scoped BigOperators Matrix

namespace ThreeCopyQutritWerner

theorem certificateHighestKernel2_3Rows_injective : Function.Injective certificateHighestKernel2_3Rows := by
  decide

theorem certificateHighestKernel2_3Rows_weight : ∀ i,
    certificateLocalWeight {0} (certificateHighestKernel2_3Rows i) = certificateHighestKernel2_3Weight := by
  decide

/-- Every physical word of the specified weight is retained. -/
theorem certificateHighestKernel2_3Rows_cover : ∀ w : CertificateLocalWord,
    certificateLocalWeight {0} w = certificateHighestKernel2_3Weight → ∃ i, certificateHighestKernel2_3Rows i = w := by
  decide

theorem certificateHighestKernel2_3Pivots_bound (i : Fin 5) :
    certificateHighestKernel2_3Rows (certificateHighestKernel2_3Pivots i) = certificateLocalPivots2_3 i := by
  fin_cases i <;> decide

/-- U is the literal archive frame restricted to the exhaustive weight rows. -/
theorem certificateHighestKernel2_3U_bound :
    certificateLocalFrame2_3.submatrix certificateHighestKernel2_3Rows id = certificateHighestKernel2_3U := by
  ext i j
  fin_cases i <;> fin_cases j <;> decide

/-- Each selected equation is an actual output coordinate of E01 or E12. -/
theorem certificateHighestKernel2_3R_bound (a : Fin 5) (b : Fin 10) :
    certificateHighestKernel2_3R a b =
      (if (certificateHighestKernel2_3Tests a).1 = 0 then certificateLocalGenerator {0} 0 1
        else certificateLocalGenerator {0} 1 2) (certificateHighestKernel2_3Tests a).2 (certificateHighestKernel2_3Rows b) := by
  fin_cases a <;> fin_cases b <;> decide

theorem certificateHighestKernel2_3denominator_ne_zero : certificateHighestKernel2_3denominator ≠ 0 := by decide

/-- The full finite reconstruction is checked at every matrix entry. -/
theorem certificateHighestKernel2_3reconstruction :
    certificateHighestKernel2_3denominator • (1 - certificateHighestKernel2_3U * certificateHighestKernel2_3P) = certificateHighestKernel2_3W * certificateHighestKernel2_3R := by
  ext i j
  fin_cases i <;> fin_cases j <;> decide

end ThreeCopyQutritWerner
