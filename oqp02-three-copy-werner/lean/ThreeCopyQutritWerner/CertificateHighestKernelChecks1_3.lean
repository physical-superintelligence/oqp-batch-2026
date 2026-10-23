module

public import ThreeCopyQutritWerner.CertificateHighestKernelData1_3

@[expose] public section


/-! Physical source binding and exact scaled kernel reconstruction.
These are ordinary kernel checks, not imported arithmetic assumptions. -/

set_option maxRecDepth 100000
set_option maxHeartbeats 100000000

open scoped BigOperators Matrix

namespace ThreeCopyQutritWerner

theorem certificateHighestKernel1_3Rows_injective : Function.Injective certificateHighestKernel1_3Rows := by
  decide

theorem certificateHighestKernel1_3Rows_weight : ∀ i,
    certificateLocalWeight {0, 1, 2} (certificateHighestKernel1_3Rows i) = certificateHighestKernel1_3Weight := by
  decide

/-- Every physical word of the specified weight is retained. -/
theorem certificateHighestKernel1_3Rows_cover : ∀ w : CertificateLocalWord,
    certificateLocalWeight {0, 1, 2} w = certificateHighestKernel1_3Weight → ∃ i, certificateHighestKernel1_3Rows i = w := by
  decide

theorem certificateHighestKernel1_3Pivots_bound (i : Fin 9) :
    certificateHighestKernel1_3Rows (certificateHighestKernel1_3Pivots i) = certificateLocalPivots1_3 i := by
  fin_cases i <;> decide

/-- U is the literal archive frame restricted to the exhaustive weight rows. -/
theorem certificateHighestKernel1_3U_bound :
    certificateLocalFrame1_3.submatrix certificateHighestKernel1_3Rows id = certificateHighestKernel1_3U := by
  ext i j
  fin_cases i <;> fin_cases j <;> decide

/-- Each selected equation is an actual output coordinate of E01 or E12. -/
theorem certificateHighestKernel1_3R_bound (a : Fin 6) (b : Fin 15) :
    certificateHighestKernel1_3R a b =
      (if (certificateHighestKernel1_3Tests a).1 = 0 then certificateLocalGenerator {0, 1, 2} 0 1
        else certificateLocalGenerator {0, 1, 2} 1 2) (certificateHighestKernel1_3Tests a).2 (certificateHighestKernel1_3Rows b) := by
  fin_cases a <;> fin_cases b <;> decide

theorem certificateHighestKernel1_3denominator_ne_zero : certificateHighestKernel1_3denominator ≠ 0 := by decide

/-- The full finite reconstruction is checked at every matrix entry. -/
theorem certificateHighestKernel1_3reconstruction :
    certificateHighestKernel1_3denominator • (1 - certificateHighestKernel1_3U * certificateHighestKernel1_3P) = certificateHighestKernel1_3W * certificateHighestKernel1_3R := by
  ext i j
  fin_cases i <;> fin_cases j <;> decide

end ThreeCopyQutritWerner
