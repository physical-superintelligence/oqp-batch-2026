module

public import ThreeCopyQutritWerner.CertificateHighestKernelData2_1

@[expose] public section


/-! Physical source binding and exact scaled kernel reconstruction.
These are ordinary kernel checks, not imported arithmetic assumptions. -/

set_option maxRecDepth 100000
set_option maxHeartbeats 100000000

open scoped BigOperators Matrix

namespace ThreeCopyQutritWerner

theorem certificateHighestKernel2_1Rows_injective : Function.Injective certificateHighestKernel2_1Rows := by
  decide

theorem certificateHighestKernel2_1Rows_weight : ∀ i,
    certificateLocalWeight {0} (certificateHighestKernel2_1Rows i) = certificateHighestKernel2_1Weight := by
  decide

/-- Every physical word of the specified weight is retained. -/
theorem certificateHighestKernel2_1Rows_cover : ∀ w : CertificateLocalWord,
    certificateLocalWeight {0} w = certificateHighestKernel2_1Weight → ∃ i, certificateHighestKernel2_1Rows i = w := by
  decide

theorem certificateHighestKernel2_1Pivots_bound (i : Fin 4) :
    certificateHighestKernel2_1Rows (certificateHighestKernel2_1Pivots i) = certificateLocalPivots2_1 i := by
  fin_cases i <;> decide

/-- U is the literal archive frame restricted to the exhaustive weight rows. -/
theorem certificateHighestKernel2_1U_bound :
    certificateLocalFrame2_1.submatrix certificateHighestKernel2_1Rows id = certificateHighestKernel2_1U := by
  ext i j
  fin_cases i <;> fin_cases j <;> decide

/-- Each selected equation is an actual output coordinate of E01 or E12. -/
theorem certificateHighestKernel2_1R_bound (a : Fin 1) (b : Fin 5) :
    certificateHighestKernel2_1R a b =
      (if (certificateHighestKernel2_1Tests a).1 = 0 then certificateLocalGenerator {0} 0 1
        else certificateLocalGenerator {0} 1 2) (certificateHighestKernel2_1Tests a).2 (certificateHighestKernel2_1Rows b) := by
  fin_cases a <;> fin_cases b <;> decide

theorem certificateHighestKernel2_1denominator_ne_zero : certificateHighestKernel2_1denominator ≠ 0 := by decide

/-- The full finite reconstruction is checked at every matrix entry. -/
theorem certificateHighestKernel2_1reconstruction :
    certificateHighestKernel2_1denominator • (1 - certificateHighestKernel2_1U * certificateHighestKernel2_1P) = certificateHighestKernel2_1W * certificateHighestKernel2_1R := by
  ext i j
  fin_cases i <;> fin_cases j <;> decide

end ThreeCopyQutritWerner
