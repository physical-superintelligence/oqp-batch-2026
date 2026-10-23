module

public import ThreeCopyQutritWerner.CertificateHighestKernelData1_1

@[expose] public section


/-! Physical source binding and exact scaled kernel reconstruction.
These are ordinary kernel checks, not imported arithmetic assumptions. -/

set_option maxRecDepth 100000
set_option maxHeartbeats 100000000

open scoped BigOperators Matrix

namespace ThreeCopyQutritWerner

theorem certificateHighestKernel1_1Rows_injective : Function.Injective certificateHighestKernel1_1Rows := by
  decide

theorem certificateHighestKernel1_1Rows_weight : ∀ i,
    certificateLocalWeight {0, 1, 2} (certificateHighestKernel1_1Rows i) = certificateHighestKernel1_1Weight := by
  decide

/-- Every physical word of the specified weight is retained. -/
theorem certificateHighestKernel1_1Rows_cover : ∀ w : CertificateLocalWord,
    certificateLocalWeight {0, 1, 2} w = certificateHighestKernel1_1Weight → ∃ i, certificateHighestKernel1_1Rows i = w := by
  decide

theorem certificateHighestKernel1_1Pivots_bound (i : Fin 2) :
    certificateHighestKernel1_1Rows (certificateHighestKernel1_1Pivots i) = certificateLocalPivots1_1 i := by
  fin_cases i <;> decide

/-- U is the literal archive frame restricted to the exhaustive weight rows. -/
theorem certificateHighestKernel1_1U_bound :
    certificateLocalFrame1_1.submatrix certificateHighestKernel1_1Rows id = certificateHighestKernel1_1U := by
  ext i j
  fin_cases i <;> fin_cases j <;> decide

/-- Each selected equation is an actual output coordinate of E01 or E12. -/
theorem certificateHighestKernel1_1R_bound (a : Fin 1) (b : Fin 3) :
    certificateHighestKernel1_1R a b =
      (if (certificateHighestKernel1_1Tests a).1 = 0 then certificateLocalGenerator {0, 1, 2} 0 1
        else certificateLocalGenerator {0, 1, 2} 1 2) (certificateHighestKernel1_1Tests a).2 (certificateHighestKernel1_1Rows b) := by
  fin_cases a <;> fin_cases b <;> decide

theorem certificateHighestKernel1_1denominator_ne_zero : certificateHighestKernel1_1denominator ≠ 0 := by decide

/-- The full finite reconstruction is checked at every matrix entry. -/
theorem certificateHighestKernel1_1reconstruction :
    certificateHighestKernel1_1denominator • (1 - certificateHighestKernel1_1U * certificateHighestKernel1_1P) = certificateHighestKernel1_1W * certificateHighestKernel1_1R := by
  ext i j
  fin_cases i <;> fin_cases j <;> decide

end ThreeCopyQutritWerner
