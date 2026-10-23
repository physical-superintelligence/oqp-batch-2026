module

public import ThreeCopyQutritWerner.CertificateHighestKernelData1_0

@[expose] public section


/-! Physical source binding and exact scaled kernel reconstruction.
These are ordinary kernel checks, not imported arithmetic assumptions. -/

set_option maxRecDepth 100000
set_option maxHeartbeats 100000000

open scoped BigOperators Matrix

namespace ThreeCopyQutritWerner

theorem certificateHighestKernel1_0Rows_injective : Function.Injective certificateHighestKernel1_0Rows := by
  decide

theorem certificateHighestKernel1_0Rows_weight : ∀ i,
    certificateLocalWeight {0, 1, 2} (certificateHighestKernel1_0Rows i) = certificateHighestKernel1_0Weight := by
  decide

/-- Every physical word of the specified weight is retained. -/
theorem certificateHighestKernel1_0Rows_cover : ∀ w : CertificateLocalWord,
    certificateLocalWeight {0, 1, 2} w = certificateHighestKernel1_0Weight → ∃ i, certificateHighestKernel1_0Rows i = w := by
  decide

theorem certificateHighestKernel1_0Pivots_bound (i : Fin 1) :
    certificateHighestKernel1_0Rows (certificateHighestKernel1_0Pivots i) = certificateLocalPivots1_0 i := by
  fin_cases i <;> decide

/-- U is the literal archive frame restricted to the exhaustive weight rows. -/
theorem certificateHighestKernel1_0U_bound :
    certificateLocalFrame1_0.submatrix certificateHighestKernel1_0Rows id = certificateHighestKernel1_0U := by
  ext i j
  fin_cases i <;> fin_cases j <;> decide

/-- Each selected equation is an actual output coordinate of E01 or E12. -/
theorem certificateHighestKernel1_0R_bound (a : Fin 0) (b : Fin 1) :
    certificateHighestKernel1_0R a b =
      (if (certificateHighestKernel1_0Tests a).1 = 0 then certificateLocalGenerator {0, 1, 2} 0 1
        else certificateLocalGenerator {0, 1, 2} 1 2) (certificateHighestKernel1_0Tests a).2 (certificateHighestKernel1_0Rows b) := by
  fin_cases a <;> fin_cases b <;> decide

theorem certificateHighestKernel1_0denominator_ne_zero : certificateHighestKernel1_0denominator ≠ 0 := by decide

/-- The full finite reconstruction is checked at every matrix entry. -/
theorem certificateHighestKernel1_0reconstruction :
    certificateHighestKernel1_0denominator • (1 - certificateHighestKernel1_0U * certificateHighestKernel1_0P) = certificateHighestKernel1_0W * certificateHighestKernel1_0R := by
  ext i j
  fin_cases i <;> fin_cases j <;> decide

end ThreeCopyQutritWerner
