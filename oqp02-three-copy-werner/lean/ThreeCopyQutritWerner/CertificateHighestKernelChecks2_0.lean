module

public import ThreeCopyQutritWerner.CertificateHighestKernelData2_0

@[expose] public section


/-! Physical source binding and exact scaled kernel reconstruction.
These are ordinary kernel checks, not imported arithmetic assumptions. -/

set_option maxRecDepth 100000
set_option maxHeartbeats 100000000

open scoped BigOperators Matrix

namespace ThreeCopyQutritWerner

theorem certificateHighestKernel2_0Rows_injective : Function.Injective certificateHighestKernel2_0Rows := by
  decide

theorem certificateHighestKernel2_0Rows_weight : ∀ i,
    certificateLocalWeight {0} (certificateHighestKernel2_0Rows i) = certificateHighestKernel2_0Weight := by
  decide

/-- Every physical word of the specified weight is retained. -/
theorem certificateHighestKernel2_0Rows_cover : ∀ w : CertificateLocalWord,
    certificateLocalWeight {0} w = certificateHighestKernel2_0Weight → ∃ i, certificateHighestKernel2_0Rows i = w := by
  decide

theorem certificateHighestKernel2_0Pivots_bound (i : Fin 1) :
    certificateHighestKernel2_0Rows (certificateHighestKernel2_0Pivots i) = certificateLocalPivots2_0 i := by
  fin_cases i <;> decide

/-- U is the literal archive frame restricted to the exhaustive weight rows. -/
theorem certificateHighestKernel2_0U_bound :
    certificateLocalFrame2_0.submatrix certificateHighestKernel2_0Rows id = certificateHighestKernel2_0U := by
  ext i j
  fin_cases i <;> fin_cases j <;> decide

/-- Each selected equation is an actual output coordinate of E01 or E12. -/
theorem certificateHighestKernel2_0R_bound (a : Fin 0) (b : Fin 1) :
    certificateHighestKernel2_0R a b =
      (if (certificateHighestKernel2_0Tests a).1 = 0 then certificateLocalGenerator {0} 0 1
        else certificateLocalGenerator {0} 1 2) (certificateHighestKernel2_0Tests a).2 (certificateHighestKernel2_0Rows b) := by
  fin_cases a <;> fin_cases b <;> decide

theorem certificateHighestKernel2_0denominator_ne_zero : certificateHighestKernel2_0denominator ≠ 0 := by decide

/-- The full finite reconstruction is checked at every matrix entry. -/
theorem certificateHighestKernel2_0reconstruction :
    certificateHighestKernel2_0denominator • (1 - certificateHighestKernel2_0U * certificateHighestKernel2_0P) = certificateHighestKernel2_0W * certificateHighestKernel2_0R := by
  ext i j
  fin_cases i <;> fin_cases j <;> decide

end ThreeCopyQutritWerner
