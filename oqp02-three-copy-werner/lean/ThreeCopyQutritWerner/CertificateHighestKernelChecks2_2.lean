module

public import ThreeCopyQutritWerner.CertificateHighestKernelData2_2

@[expose] public section


/-! Physical source binding and exact scaled kernel reconstruction.
These are ordinary kernel checks, not imported arithmetic assumptions. -/

set_option maxRecDepth 100000
set_option maxHeartbeats 100000000

open scoped BigOperators Matrix

namespace ThreeCopyQutritWerner

theorem certificateHighestKernel2_2Rows_injective : Function.Injective certificateHighestKernel2_2Rows := by
  decide

theorem certificateHighestKernel2_2Rows_weight : ∀ i,
    certificateLocalWeight {0} (certificateHighestKernel2_2Rows i) = certificateHighestKernel2_2Weight := by
  decide

/-- Every physical word of the specified weight is retained. -/
theorem certificateHighestKernel2_2Rows_cover : ∀ w : CertificateLocalWord,
    certificateLocalWeight {0} w = certificateHighestKernel2_2Weight → ∃ i, certificateHighestKernel2_2Rows i = w := by
  decide

theorem certificateHighestKernel2_2Pivots_bound (i : Fin 5) :
    certificateHighestKernel2_2Rows (certificateHighestKernel2_2Pivots i) = certificateLocalPivots2_2 i := by
  fin_cases i <;> decide

/-- U is the literal archive frame restricted to the exhaustive weight rows. -/
theorem certificateHighestKernel2_2U_bound :
    certificateLocalFrame2_2.submatrix certificateHighestKernel2_2Rows id = certificateHighestKernel2_2U := by
  ext i j
  fin_cases i <;> fin_cases j <;> decide

/-- Each selected equation is an actual output coordinate of E01 or E12. -/
theorem certificateHighestKernel2_2R_bound (a : Fin 6) (b : Fin 11) :
    certificateHighestKernel2_2R a b =
      (if (certificateHighestKernel2_2Tests a).1 = 0 then certificateLocalGenerator {0} 0 1
        else certificateLocalGenerator {0} 1 2) (certificateHighestKernel2_2Tests a).2 (certificateHighestKernel2_2Rows b) := by
  fin_cases a <;> fin_cases b <;> decide

theorem certificateHighestKernel2_2denominator_ne_zero : certificateHighestKernel2_2denominator ≠ 0 := by decide

/-- The full finite reconstruction is checked at every matrix entry. -/
theorem certificateHighestKernel2_2reconstruction :
    certificateHighestKernel2_2denominator • (1 - certificateHighestKernel2_2U * certificateHighestKernel2_2P) = certificateHighestKernel2_2W * certificateHighestKernel2_2R := by
  ext i j
  fin_cases i <;> fin_cases j <;> decide

end ThreeCopyQutritWerner
