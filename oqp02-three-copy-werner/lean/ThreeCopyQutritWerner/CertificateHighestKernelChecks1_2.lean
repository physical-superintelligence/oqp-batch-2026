module

public import ThreeCopyQutritWerner.CertificateHighestKernelData1_2

@[expose] public section


/-! Physical source binding and exact scaled kernel reconstruction.
These are ordinary kernel checks, not imported arithmetic assumptions. -/

set_option maxRecDepth 100000
set_option maxHeartbeats 100000000

open scoped BigOperators Matrix

namespace ThreeCopyQutritWerner

theorem certificateHighestKernel1_2Rows_injective : Function.Injective certificateHighestKernel1_2Rows := by
  decide

theorem certificateHighestKernel1_2Rows_weight : ∀ i,
    certificateLocalWeight {0, 1, 2} (certificateHighestKernel1_2Rows i) = certificateHighestKernel1_2Weight := by
  decide

/-- Every physical word of the specified weight is retained. -/
theorem certificateHighestKernel1_2Rows_cover : ∀ w : CertificateLocalWord,
    certificateLocalWeight {0, 1, 2} w = certificateHighestKernel1_2Weight → ∃ i, certificateHighestKernel1_2Rows i = w := by
  decide

theorem certificateHighestKernel1_2Pivots_bound (i : Fin 2) :
    certificateHighestKernel1_2Rows (certificateHighestKernel1_2Pivots i) = certificateLocalPivots1_2 i := by
  fin_cases i <;> decide

/-- U is the literal archive frame restricted to the exhaustive weight rows. -/
theorem certificateHighestKernel1_2U_bound :
    certificateLocalFrame1_2.submatrix certificateHighestKernel1_2Rows id = certificateHighestKernel1_2U := by
  ext i j
  fin_cases i <;> fin_cases j <;> decide

/-- Each selected equation is an actual output coordinate of E01 or E12. -/
theorem certificateHighestKernel1_2R_bound (a : Fin 1) (b : Fin 3) :
    certificateHighestKernel1_2R a b =
      (if (certificateHighestKernel1_2Tests a).1 = 0 then certificateLocalGenerator {0, 1, 2} 0 1
        else certificateLocalGenerator {0, 1, 2} 1 2) (certificateHighestKernel1_2Tests a).2 (certificateHighestKernel1_2Rows b) := by
  fin_cases a <;> fin_cases b <;> decide

theorem certificateHighestKernel1_2denominator_ne_zero : certificateHighestKernel1_2denominator ≠ 0 := by decide

/-- The full finite reconstruction is checked at every matrix entry. -/
theorem certificateHighestKernel1_2reconstruction :
    certificateHighestKernel1_2denominator • (1 - certificateHighestKernel1_2U * certificateHighestKernel1_2P) = certificateHighestKernel1_2W * certificateHighestKernel1_2R := by
  ext i j
  fin_cases i <;> fin_cases j <;> decide

end ThreeCopyQutritWerner
