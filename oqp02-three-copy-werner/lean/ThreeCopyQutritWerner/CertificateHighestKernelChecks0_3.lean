module

public import ThreeCopyQutritWerner.CertificateHighestKernelData0_3

@[expose] public section


/-! Physical source binding and exact scaled kernel reconstruction.
These are ordinary kernel checks, not imported arithmetic assumptions. -/

set_option maxRecDepth 100000
set_option maxHeartbeats 100000000

open scoped BigOperators Matrix

namespace ThreeCopyQutritWerner

theorem certificateHighestKernel0_3Rows_injective : Function.Injective certificateHighestKernel0_3Rows := by
  decide

theorem certificateHighestKernel0_3Rows_weight : ∀ i,
    certificateLocalWeight {5} (certificateHighestKernel0_3Rows i) = certificateHighestKernel0_3Weight := by
  decide

/-- Every physical word of the specified weight is retained. -/
theorem certificateHighestKernel0_3Rows_cover : ∀ w : CertificateLocalWord,
    certificateLocalWeight {5} w = certificateHighestKernel0_3Weight → ∃ i, certificateHighestKernel0_3Rows i = w := by
  decide

theorem certificateHighestKernel0_3Pivots_bound (i : Fin 5) :
    certificateHighestKernel0_3Rows (certificateHighestKernel0_3Pivots i) = certificateLocalPivots0_3 i := by
  fin_cases i <;> decide

/-- U is the literal archive frame restricted to the exhaustive weight rows. -/
theorem certificateHighestKernel0_3U_bound :
    certificateLocalFrame0_3.submatrix certificateHighestKernel0_3Rows id = certificateHighestKernel0_3U := by
  ext i j
  fin_cases i <;> fin_cases j <;> decide

/-- Each selected equation is an actual output coordinate of E01 or E12. -/
theorem certificateHighestKernel0_3R_bound (a : Fin 5) (b : Fin 10) :
    certificateHighestKernel0_3R a b =
      (if (certificateHighestKernel0_3Tests a).1 = 0 then certificateLocalGenerator {5} 0 1
        else certificateLocalGenerator {5} 1 2) (certificateHighestKernel0_3Tests a).2 (certificateHighestKernel0_3Rows b) := by
  fin_cases a <;> fin_cases b <;> decide

theorem certificateHighestKernel0_3denominator_ne_zero : certificateHighestKernel0_3denominator ≠ 0 := by decide

/-- The full finite reconstruction is checked at every matrix entry. -/
theorem certificateHighestKernel0_3reconstruction :
    certificateHighestKernel0_3denominator • (1 - certificateHighestKernel0_3U * certificateHighestKernel0_3P) = certificateHighestKernel0_3W * certificateHighestKernel0_3R := by
  ext i j
  fin_cases i <;> fin_cases j <;> decide

end ThreeCopyQutritWerner
