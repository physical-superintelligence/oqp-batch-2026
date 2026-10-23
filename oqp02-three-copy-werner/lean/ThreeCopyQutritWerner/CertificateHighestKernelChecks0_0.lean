module

public import ThreeCopyQutritWerner.CertificateHighestKernelData0_0

@[expose] public section


/-! Physical source binding and exact scaled kernel reconstruction.
These are ordinary kernel checks, not imported arithmetic assumptions. -/

set_option maxRecDepth 100000
set_option maxHeartbeats 100000000

open scoped BigOperators Matrix

namespace ThreeCopyQutritWerner

theorem certificateHighestKernel0_0Rows_injective : Function.Injective certificateHighestKernel0_0Rows := by
  decide

theorem certificateHighestKernel0_0Rows_weight : ∀ i,
    certificateLocalWeight {5} (certificateHighestKernel0_0Rows i) = certificateHighestKernel0_0Weight := by
  decide

/-- Every physical word of the specified weight is retained. -/
theorem certificateHighestKernel0_0Rows_cover : ∀ w : CertificateLocalWord,
    certificateLocalWeight {5} w = certificateHighestKernel0_0Weight → ∃ i, certificateHighestKernel0_0Rows i = w := by
  decide

theorem certificateHighestKernel0_0Pivots_bound (i : Fin 1) :
    certificateHighestKernel0_0Rows (certificateHighestKernel0_0Pivots i) = certificateLocalPivots0_0 i := by
  fin_cases i <;> decide

/-- U is the literal archive frame restricted to the exhaustive weight rows. -/
theorem certificateHighestKernel0_0U_bound :
    certificateLocalFrame0_0.submatrix certificateHighestKernel0_0Rows id = certificateHighestKernel0_0U := by
  ext i j
  fin_cases i <;> fin_cases j <;> decide

/-- Each selected equation is an actual output coordinate of E01 or E12. -/
theorem certificateHighestKernel0_0R_bound (a : Fin 0) (b : Fin 1) :
    certificateHighestKernel0_0R a b =
      (if (certificateHighestKernel0_0Tests a).1 = 0 then certificateLocalGenerator {5} 0 1
        else certificateLocalGenerator {5} 1 2) (certificateHighestKernel0_0Tests a).2 (certificateHighestKernel0_0Rows b) := by
  fin_cases a <;> fin_cases b <;> decide

theorem certificateHighestKernel0_0denominator_ne_zero : certificateHighestKernel0_0denominator ≠ 0 := by decide

/-- The full finite reconstruction is checked at every matrix entry. -/
theorem certificateHighestKernel0_0reconstruction :
    certificateHighestKernel0_0denominator • (1 - certificateHighestKernel0_0U * certificateHighestKernel0_0P) = certificateHighestKernel0_0W * certificateHighestKernel0_0R := by
  ext i j
  fin_cases i <;> fin_cases j <;> decide

end ThreeCopyQutritWerner
