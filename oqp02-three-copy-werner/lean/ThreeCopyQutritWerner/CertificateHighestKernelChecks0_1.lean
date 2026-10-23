module

public import ThreeCopyQutritWerner.CertificateHighestKernelData0_1

@[expose] public section


/-! Physical source binding and exact scaled kernel reconstruction.
These are ordinary kernel checks, not imported arithmetic assumptions. -/

set_option maxRecDepth 100000
set_option maxHeartbeats 100000000

open scoped BigOperators Matrix

namespace ThreeCopyQutritWerner

theorem certificateHighestKernel0_1Rows_injective : Function.Injective certificateHighestKernel0_1Rows := by
  decide

theorem certificateHighestKernel0_1Rows_weight : ∀ i,
    certificateLocalWeight {5} (certificateHighestKernel0_1Rows i) = certificateHighestKernel0_1Weight := by
  decide

/-- Every physical word of the specified weight is retained. -/
theorem certificateHighestKernel0_1Rows_cover : ∀ w : CertificateLocalWord,
    certificateLocalWeight {5} w = certificateHighestKernel0_1Weight → ∃ i, certificateHighestKernel0_1Rows i = w := by
  decide

theorem certificateHighestKernel0_1Pivots_bound (i : Fin 4) :
    certificateHighestKernel0_1Rows (certificateHighestKernel0_1Pivots i) = certificateLocalPivots0_1 i := by
  fin_cases i <;> decide

/-- U is the literal archive frame restricted to the exhaustive weight rows. -/
theorem certificateHighestKernel0_1U_bound :
    certificateLocalFrame0_1.submatrix certificateHighestKernel0_1Rows id = certificateHighestKernel0_1U := by
  ext i j
  fin_cases i <;> fin_cases j <;> decide

/-- Each selected equation is an actual output coordinate of E01 or E12. -/
theorem certificateHighestKernel0_1R_bound (a : Fin 1) (b : Fin 5) :
    certificateHighestKernel0_1R a b =
      (if (certificateHighestKernel0_1Tests a).1 = 0 then certificateLocalGenerator {5} 0 1
        else certificateLocalGenerator {5} 1 2) (certificateHighestKernel0_1Tests a).2 (certificateHighestKernel0_1Rows b) := by
  fin_cases a <;> fin_cases b <;> decide

theorem certificateHighestKernel0_1denominator_ne_zero : certificateHighestKernel0_1denominator ≠ 0 := by decide

/-- The full finite reconstruction is checked at every matrix entry. -/
theorem certificateHighestKernel0_1reconstruction :
    certificateHighestKernel0_1denominator • (1 - certificateHighestKernel0_1U * certificateHighestKernel0_1P) = certificateHighestKernel0_1W * certificateHighestKernel0_1R := by
  ext i j
  fin_cases i <;> fin_cases j <;> decide

end ThreeCopyQutritWerner
