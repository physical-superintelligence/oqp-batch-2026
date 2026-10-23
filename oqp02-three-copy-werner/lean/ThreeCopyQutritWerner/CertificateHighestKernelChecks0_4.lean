module

public import ThreeCopyQutritWerner.CertificateHighestKernelData0_4

@[expose] public section


/-! Physical source binding and exact scaled kernel reconstruction.
These are ordinary kernel checks, not imported arithmetic assumptions. -/

set_option maxRecDepth 100000
set_option maxHeartbeats 100000000

open scoped BigOperators Matrix

namespace ThreeCopyQutritWerner

theorem certificateHighestKernel0_4Rows_injective : Function.Injective certificateHighestKernel0_4Rows := by
  decide

theorem certificateHighestKernel0_4Rows_weight : ∀ i,
    certificateLocalWeight {5} (certificateHighestKernel0_4Rows i) = certificateHighestKernel0_4Weight := by
  decide

/-- Every physical word of the specified weight is retained. -/
theorem certificateHighestKernel0_4Rows_cover : ∀ w : CertificateLocalWord,
    certificateLocalWeight {5} w = certificateHighestKernel0_4Weight → ∃ i, certificateHighestKernel0_4Rows i = w := by
  decide

theorem certificateHighestKernel0_4Pivots_bound (i : Fin 15) :
    certificateHighestKernel0_4Rows (certificateHighestKernel0_4Pivots i) = certificateLocalPivots0_4 i := by
  fin_cases i <;> decide

/-- U is the literal archive frame restricted to the exhaustive weight rows. -/
theorem certificateHighestKernel0_4U_bound :
    certificateLocalFrame0_4.submatrix certificateHighestKernel0_4Rows id = certificateHighestKernel0_4U := by
  ext i j
  fin_cases i <;> fin_cases j <;> decide

/-- Each selected equation is an actual output coordinate of E01 or E12. -/
theorem certificateHighestKernel0_4R_bound (a : Fin 20) (b : Fin 35) :
    certificateHighestKernel0_4R a b =
      (if (certificateHighestKernel0_4Tests a).1 = 0 then certificateLocalGenerator {5} 0 1
        else certificateLocalGenerator {5} 1 2) (certificateHighestKernel0_4Tests a).2 (certificateHighestKernel0_4Rows b) := by
  fin_cases a <;> fin_cases b <;> decide

theorem certificateHighestKernel0_4denominator_ne_zero : certificateHighestKernel0_4denominator ≠ 0 := by decide

/-- The full finite reconstruction is checked at every matrix entry. -/
theorem certificateHighestKernel0_4reconstruction :
    certificateHighestKernel0_4denominator • (1 - certificateHighestKernel0_4U * certificateHighestKernel0_4P) = certificateHighestKernel0_4W * certificateHighestKernel0_4R := by
  ext i j
  fin_cases i <;> fin_cases j <;> decide

end ThreeCopyQutritWerner
