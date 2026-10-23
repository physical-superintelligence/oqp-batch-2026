module

public import ThreeCopyQutritWerner.CertificateHighestKernelData0_2

@[expose] public section


/-! Physical source binding and exact scaled kernel reconstruction.
These are ordinary kernel checks, not imported arithmetic assumptions. -/

set_option maxRecDepth 100000
set_option maxHeartbeats 100000000

open scoped BigOperators Matrix

namespace ThreeCopyQutritWerner

theorem certificateHighestKernel0_2Rows_injective : Function.Injective certificateHighestKernel0_2Rows := by
  decide

theorem certificateHighestKernel0_2Rows_weight : ∀ i,
    certificateLocalWeight {5} (certificateHighestKernel0_2Rows i) = certificateHighestKernel0_2Weight := by
  decide

/-- Every physical word of the specified weight is retained. -/
theorem certificateHighestKernel0_2Rows_cover : ∀ w : CertificateLocalWord,
    certificateLocalWeight {5} w = certificateHighestKernel0_2Weight → ∃ i, certificateHighestKernel0_2Rows i = w := by
  decide

theorem certificateHighestKernel0_2Pivots_bound (i : Fin 5) :
    certificateHighestKernel0_2Rows (certificateHighestKernel0_2Pivots i) = certificateLocalPivots0_2 i := by
  fin_cases i <;> decide

/-- U is the literal archive frame restricted to the exhaustive weight rows. -/
theorem certificateHighestKernel0_2U_bound :
    certificateLocalFrame0_2.submatrix certificateHighestKernel0_2Rows id = certificateHighestKernel0_2U := by
  ext i j
  fin_cases i <;> fin_cases j <;> decide

/-- Each selected equation is an actual output coordinate of E01 or E12. -/
theorem certificateHighestKernel0_2R_bound (a : Fin 6) (b : Fin 11) :
    certificateHighestKernel0_2R a b =
      (if (certificateHighestKernel0_2Tests a).1 = 0 then certificateLocalGenerator {5} 0 1
        else certificateLocalGenerator {5} 1 2) (certificateHighestKernel0_2Tests a).2 (certificateHighestKernel0_2Rows b) := by
  fin_cases a <;> fin_cases b <;> decide

theorem certificateHighestKernel0_2denominator_ne_zero : certificateHighestKernel0_2denominator ≠ 0 := by decide

/-- The full finite reconstruction is checked at every matrix entry. -/
theorem certificateHighestKernel0_2reconstruction :
    certificateHighestKernel0_2denominator • (1 - certificateHighestKernel0_2U * certificateHighestKernel0_2P) = certificateHighestKernel0_2W * certificateHighestKernel0_2R := by
  ext i j
  fin_cases i <;> fin_cases j <;> decide

end ThreeCopyQutritWerner
