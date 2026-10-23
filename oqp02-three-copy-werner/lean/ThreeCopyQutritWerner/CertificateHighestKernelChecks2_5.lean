module

public import ThreeCopyQutritWerner.CertificateHighestKernelData2_5

@[expose] public section


/-! Physical source binding and exact scaled kernel reconstruction.
These are ordinary kernel checks, not imported arithmetic assumptions. -/

set_option maxRecDepth 100000
set_option maxHeartbeats 100000000

open scoped BigOperators Matrix

namespace ThreeCopyQutritWerner

theorem certificateHighestKernel2_5Rows_injective : Function.Injective certificateHighestKernel2_5Rows := by
  decide +kernel

theorem certificateHighestKernel2_5Rows_weight : ∀ i,
    certificateLocalWeight {0} (certificateHighestKernel2_5Rows i) = certificateHighestKernel2_5Weight := by
  decide +kernel

/-- Every physical word of the specified weight is retained. -/
theorem certificateHighestKernel2_5Rows_cover : ∀ w : CertificateLocalWord,
    certificateLocalWeight {0} w = certificateHighestKernel2_5Weight → ∃ i, certificateHighestKernel2_5Rows i = w := by
  decide +kernel

theorem certificateHighestKernel2_5Pivots_bound (i : Fin 10) :
    certificateHighestKernel2_5Rows (certificateHighestKernel2_5Pivots i) = certificateLocalPivots2_5 i := by
  revert i
  decide +kernel

/-- U is the literal archive frame restricted to the exhaustive weight rows. -/
theorem certificateHighestKernel2_5U_bound :
    certificateLocalFrame2_5.submatrix certificateHighestKernel2_5Rows id = certificateHighestKernel2_5U := by
  apply Matrix.ext
  letI (i : Fin 50) (j : Fin 10) : Decidable
      (certificateLocalFrame2_5.submatrix certificateHighestKernel2_5Rows id i j =
        certificateHighestKernel2_5U i j) := Int.instDecidableEq _ _
  decide

/-- Each selected equation is an actual output coordinate of E01 or E12. -/
theorem certificateHighestKernel2_5R_bound (a : Fin 40) (b : Fin 50) :
    certificateHighestKernel2_5R a b =
      (if (certificateHighestKernel2_5Tests a).1 = 0 then certificateLocalGenerator {0} 0 1
        else certificateLocalGenerator {0} 1 2) (certificateHighestKernel2_5Tests a).2 (certificateHighestKernel2_5Rows b) := by
  revert a b
  letI (a : Fin 40) (b : Fin 50) : Decidable
      (certificateHighestKernel2_5R a b =
      (if (certificateHighestKernel2_5Tests a).1 = 0 then certificateLocalGenerator {0} 0 1
        else certificateLocalGenerator {0} 1 2) (certificateHighestKernel2_5Tests a).2 (certificateHighestKernel2_5Rows b)) := Int.instDecidableEq _ _
  decide

theorem certificateHighestKernel2_5denominator_ne_zero : certificateHighestKernel2_5denominator ≠ 0 := by
  decide +kernel

/-- The full finite reconstruction is checked at every matrix entry. -/
theorem certificateHighestKernel2_5reconstruction :
    certificateHighestKernel2_5denominator • (1 - certificateHighestKernel2_5U * certificateHighestKernel2_5P) = certificateHighestKernel2_5W * certificateHighestKernel2_5R := by
  apply Matrix.ext
  decide +kernel

end ThreeCopyQutritWerner
