module

public import ThreeCopyQutritWerner.CertificateHighestKernelData1_6

@[expose] public section


/-! Physical source binding and exact scaled kernel reconstruction.
These are ordinary kernel checks, not imported arithmetic assumptions. -/

set_option maxRecDepth 100000
set_option maxHeartbeats 100000000

open scoped BigOperators Matrix

namespace ThreeCopyQutritWerner

theorem certificateHighestKernel1_6Rows_injective : Function.Injective certificateHighestKernel1_6Rows := by
  decide +kernel

theorem certificateHighestKernel1_6Rows_weight : ∀ i,
    certificateLocalWeight {0, 1, 2} (certificateHighestKernel1_6Rows i) = certificateHighestKernel1_6Weight := by
  decide +kernel

/-- Every physical word of the specified weight is retained. -/
theorem certificateHighestKernel1_6Rows_cover : ∀ w : CertificateLocalWord,
    certificateLocalWeight {0, 1, 2} w = certificateHighestKernel1_6Weight → ∃ i, certificateHighestKernel1_6Rows i = w := by
  decide +kernel

theorem certificateHighestKernel1_6Pivots_bound (i : Fin 17) :
    certificateHighestKernel1_6Rows (certificateHighestKernel1_6Pivots i) = certificateLocalPivots1_6 i := by
  revert i
  decide +kernel

/-- U is the literal archive frame restricted to the exhaustive weight rows. -/
theorem certificateHighestKernel1_6U_bound :
    certificateLocalFrame1_6.submatrix certificateHighestKernel1_6Rows id = certificateHighestKernel1_6U := by
  apply Matrix.ext
  letI (i : Fin 60) (j : Fin 17) : Decidable
      (certificateLocalFrame1_6.submatrix certificateHighestKernel1_6Rows id i j =
        certificateHighestKernel1_6U i j) := Int.instDecidableEq _ _
  decide

/-- Each selected equation is an actual output coordinate of E01 or E12. -/
theorem certificateHighestKernel1_6R_bound (a : Fin 43) (b : Fin 60) :
    certificateHighestKernel1_6R a b =
      (if (certificateHighestKernel1_6Tests a).1 = 0 then certificateLocalGenerator {0, 1, 2} 0 1
        else certificateLocalGenerator {0, 1, 2} 1 2) (certificateHighestKernel1_6Tests a).2 (certificateHighestKernel1_6Rows b) := by
  revert a b
  letI (a : Fin 43) (b : Fin 60) : Decidable
      (certificateHighestKernel1_6R a b =
      (if (certificateHighestKernel1_6Tests a).1 = 0 then certificateLocalGenerator {0, 1, 2} 0 1
        else certificateLocalGenerator {0, 1, 2} 1 2) (certificateHighestKernel1_6Tests a).2 (certificateHighestKernel1_6Rows b)) := Int.instDecidableEq _ _
  decide

theorem certificateHighestKernel1_6denominator_ne_zero : certificateHighestKernel1_6denominator ≠ 0 := by
  decide +kernel

/-- The full finite reconstruction is checked at every matrix entry. -/
theorem certificateHighestKernel1_6reconstruction :
    certificateHighestKernel1_6denominator • (1 - certificateHighestKernel1_6U * certificateHighestKernel1_6P) = certificateHighestKernel1_6W * certificateHighestKernel1_6R := by
  apply Matrix.ext
  decide +kernel

end ThreeCopyQutritWerner
