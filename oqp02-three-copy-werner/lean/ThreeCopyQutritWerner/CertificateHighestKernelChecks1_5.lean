module

public import ThreeCopyQutritWerner.CertificateHighestKernelData1_5

@[expose] public section


/-! Physical source binding and exact scaled kernel reconstruction.
These are ordinary kernel checks, not imported arithmetic assumptions. -/

set_option maxRecDepth 100000
set_option maxHeartbeats 100000000

open scoped BigOperators Matrix

namespace ThreeCopyQutritWerner

theorem certificateHighestKernel1_5Rows_injective : Function.Injective certificateHighestKernel1_5Rows := by
  decide +kernel

theorem certificateHighestKernel1_5Rows_weight : ∀ i,
    certificateLocalWeight {0, 1, 2} (certificateHighestKernel1_5Rows i) = certificateHighestKernel1_5Weight := by
  decide +kernel

/-- Every physical word of the specified weight is retained. -/
theorem certificateHighestKernel1_5Rows_cover : ∀ w : CertificateLocalWord,
    certificateLocalWeight {0, 1, 2} w = certificateHighestKernel1_5Weight → ∃ i, certificateHighestKernel1_5Rows i = w := by
  decide +kernel

theorem certificateHighestKernel1_5Pivots_bound (i : Fin 7) :
    certificateHighestKernel1_5Rows (certificateHighestKernel1_5Pivots i) = certificateLocalPivots1_5 i := by
  revert i
  decide +kernel

/-- U is the literal archive frame restricted to the exhaustive weight rows. -/
theorem certificateHighestKernel1_5U_bound :
    certificateLocalFrame1_5.submatrix certificateHighestKernel1_5Rows id = certificateHighestKernel1_5U := by
  apply Matrix.ext
  letI (i : Fin 24) (j : Fin 7) : Decidable
      (certificateLocalFrame1_5.submatrix certificateHighestKernel1_5Rows id i j =
        certificateHighestKernel1_5U i j) := Int.instDecidableEq _ _
  decide

/-- Each selected equation is an actual output coordinate of E01 or E12. -/
theorem certificateHighestKernel1_5R_bound (a : Fin 17) (b : Fin 24) :
    certificateHighestKernel1_5R a b =
      (if (certificateHighestKernel1_5Tests a).1 = 0 then certificateLocalGenerator {0, 1, 2} 0 1
        else certificateLocalGenerator {0, 1, 2} 1 2) (certificateHighestKernel1_5Tests a).2 (certificateHighestKernel1_5Rows b) := by
  revert a b
  letI (a : Fin 17) (b : Fin 24) : Decidable
      (certificateHighestKernel1_5R a b =
      (if (certificateHighestKernel1_5Tests a).1 = 0 then certificateLocalGenerator {0, 1, 2} 0 1
        else certificateLocalGenerator {0, 1, 2} 1 2) (certificateHighestKernel1_5Tests a).2 (certificateHighestKernel1_5Rows b)) := Int.instDecidableEq _ _
  decide

theorem certificateHighestKernel1_5denominator_ne_zero : certificateHighestKernel1_5denominator ≠ 0 := by
  decide +kernel

/-- The full finite reconstruction is checked at every matrix entry. -/
theorem certificateHighestKernel1_5reconstruction :
    certificateHighestKernel1_5denominator • (1 - certificateHighestKernel1_5U * certificateHighestKernel1_5P) = certificateHighestKernel1_5W * certificateHighestKernel1_5R := by
  apply Matrix.ext
  decide +kernel

end ThreeCopyQutritWerner
