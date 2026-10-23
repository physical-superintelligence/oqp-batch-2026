module

public import ThreeCopyQutritWerner.CertificateHighestKernelData0_5

@[expose] public section


/-! Physical source binding and exact scaled kernel reconstruction.
These are ordinary kernel checks, not imported arithmetic assumptions. -/

set_option maxRecDepth 100000
set_option maxHeartbeats 100000000

open scoped BigOperators Matrix

namespace ThreeCopyQutritWerner

theorem certificateHighestKernel0_5Rows_injective : Function.Injective certificateHighestKernel0_5Rows := by
  decide +kernel

theorem certificateHighestKernel0_5Rows_weight : ∀ i,
    certificateLocalWeight {5} (certificateHighestKernel0_5Rows i) = certificateHighestKernel0_5Weight := by
  decide +kernel

/-- Every physical word of the specified weight is retained. -/
theorem certificateHighestKernel0_5Rows_cover : ∀ w : CertificateLocalWord,
    certificateLocalWeight {5} w = certificateHighestKernel0_5Weight → ∃ i, certificateHighestKernel0_5Rows i = w := by
  decide +kernel

theorem certificateHighestKernel0_5Pivots_bound (i : Fin 10) :
    certificateHighestKernel0_5Rows (certificateHighestKernel0_5Pivots i) = certificateLocalPivots0_5 i := by
  revert i
  decide +kernel

/-- U is the literal archive frame restricted to the exhaustive weight rows. -/
theorem certificateHighestKernel0_5U_bound :
    certificateLocalFrame0_5.submatrix certificateHighestKernel0_5Rows id = certificateHighestKernel0_5U := by
  apply Matrix.ext
  letI (i : Fin 50) (j : Fin 10) : Decidable
      (certificateLocalFrame0_5.submatrix certificateHighestKernel0_5Rows id i j =
        certificateHighestKernel0_5U i j) := Int.instDecidableEq _ _
  decide

/-- Each selected equation is an actual output coordinate of E01 or E12. -/
theorem certificateHighestKernel0_5R_bound (a : Fin 40) (b : Fin 50) :
    certificateHighestKernel0_5R a b =
      (if (certificateHighestKernel0_5Tests a).1 = 0 then certificateLocalGenerator {5} 0 1
        else certificateLocalGenerator {5} 1 2) (certificateHighestKernel0_5Tests a).2 (certificateHighestKernel0_5Rows b) := by
  revert a b
  letI (a : Fin 40) (b : Fin 50) : Decidable
      (certificateHighestKernel0_5R a b =
        (if (certificateHighestKernel0_5Tests a).1 = 0 then certificateLocalGenerator {5} 0 1
          else certificateLocalGenerator {5} 1 2)
          (certificateHighestKernel0_5Tests a).2 (certificateHighestKernel0_5Rows b)) :=
    Int.instDecidableEq _ _
  decide

theorem certificateHighestKernel0_5denominator_ne_zero : certificateHighestKernel0_5denominator ≠ 0 := by
  decide +kernel

/-- The full finite reconstruction is checked at every matrix entry. -/
theorem certificateHighestKernel0_5reconstruction :
    certificateHighestKernel0_5denominator • (1 - certificateHighestKernel0_5U * certificateHighestKernel0_5P) = certificateHighestKernel0_5W * certificateHighestKernel0_5R := by
  apply Matrix.ext
  decide +kernel

end ThreeCopyQutritWerner
