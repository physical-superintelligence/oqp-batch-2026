module

public import ThreeCopyQutritWerner.CertificateHighestKernelData0_6

@[expose] public section


set_option maxRecDepth 100000
set_option maxHeartbeats 100000000

open scoped BigOperators Matrix
namespace ThreeCopyQutritWerner

theorem certificateHighestKernel0_6RCheck014 : ∀ i : Fin 2, ∀ j : Fin 80,
    certificateHighestKernel0_6R (⟨28 + i.val, Nat.lt_of_lt_of_le (Nat.add_lt_add_left i.isLt 28) (by decide)⟩ : Fin 69) j =
      (if (certificateHighestKernel0_6Tests (⟨28 + i.val, Nat.lt_of_lt_of_le (Nat.add_lt_add_left i.isLt 28) (by decide)⟩ : Fin 69)).1 = 0 then certificateLocalGenerator {5} 0 1
        else certificateLocalGenerator {5} 1 2) (certificateHighestKernel0_6Tests (⟨28 + i.val, Nat.lt_of_lt_of_le (Nat.add_lt_add_left i.isLt 28) (by decide)⟩ : Fin 69)).2 (certificateHighestKernel0_6Rows j) := by
  letI (i : Fin 2) (j : Fin 80) : Decidable
      (certificateHighestKernel0_6R (⟨28 + i.val, Nat.lt_of_lt_of_le (Nat.add_lt_add_left i.isLt 28) (by decide)⟩ : Fin 69) j =
      (if (certificateHighestKernel0_6Tests (⟨28 + i.val, Nat.lt_of_lt_of_le (Nat.add_lt_add_left i.isLt 28) (by decide)⟩ : Fin 69)).1 = 0 then certificateLocalGenerator {5} 0 1
        else certificateLocalGenerator {5} 1 2) (certificateHighestKernel0_6Tests (⟨28 + i.val, Nat.lt_of_lt_of_le (Nat.add_lt_add_left i.isLt 28) (by decide)⟩ : Fin 69)).2 (certificateHighestKernel0_6Rows j)) := Int.instDecidableEq _ _
  decide

end ThreeCopyQutritWerner
