module

public import ThreeCopyQutritWerner.CertificateHighestKernelData2_6

@[expose] public section


set_option maxRecDepth 100000
set_option maxHeartbeats 100000000

open scoped BigOperators Matrix
namespace ThreeCopyQutritWerner

theorem certificateHighestKernel2_6RCheck024 : ∀ i : Fin 2, ∀ j : Fin 80,
    certificateHighestKernel2_6R (⟨48 + i.val, Nat.lt_of_lt_of_le (Nat.add_lt_add_left i.isLt 48) (by decide)⟩ : Fin 69) j =
      (if (certificateHighestKernel2_6Tests (⟨48 + i.val, Nat.lt_of_lt_of_le (Nat.add_lt_add_left i.isLt 48) (by decide)⟩ : Fin 69)).1 = 0 then certificateLocalGenerator {0} 0 1
        else certificateLocalGenerator {0} 1 2) (certificateHighestKernel2_6Tests (⟨48 + i.val, Nat.lt_of_lt_of_le (Nat.add_lt_add_left i.isLt 48) (by decide)⟩ : Fin 69)).2 (certificateHighestKernel2_6Rows j) := by
  letI (i : Fin 2) (j : Fin 80) : Decidable
      (certificateHighestKernel2_6R (⟨48 + i.val, Nat.lt_of_lt_of_le (Nat.add_lt_add_left i.isLt 48) (by decide)⟩ : Fin 69) j =
      (if (certificateHighestKernel2_6Tests (⟨48 + i.val, Nat.lt_of_lt_of_le (Nat.add_lt_add_left i.isLt 48) (by decide)⟩ : Fin 69)).1 = 0 then certificateLocalGenerator {0} 0 1
        else certificateLocalGenerator {0} 1 2) (certificateHighestKernel2_6Tests (⟨48 + i.val, Nat.lt_of_lt_of_le (Nat.add_lt_add_left i.isLt 48) (by decide)⟩ : Fin 69)).2 (certificateHighestKernel2_6Rows j)) := Int.instDecidableEq _ _
  decide

end ThreeCopyQutritWerner
