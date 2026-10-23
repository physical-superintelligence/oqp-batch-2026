module

public import ThreeCopyQutritWerner.CertificateHighestKernelData1_7

@[expose] public section


set_option maxRecDepth 100000
set_option maxHeartbeats 100000000

open scoped BigOperators Matrix
namespace ThreeCopyQutritWerner

theorem certificateHighestKernel1_7RCheck040 : ∀ i : Fin 2, ∀ j : Fin 93,
    certificateHighestKernel1_7R (⟨80 + i.val, Nat.lt_of_lt_of_le (Nat.add_lt_add_left i.isLt 80) (by decide)⟩ : Fin 87) j =
      (if (certificateHighestKernel1_7Tests (⟨80 + i.val, Nat.lt_of_lt_of_le (Nat.add_lt_add_left i.isLt 80) (by decide)⟩ : Fin 87)).1 = 0 then certificateLocalGenerator {0, 1, 2} 0 1
        else certificateLocalGenerator {0, 1, 2} 1 2) (certificateHighestKernel1_7Tests (⟨80 + i.val, Nat.lt_of_lt_of_le (Nat.add_lt_add_left i.isLt 80) (by decide)⟩ : Fin 87)).2 (certificateHighestKernel1_7Rows j) := by
  letI (i : Fin 2) (j : Fin 93) : Decidable
      (certificateHighestKernel1_7R (⟨80 + i.val, Nat.lt_of_lt_of_le (Nat.add_lt_add_left i.isLt 80) (by decide)⟩ : Fin 87) j =
      (if (certificateHighestKernel1_7Tests (⟨80 + i.val, Nat.lt_of_lt_of_le (Nat.add_lt_add_left i.isLt 80) (by decide)⟩ : Fin 87)).1 = 0 then certificateLocalGenerator {0, 1, 2} 0 1
        else certificateLocalGenerator {0, 1, 2} 1 2) (certificateHighestKernel1_7Tests (⟨80 + i.val, Nat.lt_of_lt_of_le (Nat.add_lt_add_left i.isLt 80) (by decide)⟩ : Fin 87)).2 (certificateHighestKernel1_7Rows j)) := Int.instDecidableEq _ _
  decide

end ThreeCopyQutritWerner
