module

public import ThreeCopyQutritWerner.CertificateHighestKernelData1_7

@[expose] public section


set_option maxRecDepth 100000
set_option maxHeartbeats 100000000

open scoped BigOperators Matrix
namespace ThreeCopyQutritWerner

theorem certificateHighestKernel1_7ReconstructionCheck079 : ∀ i : Fin 1, ∀ j : Fin 93,
    (certificateHighestKernel1_7denominator • (1 - certificateHighestKernel1_7U * certificateHighestKernel1_7P) : Matrix (Fin 93) (Fin 93) ℤ) (⟨79 + i.val, Nat.lt_of_lt_of_le (Nat.add_lt_add_left i.isLt 79) (by decide)⟩ : Fin 93) j =
      (certificateHighestKernel1_7W * certificateHighestKernel1_7R) (⟨79 + i.val, Nat.lt_of_lt_of_le (Nat.add_lt_add_left i.isLt 79) (by decide)⟩ : Fin 93) j := by
  decide +kernel

end ThreeCopyQutritWerner
