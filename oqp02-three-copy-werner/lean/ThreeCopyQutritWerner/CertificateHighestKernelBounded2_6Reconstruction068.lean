module

public import ThreeCopyQutritWerner.CertificateHighestKernelData2_6

@[expose] public section


set_option maxRecDepth 100000
set_option maxHeartbeats 100000000

open scoped BigOperators Matrix
namespace ThreeCopyQutritWerner

theorem certificateHighestKernel2_6ReconstructionCheck068 : ∀ i : Fin 1, ∀ j : Fin 80,
    (certificateHighestKernel2_6denominator • (1 - certificateHighestKernel2_6U * certificateHighestKernel2_6P) : Matrix (Fin 80) (Fin 80) ℤ) (⟨68 + i.val, Nat.lt_of_lt_of_le (Nat.add_lt_add_left i.isLt 68) (by decide)⟩ : Fin 80) j =
      (certificateHighestKernel2_6W * certificateHighestKernel2_6R) (⟨68 + i.val, Nat.lt_of_lt_of_le (Nat.add_lt_add_left i.isLt 68) (by decide)⟩ : Fin 80) j := by
  decide +kernel

end ThreeCopyQutritWerner
