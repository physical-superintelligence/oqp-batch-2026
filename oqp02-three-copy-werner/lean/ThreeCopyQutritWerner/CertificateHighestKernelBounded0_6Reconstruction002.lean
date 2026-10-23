module

public import ThreeCopyQutritWerner.CertificateHighestKernelData0_6

@[expose] public section


set_option maxRecDepth 100000
set_option maxHeartbeats 100000000

open scoped BigOperators Matrix
namespace ThreeCopyQutritWerner

theorem certificateHighestKernel0_6ReconstructionCheck002 : ∀ i : Fin 1, ∀ j : Fin 80,
    (certificateHighestKernel0_6denominator • (1 - certificateHighestKernel0_6U * certificateHighestKernel0_6P) : Matrix (Fin 80) (Fin 80) ℤ) (⟨2 + i.val, Nat.lt_of_lt_of_le (Nat.add_lt_add_left i.isLt 2) (by decide)⟩ : Fin 80) j =
      (certificateHighestKernel0_6W * certificateHighestKernel0_6R) (⟨2 + i.val, Nat.lt_of_lt_of_le (Nat.add_lt_add_left i.isLt 2) (by decide)⟩ : Fin 80) j := by
  decide +kernel

end ThreeCopyQutritWerner
