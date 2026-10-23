module

public import ThreeCopyQutritWerner.CertificateHighestKernelData0_6

@[expose] public section


set_option maxRecDepth 100000
set_option maxHeartbeats 100000000

open scoped BigOperators Matrix
namespace ThreeCopyQutritWerner

theorem certificateHighestKernel0_6UCheck017 : ∀ i : Fin 4, ∀ j : Fin 11,
    certificateLocalFrame0_6.submatrix certificateHighestKernel0_6Rows id (⟨68 + i.val, Nat.lt_of_lt_of_le (Nat.add_lt_add_left i.isLt 68) (by decide)⟩ : Fin 80) j =
      certificateHighestKernel0_6U (⟨68 + i.val, Nat.lt_of_lt_of_le (Nat.add_lt_add_left i.isLt 68) (by decide)⟩ : Fin 80) j := by
  letI (i : Fin 4) (j : Fin 11) : Decidable
      (certificateLocalFrame0_6.submatrix certificateHighestKernel0_6Rows id (⟨68 + i.val, Nat.lt_of_lt_of_le (Nat.add_lt_add_left i.isLt 68) (by decide)⟩ : Fin 80) j =
      certificateHighestKernel0_6U (⟨68 + i.val, Nat.lt_of_lt_of_le (Nat.add_lt_add_left i.isLt 68) (by decide)⟩ : Fin 80) j) := Int.instDecidableEq _ _
  decide

end ThreeCopyQutritWerner
