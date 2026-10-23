module

public import ThreeCopyQutritWerner.CertificateHighestKernelData1_7

@[expose] public section


set_option maxRecDepth 100000
set_option maxHeartbeats 100000000

open scoped BigOperators Matrix
namespace ThreeCopyQutritWerner

theorem certificateHighestKernel1_7UCheck011 : ∀ i : Fin 4, ∀ j : Fin 6,
    certificateLocalFrame1_7.submatrix certificateHighestKernel1_7Rows id (⟨44 + i.val, Nat.lt_of_lt_of_le (Nat.add_lt_add_left i.isLt 44) (by decide)⟩ : Fin 93) j =
      certificateHighestKernel1_7U (⟨44 + i.val, Nat.lt_of_lt_of_le (Nat.add_lt_add_left i.isLt 44) (by decide)⟩ : Fin 93) j := by
  letI (i : Fin 4) (j : Fin 6) : Decidable
      (certificateLocalFrame1_7.submatrix certificateHighestKernel1_7Rows id (⟨44 + i.val, Nat.lt_of_lt_of_le (Nat.add_lt_add_left i.isLt 44) (by decide)⟩ : Fin 93) j =
      certificateHighestKernel1_7U (⟨44 + i.val, Nat.lt_of_lt_of_le (Nat.add_lt_add_left i.isLt 44) (by decide)⟩ : Fin 93) j) := Int.instDecidableEq _ _
  decide

end ThreeCopyQutritWerner
