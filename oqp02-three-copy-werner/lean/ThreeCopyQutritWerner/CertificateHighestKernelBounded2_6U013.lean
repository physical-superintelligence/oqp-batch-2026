module

public import ThreeCopyQutritWerner.CertificateHighestKernelData2_6

@[expose] public section


set_option maxRecDepth 100000
set_option maxHeartbeats 100000000

open scoped BigOperators Matrix
namespace ThreeCopyQutritWerner

theorem certificateHighestKernel2_6UCheck013 : ∀ i : Fin 4, ∀ j : Fin 11,
    certificateLocalFrame2_6.submatrix certificateHighestKernel2_6Rows id (⟨52 + i.val, Nat.lt_of_lt_of_le (Nat.add_lt_add_left i.isLt 52) (by decide)⟩ : Fin 80) j =
      certificateHighestKernel2_6U (⟨52 + i.val, Nat.lt_of_lt_of_le (Nat.add_lt_add_left i.isLt 52) (by decide)⟩ : Fin 80) j := by
  letI (i : Fin 4) (j : Fin 11) : Decidable
      (certificateLocalFrame2_6.submatrix certificateHighestKernel2_6Rows id (⟨52 + i.val, Nat.lt_of_lt_of_le (Nat.add_lt_add_left i.isLt 52) (by decide)⟩ : Fin 80) j =
      certificateHighestKernel2_6U (⟨52 + i.val, Nat.lt_of_lt_of_le (Nat.add_lt_add_left i.isLt 52) (by decide)⟩ : Fin 80) j) := Int.instDecidableEq _ _
  decide

end ThreeCopyQutritWerner
