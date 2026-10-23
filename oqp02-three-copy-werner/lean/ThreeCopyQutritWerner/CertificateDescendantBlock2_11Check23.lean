module

public import ThreeCopyQutritWerner.CertificateDescendantBlock2_11BoundedData

@[expose] public section


set_option maxRecDepth 100000
set_option maxHeartbeats 100000000
open scoped Matrix
namespace ThreeCopyQutritWerner

theorem certificateDescendantBlock2_11Check23_inverse : ∀ r : Fin 2, ∀ j : Fin 80,
    (certificateDescendantBlockA2_11 * certificateDescendantBlockW2_11) (⟨46 + r.val, Nat.lt_of_lt_of_le (Nat.add_lt_add_left r.isLt 46) (by decide)⟩ : Fin 80) j =
      ((15120 : ℤ) • (1 : Matrix (Fin 80) (Fin 80) ℤ)) (⟨46 + r.val, Nat.lt_of_lt_of_le (Nat.add_lt_add_left r.isLt 46) (by decide)⟩ : Fin 80) j := by
  decide +kernel

theorem certificateDescendantBlock2_11Check23_physical : ∀ r : Fin 2, ∀ j : Fin 80,
    certificateSparseVector
      (certificateDescendantColumns2 (certificateDescendantBlockColumns2 11 j))
      (certificateDescendantBlockRows2 11 (⟨46 + r.val, Nat.lt_of_lt_of_le (Nat.add_lt_add_left r.isLt 46) (by decide)⟩ : Fin 80)) =
      certificateDescendantBlockA2_11 (⟨46 + r.val, Nat.lt_of_lt_of_le (Nat.add_lt_add_left r.isLt 46) (by decide)⟩ : Fin 80) j := by
  decide +kernel

end ThreeCopyQutritWerner
