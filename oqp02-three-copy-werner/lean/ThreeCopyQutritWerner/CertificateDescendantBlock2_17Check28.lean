module

public import ThreeCopyQutritWerner.CertificateDescendantBlock2_17BoundedData

@[expose] public section


set_option maxRecDepth 100000
set_option maxHeartbeats 100000000
open scoped Matrix
namespace ThreeCopyQutritWerner

theorem certificateDescendantBlock2_17Check28_inverse : ∀ r : Fin 2, ∀ j : Fin 80,
    (certificateDescendantBlockA2_17 * certificateDescendantBlockW2_17) (⟨56 + r.val, Nat.lt_of_lt_of_le (Nat.add_lt_add_left r.isLt 56) (by decide)⟩ : Fin 80) j =
      ((2520 : ℤ) • (1 : Matrix (Fin 80) (Fin 80) ℤ)) (⟨56 + r.val, Nat.lt_of_lt_of_le (Nat.add_lt_add_left r.isLt 56) (by decide)⟩ : Fin 80) j := by
  decide +kernel

theorem certificateDescendantBlock2_17Check28_physical : ∀ r : Fin 2, ∀ j : Fin 80,
    certificateSparseVector
      (certificateDescendantColumns2 (certificateDescendantBlockColumns2 17 j))
      (certificateDescendantBlockRows2 17 (⟨56 + r.val, Nat.lt_of_lt_of_le (Nat.add_lt_add_left r.isLt 56) (by decide)⟩ : Fin 80)) =
      certificateDescendantBlockA2_17 (⟨56 + r.val, Nat.lt_of_lt_of_le (Nat.add_lt_add_left r.isLt 56) (by decide)⟩ : Fin 80) j := by
  decide +kernel

end ThreeCopyQutritWerner
