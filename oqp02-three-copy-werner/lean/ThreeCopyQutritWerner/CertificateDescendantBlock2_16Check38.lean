module

public import ThreeCopyQutritWerner.CertificateDescendantBlock2_16BoundedData

@[expose] public section


set_option maxRecDepth 100000
set_option maxHeartbeats 100000000
open scoped Matrix
namespace ThreeCopyQutritWerner

theorem certificateDescendantBlock2_16Check38_inverse : ∀ r : Fin 2, ∀ j : Fin 80,
    (certificateDescendantBlockA2_16 * certificateDescendantBlockW2_16) (⟨76 + r.val, Nat.lt_of_lt_of_le (Nat.add_lt_add_left r.isLt 76) (by decide)⟩ : Fin 80) j =
      ((5040 : ℤ) • (1 : Matrix (Fin 80) (Fin 80) ℤ)) (⟨76 + r.val, Nat.lt_of_lt_of_le (Nat.add_lt_add_left r.isLt 76) (by decide)⟩ : Fin 80) j := by
  decide +kernel

theorem certificateDescendantBlock2_16Check38_physical : ∀ r : Fin 2, ∀ j : Fin 80,
    certificateSparseVector
      (certificateDescendantColumns2 (certificateDescendantBlockColumns2 16 j))
      (certificateDescendantBlockRows2 16 (⟨76 + r.val, Nat.lt_of_lt_of_le (Nat.add_lt_add_left r.isLt 76) (by decide)⟩ : Fin 80)) =
      certificateDescendantBlockA2_16 (⟨76 + r.val, Nat.lt_of_lt_of_le (Nat.add_lt_add_left r.isLt 76) (by decide)⟩ : Fin 80) j := by
  decide +kernel

end ThreeCopyQutritWerner
