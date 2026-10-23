module

public import ThreeCopyQutritWerner.CertificateRegisterPerm
public import Mathlib.Data.Complex.Basic

@[expose] public section


/-! Register matrices form the exact physical register representation.
Both declarations are moved verbatim from CertificateCentralIdempotence;
no character convolution or concrete carrier identity is needed here. -/

noncomputable section
namespace ThreeCopyQutritWerner

/-- The coordinate relabeling and permutation-matrix conventions cancel their
two order reversals, giving an ordinary representation of the register group. -/
theorem certificateRegisterMatrix_mul {k : ℕ} {n : Type*} [Fintype n] [DecidableEq n]
    (σ τ : Equiv.Perm (Fin k)) :
    (certificateRegisterPerm (n := n) σ).permMatrix ℂ *
        (certificateRegisterPerm τ).permMatrix ℂ =
      (certificateRegisterPerm (σ * τ)).permMatrix ℂ := by
  rw [← Matrix.permMatrix_mul]
  congr 1

theorem certificateRegisterMatrix_one {k : ℕ} {n : Type*} [Fintype n] [DecidableEq n] :
    (certificateRegisterPerm (n := n) (1 : Equiv.Perm (Fin k))).permMatrix ℂ = 1 := by
  change (1 : Equiv.Perm (Fin k → n)).permMatrix ℂ = 1
  exact Matrix.permMatrix_one

end ThreeCopyQutritWerner
