module

public import ThreeCopyQutritWerner.ComplexConjugatePolynomial
public import Mathlib.LinearAlgebra.Matrix.Polynomial

@[expose] public section


/-! Actual joint local minors separate source and conjugate-corange pencil parameters. -/

noncomputable section

open scoped Matrix ComplexConjugate

namespace ThreeCopyQutritWerner

/-- The original two affine column families, kept in distinct column summands. -/
def jointAffinePencil {κ lam : Type*}
    (A B : Matrix (Fin 3) κ ℂ) (C D : Matrix (Fin 3) lam ℂ) (z w : ℂ) :
    Matrix (Fin 3) (κ ⊕ lam) ℂ :=
  fun i j => Sum.elim (fun a => A i a + z * B i a) (fun b => C i b + w * D i b) j

def jointAffinePencilMinor {κ lam : Type*}
    (A B : Matrix (Fin 3) κ ℂ) (C D : Matrix (Fin 3) lam ℂ)
    (cols : Fin 3 → κ ⊕ lam) : MvPolynomial (Fin 2) ℂ :=
  Matrix.det (fun i j => Sum.elim
    (fun a => MvPolynomial.C (A i a) + MvPolynomial.X 0 * MvPolynomial.C (B i a))
    (fun b => MvPolynomial.C (C i b) + MvPolynomial.X 1 * MvPolynomial.C (D i b)) (cols j))

theorem jointAffinePencilMinor_eval {κ lam : Type*}
    (A B : Matrix (Fin 3) κ ℂ) (C D : Matrix (Fin 3) lam ℂ)
    (cols : Fin 3 → κ ⊕ lam) (z w : ℂ) :
    MvPolynomial.eval ![z, w] (jointAffinePencilMinor A B C D cols) =
      ((jointAffinePencil A B C D z w).submatrix id cols).det := by
  let P : Matrix (Fin 3) (Fin 3) (MvPolynomial (Fin 2) ℂ) := fun i j => Sum.elim
    (fun a => MvPolynomial.C (A i a) + MvPolynomial.X 0 * MvPolynomial.C (B i a))
    (fun b => MvPolynomial.C (C i b) + MvPolynomial.X 1 * MvPolynomial.C (D i b)) (cols j)
  have hP : (MvPolynomial.eval ![z, w]).mapMatrix P =
      (jointAffinePencil A B C D z w).submatrix id cols := by
    ext i j
    change MvPolynomial.eval ![z, w] (P i j) =
      jointAffinePencil A B C D z w i (cols j)
    dsimp only [P, jointAffinePencil]
    cases h : cols j <;> simp [h]
  calc
    _ = (MvPolynomial.eval ![z, w]) P.det := rfl
    _ = ((MvPolynomial.eval ![z, w]).mapMatrix P).det :=
      RingHom.map_det (MvPolynomial.eval ![z, w]) P
    _ = _ := congrArg Matrix.det hP

/-- Vanishing along the actual conjugated pencil implies vanishing for two
independent complex parameters. This asserts minors, not a common-plane conclusion. -/
theorem jointAffinePencil_minors_separate {κ lam : Type*}
    (A B : Matrix (Fin 3) κ ℂ) (C D : Matrix (Fin 3) lam ℂ)
    (hp : ∀ z : ℂ, ∀ cols : Fin 3 → κ ⊕ lam,
      ((jointAffinePencil A B C D z (conj z)).submatrix id cols).det = 0)
    (z w : ℂ) (cols : Fin 3 → κ ⊕ lam) :
    ((jointAffinePencil A B C D z w).submatrix id cols).det = 0 := by
  rw [← jointAffinePencilMinor_eval]
  exact mvPolynomial_eval_zero_of_eval_conjugate _
    (fun x => by rw [jointAffinePencilMinor_eval]; exact hp x cols) z w

end ThreeCopyQutritWerner
