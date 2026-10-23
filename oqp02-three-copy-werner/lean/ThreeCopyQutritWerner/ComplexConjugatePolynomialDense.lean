module

public import ThreeCopyQutritWerner.JointPencilSeparation
public import Mathlib.Topology.Algebra.MvPolynomial
public import Mathlib.Topology.Algebra.Module.Cardinality
public import Mathlib.Algebra.Module.Card
public import Mathlib.SetTheory.Cardinal.CountableCover
public import Mathlib.Topology.MetricSpace.Perfect
public import Mathlib.Topology.Metrizable.Real

@[expose] public section


/-! Conjugate-pencil separation survives countably many exceptional parameters. -/

noncomputable section

open scoped ComplexConjugate

namespace ThreeCopyQutritWerner

theorem mvPolynomial_eq_zero_of_eval_conjugate_dense
    (p : MvPolynomial (Fin 2) ℂ) (s : Set ℂ) (hs : Dense s)
    (hp : ∀ z ∈ s, MvPolynomial.eval ![z, conj z] p = 0) : p = 0 := by
  have hc : Continuous (fun z : ℂ => ![z, conj z]) := by fun_prop
  have he : (fun z : ℂ => MvPolynomial.eval ![z, conj z] p) = fun _ => 0 :=
    Continuous.ext_on hs (p.continuous_eval.comp hc) continuous_const hp
  exact mvPolynomial_eq_zero_of_eval_conjugate p (fun z => congrFun he z)

theorem mvPolynomial_eq_zero_of_eval_conjugate_off_countable
    (p : MvPolynomial (Fin 2) ℂ) (s : Set ℂ) (hs : s.Countable)
    (hp : ∀ z ∉ s, MvPolynomial.eval ![z, conj z] p = 0) : p = 0 :=
  mvPolynomial_eq_zero_of_eval_conjugate_dense p sᶜ (hs.dense_compl ℂ) hp

/-- In particular, finite rank-drop exceptions do not prevent separation.
The exceptional set is explicit and must be proved countable by the caller. -/
theorem jointAffinePencil_minors_separate_off_countable {κ lam : Type*}
    (A B : Matrix (Fin 3) κ ℂ) (C D : Matrix (Fin 3) lam ℂ)
    (s : Set ℂ) (hs : s.Countable)
    (hp : ∀ z ∉ s, ∀ cols : Fin 3 → κ ⊕ lam,
      ((jointAffinePencil A B C D z (conj z)).submatrix id cols).det = 0)
    (z w : ℂ) (cols : Fin 3 → κ ⊕ lam) :
    ((jointAffinePencil A B C D z w).submatrix id cols).det = 0 := by
  have hz : jointAffinePencilMinor A B C D cols = 0 :=
    mvPolynomial_eq_zero_of_eval_conjugate_off_countable _ s hs
      (fun x hx => by rw [jointAffinePencilMinor_eval]; exact hp x hx cols)
  rw [← jointAffinePencilMinor_eval, hz, map_zero]

end ThreeCopyQutritWerner
