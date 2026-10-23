module

public import CGLMPBounds.Defs.TraceDensity

@[expose] public section


/-!
# Logarithmic derivatives as sums over roots with multiplicity

The root index is a multiset throughout. No square-free or simple-root
assumption is used. These finite identities are the scalar part of the
trace-resolvent route to the cluster trace in Lemma C.3.
-/

namespace CGLMPBounds.Hardy
noncomputable section
open Polynomial

lemma rootProduct_derivative_eval (s : Multiset ℂ) (ζ : ℂ)
    (hζ : ∀ a ∈ s, ζ ≠ a) :
    ((s.map (fun a => X - C a)).prod).derivative.eval ζ =
      ((s.map (fun a => X - C a)).prod).eval ζ *
        (s.map (fun a => 1 / (ζ - a))).sum := by
  revert hζ
  induction s using Multiset.induction_on with
  | empty => intro _; simp
  | @cons a s ih =>
    intro hζ
    have ha : ζ - a ≠ 0 := sub_ne_zero.mpr (hζ a (Multiset.mem_cons_self _ _))
    have hs : ∀ b ∈ s, ζ ≠ b := fun b hb => hζ b (Multiset.mem_cons_of_mem hb)
    simp only [Multiset.map_cons, Multiset.prod_cons, Multiset.sum_cons,
      Polynomial.derivative_mul, Polynomial.derivative_X_sub_C,
      Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_one,
      Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C, one_mul, ih hs]
    field_simp [ha]
    <;> ring

/-- The logarithmic derivative of any monic complex polynomial away from its
roots is the sum of reciprocal differences, counted with algebraic multiplicity. -/
theorem polynomial_logDerivative_eq_root_sum (p : ℂ[X]) (hp : p.Monic)
    (ζ : ℂ) (hζ : p.eval ζ ≠ 0) :
    p.derivative.eval ζ / p.eval ζ = (p.roots.map (fun a => 1 / (ζ - a))).sum := by
  have hroots : ∀ a ∈ p.roots, ζ ≠ a := by
    intro a ha h
    subst ζ
    exact hζ (Polynomial.isRoot_of_mem_roots ha).eq_zero
  have hfact := (IsAlgClosed.splits p).eq_prod_roots_of_monic hp
  have h := rootProduct_derivative_eval p.roots ζ hroots
  rw [← hfact] at h
  exact (div_eq_iff hζ).2 (by simpa only [mul_comm] using h)

/-- The weighted root fraction sum, with every repetition retained. -/
lemma weighted_root_fraction_sum (s : Multiset ℂ) (ζ : ℂ)
    (hζ : ∀ a ∈ s, ζ ≠ a) :
    (s.map (fun a => a / (ζ - a))).sum =
      ζ * (s.map (fun a => 1 / (ζ - a))).sum - (s.card : ℂ) := by
  revert hζ
  induction s using Multiset.induction_on with
  | empty => intro _; simp
  | @cons a s ih =>
    intro hζ
    have ha : ζ - a ≠ 0 := sub_ne_zero.mpr (hζ a (Multiset.mem_cons_self _ _))
    have hs : ∀ b ∈ s, ζ ≠ b := fun b hb => hζ b (Multiset.mem_cons_of_mem hb)
    simp only [Multiset.map_cons, Multiset.sum_cons, Multiset.card_cons, Nat.cast_add,
      Nat.cast_one, ih hs]
    field_simp [ha]
    <;> ring

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

lemma charpoly_eval_ne_zero_of_not_mem_spectrum (A : Matrix ι ι ℂ) {ζ : ℂ}
    (hζ : ζ ∉ spectrum ℂ A) : A.charpoly.eval ζ ≠ 0 := by
  intro h
  exact hζ (Matrix.mem_spectrum_of_isRoot_charpoly h)

lemma charpoly_root_ne_of_not_mem_spectrum (A : Matrix ι ι ℂ) {ζ : ℂ}
    (hζ : ζ ∉ spectrum ℂ A) : ∀ a ∈ A.charpoly.roots, ζ ≠ a := by
  intro a ha h
  subst ζ
  exact hζ (Matrix.mem_spectrum_of_isRoot_charpoly (Polynomial.isRoot_of_mem_roots ha))

lemma charpoly_roots_card (A : Matrix ι ι ℂ) :
    A.charpoly.roots.card = Fintype.card ι := by
  rw [← (IsAlgClosed.splits A.charpoly).natDegree_eq_card_roots,
    Matrix.charpoly_natDegree_eq_dim]

theorem charpoly_logDerivative_eq_root_sum (A : Matrix ι ι ℂ) {ζ : ℂ}
    (hζ : ζ ∉ spectrum ℂ A) :
    A.charpoly.derivative.eval ζ / A.charpoly.eval ζ =
      (A.charpoly.roots.map (fun a => 1 / (ζ - a))).sum :=
  polynomial_logDerivative_eq_root_sum A.charpoly A.charpoly_monic ζ
    (charpoly_eval_ne_zero_of_not_mem_spectrum A hζ)

end
end CGLMPBounds.Hardy
