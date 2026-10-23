module

public import Mathlib.Algebra.Polynomial.PartialFractions
public import Mathlib.Algebra.Polynomial.RingDivision
public import Mathlib.Analysis.Complex.Polynomial.Basic

@[expose] public section


/-! A genuine simultaneous partial-fraction expansion at all points away
from a finite complex pole set, with arbitrary multiplicities. Applying
Mathlib's algebraic decomposition to the algebra of functions on that
punctured set makes the coefficients independent of the evaluation point.
This avoids assuming the matrix integrand's desired contour equality. -/

open Polynomial

namespace CGLMPBounds.Hardy
noncomputable section

lemma complex_polynomial_eq_constant_of_degree_lt_one {p : ℂ[X]}
    (hp : p.degree < 1) : p = C (p.coeff 0) := by
  by_cases hz : p = 0
  · simp [hz]
  · apply eq_C_of_natDegree_eq_zero
    have hd : p.natDegree < 1 := (natDegree_lt_iff_degree_lt hz).mpr hp
    omega

/-- The quotient and all scalar partial-fraction coefficients are chosen once
and work at every point off the actual finite pole set. -/
theorem exists_complex_partial_fractions (p : ℂ[X]) (s : Finset ℂ) (m : ℂ → ℕ) :
    ∃ (q : ℂ[X]) (b : (a : ℂ) → Fin (m a) → ℂ),
      ∀ z : ℂ, z ∉ s →
        p.eval z * ∏ a ∈ s, (z - a)⁻¹ ^ m a =
          q.eval z + ∑ a ∈ s, ∑ j : Fin (m a), b a j * (z - a)⁻¹ ^ (j.val + 1) := by
  classical
  let Ω := {z : ℂ // z ∉ s}
  let ev : ℂ[X] →+* (Ω → ℂ) := RingHom.pi (fun z => Polynomial.evalRingHom z.val)
  letI : Algebra ℂ[X] (Ω → ℂ) := ev.toAlgebra
  let gi : ℂ → Ω → ℂ := fun a z => (z.val - a)⁻¹
  have hg : ∀ a ∈ s, (X - C a : ℂ[X]).Monic := fun a _ => monic_X_sub_C a
  have hgg : Set.Pairwise (s : Set ℂ) fun a b => IsCoprime (X - C a) (X - C b) := by
    intro a _ b _ hab
    exact isCoprime_X_sub_C_of_isUnit_sub (sub_ne_zero.mpr hab).isUnit
  have hgi : ∀ a ∈ s, gi a * algebraMap ℂ[X] (Ω → ℂ) (X - C a) = 1 := by
    intro a ha
    funext z
    have hza : z.val ≠ a := by
      intro he
      exact z.property (he.symm ▸ ha)
    change (z.val - a)⁻¹ * (X - C a).eval z.val = 1
    simp [sub_ne_zero.mpr hza]
  obtain ⟨q, r, hr, he⟩ :=
    mul_prod_pow_inverse_eq_quo_add_sum_rem_mul_pow_inverse p hg hgg m hgi
  refine ⟨q, fun a j => (r a j).coeff 0, ?_⟩
  intro z hz
  have heval := congrArg (fun f : Ω → ℂ => f ⟨z, hz⟩) he
  have hrconst : ∀ a ∈ s, ∀ j : Fin (m a), r a j = C ((r a j).coeff 0) := by
    intro a ha j
    apply complex_polynomial_eq_constant_of_degree_lt_one
    simpa only [degree_X_sub_C] using hr a ha j
  have heval' : p.eval z * ∏ a ∈ s, (z - a)⁻¹ ^ m a =
      q.eval z + ∑ a ∈ s, ∑ j : Fin (m a), (r a j).eval z * (z - a)⁻¹ ^ (j.val + 1) := by
    simpa only [RingHom.algebraMap_toAlgebra, ev, RingHom.pi_apply,
      Polynomial.coe_evalRingHom, gi, Pi.mul_apply, Pi.add_apply, Pi.pow_apply,
      Finset.prod_apply, Finset.sum_apply] using heval
  rw [heval']
  congr 1
  apply Finset.sum_congr rfl
  intro a ha
  apply Finset.sum_congr rfl
  intro j _
  rw [hrconst a ha j, eval_C]

end
end CGLMPBounds.Hardy
