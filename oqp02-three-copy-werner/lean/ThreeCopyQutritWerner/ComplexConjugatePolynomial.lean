module

public import ThreeCopyQutritWerner.Imports
public import Mathlib.Algebra.MvPolynomial.Funext
public import Mathlib.Algebra.MvPolynomial.Polynomial

@[expose] public section


/-!
# Separating a complex parameter from its conjugate in polynomial identities

A complex bivariate polynomial vanishing at every (z,conj z) is identically
zero. The real coordinate substitution z=x+iy, conj z=x-iy is invertible
over the complex numbers; infinite real evaluation grids prove the identity.
No degree bound, analytic continuation assumption or reality of coefficients
is required.
-/

noncomputable section

open scoped ComplexConjugate

namespace ThreeCopyQutritWerner

def complexConjugateSubstitution : Fin 2 → MvPolynomial (Fin 2) ℂ :=
  ![MvPolynomial.X 0 + MvPolynomial.C Complex.I * MvPolynomial.X 1,
    MvPolynomial.X 0 - MvPolynomial.C Complex.I * MvPolynomial.X 1]

theorem complexConjugateSubstitution_eval (p : MvPolynomial (Fin 2) ℂ) (x y : ℂ) :
    MvPolynomial.eval ![x, y] (p.eval₂ MvPolynomial.C complexConjugateSubstitution) =
      MvPolynomial.eval ![x + Complex.I * y, x - Complex.I * y] p := by
  rw [← MvPolynomial.eval_assoc]
  apply congrArg (fun f : Fin 2 → ℂ => MvPolynomial.eval f p)
  funext i
  fin_cases i <;> simp [complexConjugateSubstitution, Function.comp_def]

/-- The actual conjugate diagonal is sufficient to determine every complex
bivariate polynomial, including arbitrary finite degrees and complex coefficients. -/
theorem mvPolynomial_eq_zero_of_eval_conjugate (p : MvPolynomial (Fin 2) ℂ)
    (hp : ∀ z : ℂ, MvPolynomial.eval ![z, conj z] p = 0) : p = 0 := by
  let q := p.eval₂ MvPolynomial.C complexConjugateSubstitution
  have hq : q = 0 := by
    apply MvPolynomial.funext_set (fun _ : Fin 2 => Set.range ((↑) : ℝ → ℂ))
      (fun _ => Set.infinite_range_of_injective Complex.ofReal_injective)
    intro v hv
    obtain ⟨x, hx⟩ := hv 0 (Set.mem_univ 0)
    obtain ⟨y, hy⟩ := hv 1 (Set.mem_univ 1)
    have he : v = ![(x : ℂ), (y : ℂ)] := by
      funext i
      fin_cases i
      · exact hx.symm
      · exact hy.symm
    rw [he, map_zero]
    change MvPolynomial.eval ![(x : ℂ), (y : ℂ)]
      (p.eval₂ MvPolynomial.C complexConjugateSubstitution) = 0
    rw [complexConjugateSubstitution_eval]
    have hc : conj ((x : ℂ) + Complex.I * (y : ℂ)) =
        (x : ℂ) - Complex.I * (y : ℂ) := by simp [sub_eq_add_neg]
    simpa only [hc] using hp ((x : ℂ) + Complex.I * (y : ℂ))
  apply MvPolynomial.funext
  intro v
  let x := (v 0 + v 1) / 2
  let y := Complex.I * (v 1 - v 0) / 2
  have hIy : Complex.I * y = (v 0 - v 1) / 2 := by
    calc
      _ = (Complex.I * Complex.I) * (v 1 - v 0) / 2 := by dsimp [y]; ring
      _ = _ := by rw [Complex.I_mul_I]; ring
  have he : ![x + Complex.I * y, x - Complex.I * y] = v := by
    funext i
    fin_cases i
    · change x + Complex.I * y = v 0
      rw [hIy]
      dsimp [x]
      ring
    · change x - Complex.I * y = v 1
      rw [hIy]
      dsimp [x]
      ring
  have hh := complexConjugateSubstitution_eval p x y
  change MvPolynomial.eval ![x, y] q = _ at hh
  rw [hq, map_zero, he] at hh
  simpa only [map_zero] using hh.symm

theorem mvPolynomial_eval_zero_of_eval_conjugate (p : MvPolynomial (Fin 2) ℂ)
    (hp : ∀ z : ℂ, MvPolynomial.eval ![z, conj z] p = 0) (z w : ℂ) :
    MvPolynomial.eval ![z, w] p = 0 := by
  rw [mvPolynomial_eq_zero_of_eval_conjugate p hp, map_zero]

end ThreeCopyQutritWerner
