module

public import ThreeCopyQutritWerner.MultiaffineProductFactors
public import Mathlib.Algebra.MvPolynomial.Degrees
public import Mathlib.Data.Finsupp.Fintype

@[expose] public section


/-!
# Faithful multiaffine coordinates for a finite binary tensor

Each computational-basis word contributes its own squarefree monomial.
The coefficient map is injective and identifies exactly the polynomials of
degree at most one in each variable. This module does not yet identify a
physical replica projector with multiplication of these polynomials.
-/

noncomputable section

open scoped BigOperators

namespace ThreeCopyQutritWerner

variable {σ : Type*} [Fintype σ] [DecidableEq σ]

/-- The squarefree exponent of the original binary computational word. -/
def binaryWordExponent (w : σ → Fin 2) : σ →₀ ℕ :=
  Finsupp.equivFunOnFinite.symm (fun i => (w i).val)

@[simp] theorem binaryWordExponent_apply (w : σ → Fin 2) (i : σ) :
    binaryWordExponent w i = (w i).val := rfl

theorem binaryWordExponent_injective : Function.Injective (binaryWordExponent (σ := σ)) := by
  intro w v h
  funext i
  apply Fin.ext
  exact congrArg (fun m : σ →₀ ℕ => m i) h

/-- The actual binary tensor coefficients, with no quotient or identified words. -/
def binaryTensorPolynomial (x : (σ → Fin 2) → ℂ) : MvPolynomial σ ℂ :=
  ∑ w, MvPolynomial.monomial (binaryWordExponent w) (x w)

/-- Every computational-basis coefficient is recovered verbatim. -/
theorem binaryTensorPolynomial_coeff (x : (σ → Fin 2) → ℂ) (w : σ → Fin 2) :
    (binaryTensorPolynomial x).coeff (binaryWordExponent w) = x w := by
  simp only [binaryTensorPolynomial, MvPolynomial.coeff_sum, MvPolynomial.coeff_monomial,
    binaryWordExponent_injective.eq_iff, Finset.sum_ite_eq', Finset.mem_univ, if_true]

theorem binaryTensorPolynomial_injective : Function.Injective (binaryTensorPolynomial (σ := σ)) := by
  intro x y h
  funext w
  have he := congrArg (fun p : MvPolynomial σ ℂ => p.coeff (binaryWordExponent w)) h
  simpa only [binaryTensorPolynomial_coeff] using he

@[simp] theorem binaryTensorPolynomial_zero :
    binaryTensorPolynomial (0 : (σ → Fin 2) → ℂ) = 0 := by
  simp [binaryTensorPolynomial]

theorem binaryTensorPolynomial_ne_zero {x : (σ → Fin 2) → ℂ} (hx : x ≠ 0) :
    binaryTensorPolynomial x ≠ 0 := by
  intro h
  apply hx
  apply binaryTensorPolynomial_injective
  simpa only [binaryTensorPolynomial_zero] using h

/-- Each actual tensor polynomial has degree at most one in every site. -/
theorem binaryTensorPolynomial_degreeOf (x : (σ → Fin 2) → ℂ) (i : σ) :
    (binaryTensorPolynomial x).degreeOf i ≤ 1 := by
  apply (MvPolynomial.degreeOf_sum_le i Finset.univ
    (fun w => MvPolynomial.monomial (binaryWordExponent w) (x w))).trans
  apply Finset.sup_le
  intro w _
  by_cases hw : x w = 0
  · simp [hw]
  · rw [MvPolynomial.degreeOf_monomial_eq _ _ hw, binaryWordExponent_apply]
    exact Nat.le_of_lt_succ (w i).isLt

/-- A coefficient outside the binary exponents vanishes in any multiaffine polynomial. -/
theorem multiaffine_coeff_zero_of_nonbinary (p : MvPolynomial σ ℂ)
    (hp : ∀ i, p.degreeOf i ≤ 1) (m : σ →₀ ℕ) (hm : ¬ ∀ i, m i < 2) :
    p.coeff m = 0 := by
  classical
  obtain ⟨i, hi⟩ := not_forall.mp hm
  have hpi := hp i
  have hnot : m ∉ p.support :=
    MvPolynomial.notMem_support_of_degreeOf_lt i (by omega)
  exact MvPolynomial.notMem_support_iff.mp hnot

/-- The original coefficients reconstruct every multiaffine polynomial. -/
theorem binaryTensorPolynomial_reconstruct (p : MvPolynomial σ ℂ)
    (hp : ∀ i, p.degreeOf i ≤ 1) :
    binaryTensorPolynomial (fun w => p.coeff (binaryWordExponent w)) = p := by
  classical
  ext m
  by_cases hm : ∀ i, m i < 2
  · let w : σ → Fin 2 := fun i => ⟨m i, hm i⟩
    have hw : binaryWordExponent w = m := by ext i; rfl
    rw [← hw, binaryTensorPolynomial_coeff]
  · rw [multiaffine_coeff_zero_of_nonbinary _ (binaryTensorPolynomial_degreeOf _) m hm,
      multiaffine_coeff_zero_of_nonbinary p hp m hm]

end ThreeCopyQutritWerner
