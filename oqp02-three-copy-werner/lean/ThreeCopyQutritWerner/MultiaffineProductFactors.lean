module

public import Mathlib.RingTheory.Polynomial.UniqueFactorization
public import Mathlib.Algebra.MvPolynomial.NoZeroDivisors
public import Mathlib.Data.Complex.Basic
public import Lean.Elab.Tactic.Omega
public import Mathlib.Algebra.FiniteSupport.Basic
public import Mathlib.Algebra.Group.TypeTags.Pointwise
public import Mathlib.Algebra.GroupWithZero.Action.Regular
public import Mathlib.Algebra.GroupWithZero.Indicator
public import Mathlib.Algebra.Module.Torsion.Field
public import Mathlib.Algebra.NoZeroSMulDivisors.Basic
public import Mathlib.Algebra.Order.BigOperators.Ring.Finset
public import Mathlib.Algebra.Ring.Hom.InjSurj
public import Mathlib.Data.Fintype.Order
public import Mathlib.Data.List.Enum
public import Mathlib.SetTheory.Cardinal.Ordinal
public import Mathlib.SetTheory.Ordinal.FundamentalSequence
public import Mathlib.Tactic.Basify.Attr

@[expose] public section


/-!
# Exact factor separation for multiaffine product identities

A product identity between four nonzero multiaffine polynomials separates
into two pairs of factors on disjoint variable sets. This is a prospective
algebraic ingredient for the binary three-site zero classification; the
physical polynomial encoding and qutrit thin-carrier reduction are separate.
-/

namespace ThreeCopyQutritWerner

/-- A genuine product identity over a decomposition domain has a factor grid.
No coprimality or supplied factorization is an additional premise. -/
theorem exists_product_factor_grid {R : Type*} [CommMonoidWithZero R]
    [IsCancelMulZero R] [DecompositionMonoid R]
    (a b c d : R) (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0)
    (he : a * b = c * d) :
    ∃ p q r s : R, p ≠ 0 ∧ q ≠ 0 ∧ r ≠ 0 ∧ s ≠ 0 ∧
      a = p * r ∧ b = q * s ∧ c = p * s ∧ d = q * r := by
  obtain ⟨p, s, hp, hs, hps⟩ := exists_dvd_and_dvd_of_dvd_mul (show c ∣ a * b from ⟨d, he⟩)
  obtain ⟨r, har⟩ := hp
  obtain ⟨q, hbq⟩ := hs
  have hpr : p * r ≠ 0 := har ▸ ha
  have hsq : s * q ≠ 0 := hbq ▸ hb
  have hprod : c * (q * r) = c * d := by
    calc
      c * (q * r) = (p * r) * (s * q) := by rw [hps]; ac_rfl
      _ = c * d := by rw [← har, ← hbq]; exact he
  have hd : d = q * r := (mul_left_cancel₀ hc hprod).symm
  exact ⟨p, q, r, s, (mul_ne_zero_iff.mp hpr).1, (mul_ne_zero_iff.mp hsq).2,
    (mul_ne_zero_iff.mp hpr).2, (mul_ne_zero_iff.mp hsq).1,
    har, hbq.trans (mul_comm s q), hps, hd⟩

/-- Degree one in every variable prevents the two factor pairs from sharing a variable. -/
theorem multiaffine_factor_grid_separates {σ : Type*}
    (p q r s : MvPolynomial σ ℂ) (hp : p ≠ 0) (hq : q ≠ 0)
    (hr : r ≠ 0) (hs : s ≠ 0)
    (ha : ∀ i, (p * r).degreeOf i ≤ 1) (hb : ∀ i, (q * s).degreeOf i ≤ 1)
    (hc : ∀ i, (p * s).degreeOf i ≤ 1) (hd : ∀ i, (q * r).degreeOf i ≤ 1) :
    ∀ i, (p.degreeOf i = 0 ∧ q.degreeOf i = 0) ∨
      (r.degreeOf i = 0 ∧ s.degreeOf i = 0) := by
  intro i
  have ha := ha i
  have hb := hb i
  have hc := hc i
  have hd := hd i
  rw [MvPolynomial.degreeOf_mul_eq hp hr] at ha
  rw [MvPolynomial.degreeOf_mul_eq hq hs] at hb
  rw [MvPolynomial.degreeOf_mul_eq hp hs] at hc
  rw [MvPolynomial.degreeOf_mul_eq hq hr] at hd
  omega

/-- The factors and the variable partition are derived from the four original
multiaffine polynomials themselves. The fourth nonzero condition follows from
the product identity and the first three nonzero polynomials. -/
theorem exists_separated_multiaffine_product_factors {σ : Type*}
    (a b c d : MvPolynomial σ ℂ) (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0)
    (he : a * b = c * d)
    (haff : ∀ i, a.degreeOf i ≤ 1) (hbff : ∀ i, b.degreeOf i ≤ 1)
    (hcff : ∀ i, c.degreeOf i ≤ 1) (hdff : ∀ i, d.degreeOf i ≤ 1) :
    ∃ p q r s : MvPolynomial σ ℂ,
      p ≠ 0 ∧ q ≠ 0 ∧ r ≠ 0 ∧ s ≠ 0 ∧
      a = p * r ∧ b = q * s ∧ c = p * s ∧ d = q * r ∧
      (∀ i, (p.degreeOf i = 0 ∧ q.degreeOf i = 0) ∨
        (r.degreeOf i = 0 ∧ s.degreeOf i = 0)) := by
  obtain ⟨p, q, r, s, hp, hq, hr, hs, hpa, hqb, hpc, hqd⟩ :=
    exists_product_factor_grid a b c d ha hb hc he
  refine ⟨p, q, r, s, hp, hq, hr, hs, hpa, hqb, hpc, hqd, ?_⟩
  exact multiaffine_factor_grid_separates p q r s hp hq hr hs
    (hpa ▸ haff) (hqb ▸ hbff) (hpc ▸ hcff) (hqd ▸ hdff)

end ThreeCopyQutritWerner
