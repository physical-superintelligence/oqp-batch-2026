module

public import Mathlib.Analysis.SpecialFunctions.Bernstein

@[expose] public section


/-!
# Positivity from product Bernstein coefficients

Reusable algebra for Appendix J. The weights are Mathlib's actual Bernstein polynomials;
nonnegativity and partition of unity come from the pinned library. A future coefficient
certificate must prove the reconstruction of the manuscript polynomial before using this.
-/

namespace CGLMPBounds.Certificates

open Finset

/-- The exact monomial-to-Bernstein conversion. This is the one-dimensional identity
used twice in the printed Appendix J coefficient formula. -/
theorem bernstein_monomial (n p : ℕ) (hp : p ≤ n) (x : unitInterval) :
    (∑ i : Fin (n + 1), ((i.val.choose p : ℝ) / (n.choose p : ℝ)) *
      bernstein n i x) = (x : ℝ) ^ p := by
  have hn : (n.choose p : ℝ) ≠ 0 := by exact_mod_cast Nat.choose_ne_zero hp
  have hterm (i : ℕ) (hi : i < n - p + 1) :
      (((p + i).choose p : ℝ) / (n.choose p : ℝ)) * bernstein n (p + i) x =
        (x : ℝ) ^ p * bernstein (n - p) i x := by
    have hc : (n.choose (p + i) : ℝ) * ((p + i).choose p : ℝ) =
        (n.choose p : ℝ) * ((n - p).choose i : ℝ) := by
      have h := Nat.choose_mul (n := n) (k := p + i) (s := p)
        (Nat.le_add_right p i)
      have hi' : p + i - p = i := by omega
      rw [hi'] at h
      exact_mod_cast h
    have he : n - (p + i) = n - p - i := by omega
    have hcoef : (((p + i).choose p : ℝ) / (n.choose p : ℝ)) *
        (n.choose (p + i) : ℝ) = ((n - p).choose i : ℝ) := by
      field_simp
      nlinarith [hc]
    rw [bernstein_apply, bernstein_apply, he, pow_add]
    calc
      _ = ((((p + i).choose p : ℝ) / (n.choose p : ℝ)) * (n.choose (p + i) : ℝ)) *
          (x : ℝ) ^ p * (x : ℝ) ^ i * (1 - (x : ℝ)) ^ (n - p - i) := by ring
      _ = _ := by rw [hcoef]; ring
  rw [Fin.sum_univ_eq_sum_range (fun i : ℕ =>
    ((i.choose p : ℝ) / (n.choose p : ℝ)) * bernstein n i x)]
  have hlen : p + (n - p + 1) = n + 1 := by omega
  rw [← hlen, Finset.sum_range_add]
  have hzero : (∑ i ∈ Finset.range p,
      ((i.choose p : ℝ) / (n.choose p : ℝ)) * bernstein n i x) = 0 := by
    apply Finset.sum_eq_zero
    intro i hi
    simp [Nat.choose_eq_zero_of_lt (Finset.mem_range.mp hi)]
  rw [hzero, zero_add]
  calc
    _ = ∑ i ∈ Finset.range (n - p + 1), (x : ℝ) ^ p * bernstein (n - p) i x := by
      apply Finset.sum_congr rfl
      intro i hi
      exact hterm i (Finset.mem_range.mp hi)
    _ = (x : ℝ) ^ p := by
      rw [← Finset.mul_sum, ← Fin.sum_univ_eq_sum_range, bernstein.probability, mul_one]

/-- Exact reconstruction for an arbitrary finite sum of monomials of bounded bidegree.
Coefficients may have either sign. Positivity is a separate finite check. -/
theorem product_bernstein_reconstruction {ι : Type*} [Fintype ι]
    (n m : ℕ) (a : ι → ℝ) (p q : ι → ℕ)
    (hp : ∀ k, p k ≤ n) (hq : ∀ k, q k ≤ m) (x y : unitInterval) :
    (∑ i : Fin (n + 1), ∑ j : Fin (m + 1),
      (∑ k, a k * ((i.val.choose (p k) : ℝ) / (n.choose (p k) : ℝ)) *
        ((j.val.choose (q k) : ℝ) / (m.choose (q k) : ℝ))) *
          bernstein n i x * bernstein m j y) =
      ∑ k, a k * (x : ℝ) ^ p k * (y : ℝ) ^ q k := by
  simp_rw [Finset.sum_mul]
  have hswap (f : Fin (n + 1) → Fin (m + 1) → ι → ℝ) :
      (∑ i, ∑ j, ∑ k, f i j k) = ∑ k, ∑ i, ∑ j, f i j k := by
    calc
      _ = ∑ i, ∑ k, ∑ j, f i j k := by
        apply Finset.sum_congr rfl
        intro i _
        exact Finset.sum_comm
      _ = _ := Finset.sum_comm
  rw [hswap]
  apply Finset.sum_congr rfl
  intro k _
  calc
    _ = a k *
        (∑ i : Fin (n + 1), ((i.val.choose (p k) : ℝ) / (n.choose (p k) : ℝ)) *
          bernstein n i x) *
        (∑ j : Fin (m + 1), ((j.val.choose (q k) : ℝ) / (m.choose (q k) : ℝ)) *
          bernstein m j y) := by
      simp only [Finset.mul_sum, Finset.sum_mul]
      conv_rhs => rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      ring
    _ = _ := by rw [bernstein_monomial n (p k) (hp k), bernstein_monomial m (q k) (hq k)]

/-- A coefficientwise lower bound is also a lower bound on the product Bernstein expansion. -/
theorem le_product_bernstein (n m : ℕ) (c : Fin (n + 1) → Fin (m + 1) → ℝ)
    (ε : ℝ) (hc : ∀ i j, ε ≤ c i j) (x y : unitInterval) :
    ε ≤ ∑ i, ∑ j, c i j * bernstein n i x * bernstein m j y := by
  have hsum : ∑ i : Fin (n + 1), ∑ j : Fin (m + 1),
      ε * bernstein n i x * bernstein m j y = ε := by
    simp only [← Finset.mul_sum, bernstein.probability, mul_one]
  rw [← hsum]
  apply Finset.sum_le_sum
  intro i _
  apply Finset.sum_le_sum
  intro j _
  exact mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right (hc i j) bernstein_nonneg) bernstein_nonneg

/-- Strict positivity follows from a certified strictly positive common coefficient bound. -/
theorem product_bernstein_pos (n m : ℕ) (c : Fin (n + 1) → Fin (m + 1) → ℝ)
    (ε : ℝ) (hε : 0 < ε) (hc : ∀ i j, ε ≤ c i j) (x y : unitInterval) :
    0 < ∑ i, ∑ j, c i j * bernstein n i x * bernstein m j y :=
  lt_of_lt_of_le hε (le_product_bernstein n m c ε hc x y)

end CGLMPBounds.Certificates
