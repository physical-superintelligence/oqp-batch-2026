module

public import CGLMPBounds.Hardy.SchwarzFinitePoleTransport

@[expose] public section


/-! Actual circle residues of a finite polynomial/partial-fraction sum,
with arbitrary repeated poles and positive pole orders. The coefficient
formula is derived from scalar Cauchy and genuine primitives; all summands
are circle integrable. -/

open Complex Metric Set Polynomial
open scoped Classical

namespace CGLMPBounds.Hardy
noncomputable section

lemma circleIntegral_inverse_power (k : ℕ) {a c : ℂ} {R : ℝ}
    (hR : 0 ≤ R) (ha : a ∉ sphere c R) :
    (∮ z in C(c, R), (z - a)⁻¹ ^ k) =
      (2 * Real.pi * Complex.I : ℂ) * (if k = 1 ∧ a ∈ ball c R then 1 else 0) := by
  classical
  by_cases hk : k = 1
  · subst k
    simpa only [pow_one, pow_zero, one_div, true_and] using
      circleIntegral_powerRootFraction 0 hR ha
  · have hkn : -(k : ℤ) ≠ -1 := by omega
    have hz := circleIntegral.integral_sub_zpow_of_ne hkn c a R
    simpa only [zpow_neg, zpow_natCast, inv_pow, hk, false_and, if_false, mul_zero] using hz

lemma circleIntegral_finite_poles {κ : Type*} (s : Finset κ)
    (q : ℂ[X]) (a b : κ → ℂ) (k : κ → ℕ) {c : ℂ} {R : ℝ}
    (hR : 0 ≤ R) (hsep : ∀ i ∈ s, a i ∉ sphere c R) :
    (∮ z in C(c, R), q.eval z + ∑ i ∈ s, b i * (z - a i)⁻¹ ^ k i) =
      (2 * Real.pi * Complex.I : ℂ) *
        ∑ i ∈ s, if k i = 1 ∧ a i ∈ ball c R then b i else 0 := by
  classical
  have hi : ∀ i ∈ s, CircleIntegrable (fun z : ℂ => b i * (z - a i)⁻¹ ^ k i) c R := by
    intro i hi
    exact (continuousOn_const.mul (power_pole_continuousOn (hsep i hi) (k i))).circleIntegrable hR
  have hsum : CircleIntegrable (fun z : ℂ => ∑ i ∈ s, b i * (z - a i)⁻¹ ^ k i) c R := by
    convert! CircleIntegrable.sum s hi using 1
    funext z
    simp only [Finset.sum_apply]
  rw [circleIntegral.integral_add (q.continuousOn.circleIntegrable hR) hsum,
    circleIntegral_polynomial_eq_zero q hR, zero_add, circleIntegral.integral_fun_sum hi,
    Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i his
  rw [circleIntegral.integral_const_mul, circleIntegral_inverse_power (k i) hR (hsep i his)]
  by_cases h : k i = 1 ∧ a i ∈ ball c R <;> simp [h, mul_comm]

/-- The two inner circle integrals add to the outer one when every pole is
inside the outer circle and the two inner disks select complementary poles.
This is a proved finite-residue calculation, not a contour oracle. -/
theorem circleIntegral_finite_poles_partition {κ : Type*} (s : Finset κ)
    (q : ℂ[X]) (a b : κ → ℂ) (k : κ → ℕ)
    {c₁ c₂ c₃ : ℂ} {R₁ R₂ R₃ : ℝ}
    (hR₁ : 0 ≤ R₁) (hR₂ : 0 ≤ R₂) (hR₃ : 0 ≤ R₃)
    (hsep₁ : ∀ i ∈ s, a i ∉ sphere c₁ R₁)
    (hsep₂ : ∀ i ∈ s, a i ∉ sphere c₂ R₂)
    (hsep₃ : ∀ i ∈ s, a i ∉ sphere c₃ R₃)
    (houter : ∀ i ∈ s, a i ∈ ball c₃ R₃)
    (hpartition : ∀ i ∈ s, a i ∈ ball c₁ R₁ ↔ a i ∉ ball c₂ R₂) :
    (∮ z in C(c₁, R₁), q.eval z + ∑ i ∈ s, b i * (z - a i)⁻¹ ^ k i) +
      (∮ z in C(c₂, R₂), q.eval z + ∑ i ∈ s, b i * (z - a i)⁻¹ ^ k i) =
        ∮ z in C(c₃, R₃), q.eval z + ∑ i ∈ s, b i * (z - a i)⁻¹ ^ k i := by
  classical
  rw [circleIntegral_finite_poles s q a b k hR₁ hsep₁,
    circleIntegral_finite_poles s q a b k hR₂ hsep₂,
    circleIntegral_finite_poles s q a b k hR₃ hsep₃,
    ← mul_add, ← Finset.sum_add_distrib]
  congr 1
  apply Finset.sum_congr rfl
  intro i hi
  by_cases hk : k i = 1
  · by_cases h₂ : a i ∈ ball c₂ R₂
    · have h₁ : a i ∉ ball c₁ R₁ := fun h => (hpartition i hi).mp h h₂
      simp [hk, h₁, h₂, houter i hi]
    · have h₁ : a i ∈ ball c₁ R₁ := (hpartition i hi).mpr h₂
      simp [hk, h₁, h₂, houter i hi]
  · simp [hk]

end
end CGLMPBounds.Hardy
