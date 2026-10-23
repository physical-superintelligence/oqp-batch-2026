module

public import CGLMPBounds.Defs.LocalContentWeights
public import Mathlib

@[expose] public section


/-!
# Scalar inequalities for the local-component bound (Theorem F.3)

Supplement, Appendix F.4, proof of Theorem F.3. For `w ≥ 2k ≥ 0` put
`h = (w - √(w² - 4k²))/2`, the smaller root of `h² - w h + k² = 0`. The proof uses:

* `lowRoot_mul` : `h (w - h) = k²`;
* `lowRoot_le_of` : if `z ≤ w/2` and `k² ≤ z (w - z)` then `h ≤ z`;
* `revMinkowski_two`, `revMinkowski_sum` : the reverse Minkowski inequality
  `Σ_i √(w_i² - 4k_i²) ≤ √((Σ w_i)² - 4 (Σ k_i)²)` for `w_i ≥ 2k_i ≥ 0`. Since `h = w φ(k/w)` with
  `φ(t) = (1 - √(1 - 4t²))/2`, this is the weighted Jensen step `Σ w_i φ(k_i/w_i) ≥ m φ(Σ k_i / m)`
  of the source, in a form without division;
* `lowRoot_two_mul_one`, `gamma_eq_inv`, `inv_two_mul_lt_gamma` : `(2d - √(4d² - 4))/2 = γ_d`,
  `γ_d = d - √(d² - 1) = 1/(d + √(d² - 1)) > 1/(2d)` (F.10).
-/

namespace CGLMPBounds

noncomputable section

theorem lowRoot_disc_nonneg {w k : ℝ} (hk : 0 ≤ k) (hkw : 2 * k ≤ w) : 0 ≤ w ^ 2 - 4 * k ^ 2 := by
  nlinarith [mul_nonneg hk (sub_nonneg.mpr hkw), sq_nonneg (w - 2 * k)]

theorem lowRoot_mul {w k : ℝ} (hk : 0 ≤ k) (hkw : 2 * k ≤ w) :
    lowRoot w k * (w - lowRoot w k) = k ^ 2 := by
  have hs := Real.sq_sqrt (lowRoot_disc_nonneg hk hkw)
  have e : lowRoot w k * (w - lowRoot w k)
      = (w ^ 2 - Real.sqrt (w ^ 2 - 4 * k ^ 2) ^ 2) / 4 := by
    unfold lowRoot
    ring
  rw [e, hs]
  ring

theorem lowRoot_sqrt_disc_le {w k : ℝ} (hk : 0 ≤ k) (hkw : 2 * k ≤ w) :
    Real.sqrt (w ^ 2 - 4 * k ^ 2) ≤ w := by
  have hw : 0 ≤ w := by linarith
  calc Real.sqrt (w ^ 2 - 4 * k ^ 2) ≤ Real.sqrt (w ^ 2) :=
        Real.sqrt_le_sqrt (by nlinarith [sq_nonneg k])
    _ = w := Real.sqrt_sq hw

theorem lowRoot_nonneg {w k : ℝ} (hk : 0 ≤ k) (hkw : 2 * k ≤ w) : 0 ≤ lowRoot w k := by
  have := lowRoot_sqrt_disc_le hk hkw
  unfold lowRoot
  linarith

theorem lowRoot_le_half (w k : ℝ) : lowRoot w k ≤ w / 2 := by
  have := Real.sqrt_nonneg (w ^ 2 - 4 * k ^ 2)
  unfold lowRoot
  linarith

/-- If `z ≤ w/2` and `k² ≤ z (w - z)`, then `z` lies above the smaller root. -/
theorem lowRoot_le_of {w k z : ℝ} (hz : z ≤ w / 2) (hkz : k ^ 2 ≤ z * (w - z)) :
    lowRoot w k ≤ z := by
  have h1 : 0 ≤ w - 2 * z := by linarith
  have h2 : (w - 2 * z) ^ 2 ≤ w ^ 2 - 4 * k ^ 2 := by nlinarith
  have h3 : w - 2 * z ≤ Real.sqrt (w ^ 2 - 4 * k ^ 2) :=
    calc w - 2 * z = Real.sqrt ((w - 2 * z) ^ 2) := (Real.sqrt_sq h1).symm
      _ ≤ Real.sqrt (w ^ 2 - 4 * k ^ 2) := Real.sqrt_le_sqrt h2
  unfold lowRoot
  linarith

theorem revMinkowski_aux {X Y Z c : ℝ} (hX : 0 ≤ X) (hY : 0 ≤ Y) (hc : 0 ≤ c)
    (hXY : X * Y ≤ c ^ 2) (hZ : X + Y + 2 * c ≤ Z) :
    Real.sqrt X + Real.sqrt Y ≤ Real.sqrt Z := by
  have hsXY : Real.sqrt X * Real.sqrt Y ≤ c := by
    rw [← Real.sqrt_mul hX]
    calc Real.sqrt (X * Y) ≤ Real.sqrt (c ^ 2) := Real.sqrt_le_sqrt hXY
      _ = c := Real.sqrt_sq hc
  have hL : 0 ≤ Real.sqrt X + Real.sqrt Y := add_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
  have hsq : (Real.sqrt X + Real.sqrt Y) ^ 2 ≤ Z := by
    have e2 : (Real.sqrt X + Real.sqrt Y) ^ 2 = X + Y + 2 * (Real.sqrt X * Real.sqrt Y) := by
      rw [add_sq, Real.sq_sqrt hX, Real.sq_sqrt hY]
      ring
    rw [e2]
    linarith
  calc Real.sqrt X + Real.sqrt Y = Real.sqrt ((Real.sqrt X + Real.sqrt Y) ^ 2) :=
        (Real.sqrt_sq hL).symm
    _ ≤ Real.sqrt Z := Real.sqrt_le_sqrt hsq

/-- Reverse Minkowski inequality for two timelike vectors `(w_i, 2k_i)`, `w_i ≥ 2k_i ≥ 0`. -/
theorem revMinkowski_two {w₁ k₁ w₂ k₂ : ℝ} (hk₁ : 0 ≤ k₁) (h₁ : 2 * k₁ ≤ w₁) (hk₂ : 0 ≤ k₂)
    (h₂ : 2 * k₂ ≤ w₂) :
    Real.sqrt (w₁ ^ 2 - 4 * k₁ ^ 2) + Real.sqrt (w₂ ^ 2 - 4 * k₂ ^ 2)
      ≤ Real.sqrt ((w₁ + w₂) ^ 2 - 4 * (k₁ + k₂) ^ 2) := by
  have hprod : 2 * k₁ * (2 * k₂) ≤ w₁ * w₂ :=
    mul_le_mul h₁ h₂ (by linarith) (by linarith)
  refine revMinkowski_aux (lowRoot_disc_nonneg hk₁ h₁) (lowRoot_disc_nonneg hk₂ h₂)
    (c := w₁ * w₂ - 4 * (k₁ * k₂)) (by nlinarith [hprod]) ?_ (le_of_eq (by ring))
  nlinarith [sq_nonneg (w₁ * k₂ - k₁ * w₂)]

/-- Reverse Minkowski inequality for finitely many timelike vectors `(w_i, 2k_i)`. -/
theorem revMinkowski_sum {ι : Type*} [DecidableEq ι] (w k : ι → ℝ) (s : Finset ι) :
    (∀ i ∈ s, 0 ≤ k i) → (∀ i ∈ s, 2 * k i ≤ w i) →
      ∑ i ∈ s, Real.sqrt (w i ^ 2 - 4 * k i ^ 2)
        ≤ Real.sqrt ((∑ i ∈ s, w i) ^ 2 - 4 * (∑ i ∈ s, k i) ^ 2) := by
  induction s using Finset.induction_on with
  | empty =>
    intro _ _
    simp
  | insert j s hj ih =>
    intro hk hkw
    have hk' : ∀ i ∈ s, 0 ≤ k i := fun i hi => hk i (Finset.mem_insert_of_mem hi)
    have hkw' : ∀ i ∈ s, 2 * k i ≤ w i := fun i hi => hkw i (Finset.mem_insert_of_mem hi)
    have hS0 : 0 ≤ ∑ i ∈ s, k i := Finset.sum_nonneg hk'
    have hS1 : 2 * ∑ i ∈ s, k i ≤ ∑ i ∈ s, w i := by
      rw [Finset.mul_sum]
      exact Finset.sum_le_sum hkw'
    have hIH := ih hk' hkw'
    rw [Finset.sum_insert hj, Finset.sum_insert hj, Finset.sum_insert hj]
    calc Real.sqrt (w j ^ 2 - 4 * k j ^ 2) + ∑ i ∈ s, Real.sqrt (w i ^ 2 - 4 * k i ^ 2)
        ≤ Real.sqrt (w j ^ 2 - 4 * k j ^ 2)
          + Real.sqrt ((∑ i ∈ s, w i) ^ 2 - 4 * (∑ i ∈ s, k i) ^ 2) := by linarith
      _ ≤ Real.sqrt ((w j + ∑ i ∈ s, w i) ^ 2 - 4 * (k j + ∑ i ∈ s, k i) ^ 2) :=
          revMinkowski_two (hk j (Finset.mem_insert_self j s))
            (hkw j (Finset.mem_insert_self j s)) hS0 hS1

/-- With `m_A = 2d` outcomes in total, `(m_A - √(m_A² - 4))/2 = d - √(d² - 1)`. -/
theorem lowRoot_two_mul_one (d : ℝ) : lowRoot (2 * d) 1 = d - Real.sqrt (d ^ 2 - 1) := by
  unfold lowRoot
  have e : (2 * d) ^ 2 - 4 * 1 ^ 2 = 2 ^ 2 * (d ^ 2 - 1) := by ring
  rw [e, Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2 ^ 2), Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 2)]
  ring

theorem gamma_sqrt_lt {d : ℝ} (hd : 1 ≤ d) : Real.sqrt (d ^ 2 - 1) < d := by
  have h0 : 0 ≤ d ^ 2 - 1 := by nlinarith
  have hs := Real.sq_sqrt h0
  have hs0 := Real.sqrt_nonneg (d ^ 2 - 1)
  nlinarith

/-- `γ_d = d - √(d² - 1) = 1/(d + √(d² - 1))` (F.10). -/
theorem gamma_eq_inv {d : ℝ} (hd : 1 ≤ d) :
    d - Real.sqrt (d ^ 2 - 1) = 1 / (d + Real.sqrt (d ^ 2 - 1)) := by
  have h0 : 0 ≤ d ^ 2 - 1 := by nlinarith
  have hs := Real.sq_sqrt h0
  have hpos : 0 < d + Real.sqrt (d ^ 2 - 1) := by
    have := Real.sqrt_nonneg (d ^ 2 - 1)
    linarith
  rw [eq_div_iff hpos.ne']
  nlinarith

/-- `γ_d > 1/(2d)` (F.10). -/
theorem inv_two_mul_lt_gamma {d : ℝ} (hd : 1 ≤ d) : 1 / (2 * d) < d - Real.sqrt (d ^ 2 - 1) := by
  have h0 : 0 ≤ d ^ 2 - 1 := by nlinarith
  have hs := Real.sq_sqrt h0
  have hlt := gamma_sqrt_lt hd
  rw [div_lt_iff₀ (by linarith)]
  nlinarith [mul_pos (sub_pos.mpr hlt) (sub_pos.mpr hlt)]

end

end CGLMPBounds
