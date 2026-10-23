module

public import CGLMPBounds.Hardy.HardyPotentialAnalytic

@[expose] public section


/-! Global conjugation and parity of the literal double primitive.
These algebraic integral symmetries remain valid at totalized singular
points; they do not assert continuity at those points. -/

namespace CGLMPBounds.Hardy
noncomputable section
open Complex MeasureTheory
open scoped ComplexConjugate

lemma segmentPrimitive_conj {g : ℂ → ℂ}
    (hg : ∀ z, g (conj z) = conj (g z)) (z : ℂ) :
    segmentPrimitive g (conj z) = conj (segmentPrimitive g z) := by
  simp only [segmentPrimitive, map_mul]
  congr 1
  simp only [intervalIntegral.integral_of_le zero_le_one]
  rw [← integral_conj]
  apply integral_congr_ae
  filter_upwards with u
  rw [show (u : ℂ) * conj z = conj ((u : ℂ) * z) by simp, hg]

lemma segmentPrimitive_odd_of_even {g : ℂ → ℂ}
    (hg : ∀ z, g (-z) = g z) (z : ℂ) :
    segmentPrimitive g (-z) = -segmentPrimitive g z := by
  unfold segmentPrimitive
  simp only [neg_mul, mul_neg, hg]

lemma segmentPrimitive_even_of_odd {g : ℂ → ℂ}
    (hg : ∀ z, g (-z) = -g z) (z : ℂ) :
    segmentPrimitive g (-z) = segmentPrimitive g z := by
  unfold segmentPrimitive
  simp only [mul_neg, hg, intervalIntegral.integral_neg, neg_mul, neg_neg]

theorem hardyStripPotential_conj (z : ℂ) :
    hardyStripPotential (conj z) = conj (hardyStripPotential z) := by
  have hg : ∀ z, hardyStripSecant (conj z) = conj (hardyStripSecant z) := by
    intro z
    unfold hardyStripSecant
    rw [show (Real.pi : ℂ) * conj z / 2 = conj ((Real.pi : ℂ) * z / 2) by
        simp only [map_div₀, map_mul, Complex.conj_ofReal, map_ofNat],
      Complex.cos_conj]
    simp
  rw [hardyStripPotential, segmentPrimitive_conj (segmentPrimitive_conj hg)]
  simp [hardyStripPotential]

theorem hardyStripPotential_even (z : ℂ) :
    hardyStripPotential (-z) = hardyStripPotential z := by
  have hg : ∀ z, hardyStripSecant (-z) = hardyStripSecant z := by
    intro z
    simp [hardyStripSecant, mul_neg, neg_div, Complex.cos_neg]
  unfold hardyStripPotential
  rw [segmentPrimitive_even_of_odd (segmentPrimitive_odd_of_even hg)]

theorem hardyStripRealPotential_even_y (x y : ℝ) :
    hardyStripRealPotential x (-y) = hardyStripRealPotential x y := by
  unfold hardyStripRealPotential
  have he : (x : ℂ) + Complex.I * (-y : ℝ) = conj ((x : ℂ) + Complex.I * y) := by simp
  rw [he, hardyStripPotential_conj, Complex.conj_re]

theorem hardyStripRealPotential_even_x (x y : ℝ) :
    hardyStripRealPotential (-x) y = hardyStripRealPotential x y := by
  unfold hardyStripRealPotential
  have he : (-x : ℝ) + Complex.I * (y : ℂ) = -conj ((x : ℂ) + Complex.I * y) := by
    push_cast
    simp [add_comm]
  rw [he, hardyStripPotential_even, hardyStripPotential_conj, Complex.conj_re]

end
end CGLMPBounds.Hardy
