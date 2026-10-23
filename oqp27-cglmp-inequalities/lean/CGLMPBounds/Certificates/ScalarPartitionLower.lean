module

public import CGLMPBounds.Defs.ScalarPartition
public import CGLMPBounds.Certificates.ScalarCotangent
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds

@[expose] public section


/-!
# The lower bound S(x) >= 1/3 in (D.8)

The first positive cotangent-series coefficient suffices. Integrating this
pointwise bound requires a separate continuity/integrability proof at the
removable central value; no such integrability is assumed here.
-/

namespace CGLMPBounds.Certificates

theorem cotangent_numerator_lower {t : ℝ} (ht : t ∈ Set.Ioo (0 : ℝ) Real.pi) :
    t ^ 2 / 3 ≤ 1 - t * Real.cot t := by
  have hx : t / Real.pi ∈ Set.Ioo (0 : ℝ) 1 :=
    ⟨div_pos ht.1 Real.pi_pos, (div_lt_one Real.pi_pos).2 ht.2⟩
  have hx0 : 0 ≤ t / Real.pi := hx.1.le
  have hs := cotangent_power_hasSum hx
  have hf := hs.summable.le_tsum 0 (by
    intro j _
    apply mul_nonneg (pow_nonneg hx0 _)
    apply tsum_nonneg
    intro n
    positivity)
  rw [hs.tsum_eq] at hf
  norm_num only [Nat.mul_zero, Nat.zero_add, pow_one, Nat.mul_one] at hf
  rw [hasSum_zeta_two.tsum_eq] at hf
  have harg : Real.pi * (t / Real.pi) = t := by field_simp [Real.pi_ne_zero]
  rw [harg] at hf
  have hm := mul_le_mul_of_nonneg_left hf (show 0 ≤ 2 * (t / Real.pi) by positivity)
  convert hm using 1 <;> field_simp [Real.pi_ne_zero, ht.1.ne'] <;> ring

theorem scalarCotangentRemainder_even (t : ℝ) :
    scalarCotangentRemainder (-t) = scalarCotangentRemainder t := by
  by_cases ht : t = 0
  · subst t; simp
  · simp only [scalarCotangentRemainder, if_neg ht, if_neg (neg_ne_zero.mpr ht),
      Real.cot_eq_cos_div_sin, Real.cos_neg, Real.sin_neg, div_neg, neg_mul_neg, neg_sq]

theorem scalarCotangentRemainder_lower_pos {t : ℝ}
    (ht : t ∈ Set.Ioo (0 : ℝ) Real.pi) : (1 / 3 : ℝ) ≤ scalarCotangentRemainder t := by
  rw [scalarCotangentRemainder, if_neg ht.1.ne']
  have hs : 0 < Real.sin t ^ 2 :=
    sq_pos_of_pos (Real.sin_pos_of_pos_of_lt_pi ht.1 ht.2)
  apply (le_div_iff₀ hs).2
  have hn := cotangent_numerator_lower ht
  have hb := Real.sin_sq_le_sq (x := t)
  nlinarith

theorem scalarCotangentRemainder_lower {t : ℝ} (ht : |t| < Real.pi) :
    (1 / 3 : ℝ) ≤ scalarCotangentRemainder t := by
  rcases lt_trichotomy t 0 with hneg | hzero | hpos
  · have h := scalarCotangentRemainder_lower_pos
      (show -t ∈ Set.Ioo (0 : ℝ) Real.pi from
        ⟨by linarith, by simpa only [abs_of_neg hneg] using ht⟩)
    simpa only [scalarCotangentRemainder_even] using h
  · subst t; simp [scalarCotangentRemainder]
  · exact scalarCotangentRemainder_lower_pos
      ⟨hpos, by simpa only [abs_of_pos hpos] using ht⟩

theorem scalarPartitionS_lower {x : ℝ} (hx : x ∈ Set.Icc (0 : ℝ) 1) :
    (1 / 3 : ℝ) ≤ scalarPartitionS x := by
  apply scalarCotangentRemainder_lower
  have hp := Real.pi_pos
  apply abs_lt.2
  constructor <;> nlinarith [hx.1, hx.2]

theorem scalarPartitionS_reflect (x : ℝ) : scalarPartitionS (1 - x) = scalarPartitionS x := by
  unfold scalarPartitionS
  rw [show Real.pi / 2 * (1 - x - 1 / 2) = -(Real.pi / 2 * (x - 1 / 2)) by ring,
    scalarCotangentRemainder_even]

end CGLMPBounds.Certificates
