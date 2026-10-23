module

public import CGLMPBounds.Certificates.ScalarPartitionLower
public import CGLMPBounds.Certificates.BetaSeriesAlgebra
public import Mathlib.Analysis.Calculus.LHopital
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Sinc

@[expose] public section


/-!
# The removable value and the integrated lower bound in (D.8)

The definition uses the literal cotangent expression away from zero. Its value
at zero is justified by a punctured limit, not by an integrability hypothesis.
-/

open Filter Set
open scoped Topology

namespace CGLMPBounds.Certificates
noncomputable section

theorem partition_sin_ne_zero {t : ℝ} (ht : t ≠ 0) (hb : |t| < Real.pi) :
    Real.sin t ≠ 0 := by
  rcases lt_or_gt_of_ne ht with hneg | hpos
  · have hp : 0 < Real.sin (-t) := Real.sin_pos_of_pos_of_lt_pi (by linarith)
      (by simpa only [abs_of_neg hneg] using hb)
    rw [Real.sin_neg] at hp
    linarith
  · exact (Real.sin_pos_of_pos_of_lt_pi hpos
      (by simpa only [abs_of_pos hpos] using hb)).ne'

theorem scalarCotangentRemainder_continuousAt_zero :
    ContinuousAt scalarCotangentRemainder 0 := by
  have hne : ∀ᶠ t : ℝ in 𝓝[≠] 0, t ≠ 0 := by
    simpa using (eventually_mem_nhdsWithin : ∀ᶠ t : ℝ in 𝓝[≠] 0, t ∈ ({0}ᶜ : Set ℝ))
  have hsmall : ∀ᶠ t : ℝ in 𝓝[≠] 0,
      t ∈ Ioo (-(Real.pi / 2)) (Real.pi / 2) :=
    mem_nhdsWithin_of_mem_nhds
      (Ioo_mem_nhds (by linarith [Real.pi_pos]) (by positivity))
  have hsin : ∀ᶠ t : ℝ in 𝓝[≠] 0, Real.sin t ≠ 0 := by
    filter_upwards [hne, hsmall] with t ht hb
    apply partition_sin_ne_zero ht
    apply abs_lt.2
    constructor <;> linarith [hb.1, hb.2, Real.pi_pos]
  have hcos : ∀ᶠ t : ℝ in 𝓝[≠] 0, Real.cos t ≠ 0 := by
    filter_upwards [hsmall] with t ht
    exact (Real.cos_pos_of_mem_Ioo ht).ne'
  have hf : ∀ᶠ t : ℝ in 𝓝[≠] 0,
      HasDerivAt (fun u => Real.sin u - u * Real.cos u) (t * Real.sin t) t := by
    filter_upwards [] with t
    have h : HasDerivAt (fun u => Real.sin u - u * Real.cos u)
        (Real.cos t - (Real.cos t + t * (-Real.sin t))) t := by
      simpa only [id_eq, one_mul] using!
        (Real.hasDerivAt_sin t).sub ((hasDerivAt_id t).mul (Real.hasDerivAt_cos t))
    convert h using 1 <;> ring
  have hg : ∀ᶠ t : ℝ in 𝓝[≠] 0,
      HasDerivAt (fun u => Real.sin u ^ 3) (3 * Real.sin t ^ 2 * Real.cos t) t := by
    filter_upwards [] with t
    simpa using! (Real.hasDerivAt_sin t).pow 3
  have hg0 : ∀ᶠ t : ℝ in 𝓝[≠] 0, 3 * Real.sin t ^ 2 * Real.cos t ≠ 0 := by
    filter_upwards [hsin, hcos] with t hs hc
    exact mul_ne_zero (mul_ne_zero (by norm_num) (pow_ne_zero 2 hs)) hc
  have hf0 : Tendsto (fun t : ℝ => Real.sin t - t * Real.cos t) (𝓝[≠] 0) (𝓝 0) := by
    have hc : ContinuousAt (fun t : ℝ => Real.sin t - t * Real.cos t) 0 := by fun_prop
    simpa using hc.tendsto.mono_left nhdsWithin_le_nhds
  have hgzero : Tendsto (fun t : ℝ => Real.sin t ^ 3) (𝓝[≠] 0) (𝓝 0) := by
    have hc : ContinuousAt (fun t : ℝ => Real.sin t ^ 3) 0 := by fun_prop
    simpa using hc.tendsto.mono_left nhdsWithin_le_nhds
  have hratio : Tendsto (fun t : ℝ => t * Real.sin t /
      (3 * Real.sin t ^ 2 * Real.cos t)) (𝓝[≠] 0) (𝓝 (1 / 3 : ℝ)) := by
    have hc : ContinuousAt (fun t : ℝ => 1 / (3 * Real.sinc t * Real.cos t)) 0 := by
      apply continuousAt_const.div
      · exact (continuousAt_const.mul Real.continuous_sinc.continuousAt).mul
          Real.continuous_cos.continuousAt
      · norm_num
    have hl : Tendsto (fun t : ℝ => 1 / (3 * Real.sinc t * Real.cos t))
        (𝓝[≠] 0) (𝓝 (1 / 3 : ℝ)) := by
      simpa using hc.tendsto.mono_left nhdsWithin_le_nhds
    apply hl.congr'
    filter_upwards [hne, hsin, hcos] with t ht hs hc
    rw [Real.sinc_of_ne_zero ht]
    field_simp
  have hl := HasDerivAt.lhopital_zero_nhdsNE hf hg hg0 hf0 hgzero hratio
  rw [continuousAt_iff_punctured_nhds]
  simp only [scalarCotangentRemainder, if_pos rfl]
  apply hl.congr'
  filter_upwards [hne, hsin] with t ht hs
  rw [scalarCotangentRemainder, if_neg ht, Real.cot_eq_cos_div_sin]
  field_simp
  <;> ring

theorem scalarCotangentRemainder_continuousAt {t : ℝ} (ht : |t| < Real.pi) :
    ContinuousAt scalarCotangentRemainder t := by
  by_cases ht0 : t = 0
  · subst t
    exact scalarCotangentRemainder_continuousAt_zero
  · have hs := partition_sin_ne_zero ht0 ht
    have hc : ContinuousAt (fun u : ℝ =>
        (1 - u * (Real.cos u / Real.sin u)) / Real.sin u ^ 2) t := by
      apply ContinuousAt.div
      · exact continuousAt_const.sub (continuousAt_id.mul
          (Real.continuous_cos.continuousAt.div Real.continuous_sin.continuousAt hs))
      · exact Real.continuous_sin.continuousAt.pow 2
      · exact pow_ne_zero 2 hs
    apply hc.congr_of_eventuallyEq
    filter_upwards [isOpen_ne.mem_nhds ht0] with u hu
    simp only [scalarCotangentRemainder, if_neg hu, Real.cot_eq_cos_div_sin]

theorem scalarPartitionS_continuousOn : ContinuousOn scalarPartitionS (Icc (0 : ℝ) 1) := by
  intro x hx
  have hb : |Real.pi / 2 * (x - 1 / 2)| < Real.pi := by
    apply abs_lt.2
    constructor <;> nlinarith [hx.1, hx.2, Real.pi_pos]
  have hc : ContinuousAt (fun u : ℝ => Real.pi / 2 * (u - 1 / 2)) x := by
    fun_prop
  have hs : ContinuousAt scalarPartitionS x := by
    simpa only [scalarPartitionS, Function.comp_apply] using!
      (scalarCotangentRemainder_continuousAt hb).comp
        (f := fun u : ℝ => Real.pi / 2 * (u - 1 / 2)) (x := x) hc
  exact hs.continuousWithinAt

theorem scalarPartition_weight_intervalIntegrable (d h : ℕ) :
    IntervalIntegrable (fun x => scalarBinomialWeight d h x * scalarPartitionS x)
      MeasureTheory.volume 0 1 := by
  exact ((scalarBinomialWeight_continuous d h).continuousOn.mul
    scalarPartitionS_continuousOn).intervalIntegrable_of_Icc (by norm_num)

theorem scalarBinomialWeight_reflect (d h : ℕ) (hh : h ≤ d) (x : ℝ) :
    scalarBinomialWeight d h (1 - x) = scalarBinomialWeight d (d - h) x := by
  simp only [scalarBinomialWeight, Nat.choose_symm hh, Nat.sub_sub_self hh]
  rw [show 1 - (1 - x) = x by ring]
  ring

/-- Reflection holds for the actual beta transform, without regularity hypotheses
on g; the interval substitution is valid for the totalized Bochner integral. -/
theorem scalarBetaTransform_reflect (d h : ℕ) (hh : h ≤ d) (g : ℝ → ℝ) :
    scalarBetaTransform d h (fun x => g (1 - x)) =
      scalarBetaTransform d (d - h) g := by
  unfold scalarBetaTransform
  congr 1
  calc
    _ = ∫ x in (0 : ℝ)..1,
        scalarBinomialWeight d (d - h) (1 - x) * g (1 - x) := by
      apply intervalIntegral.integral_congr
      intro x _
      dsimp only
      rw [scalarBinomialWeight_reflect d (d - h) (Nat.sub_le _ _), Nat.sub_sub_self hh]
    _ = _ := by
      simpa using intervalIntegral.integral_comp_sub_left
        (fun x => scalarBinomialWeight d (d - h) x * g x) (a := (0 : ℝ)) (b := 1) 1

theorem scalarPartitionCoefficient_reflect (d h : ℕ) (hh : h ≤ d) :
    scalarPartitionCoefficient d h = scalarPartitionCoefficient d (d - h) := by
  unfold scalarPartitionCoefficient
  congr 1
  calc
    _ = scalarBetaTransform d h (fun x => scalarPartitionS (1 - x)) := by
      simp_rw [scalarPartitionS_reflect]
    _ = _ := scalarBetaTransform_reflect d h hh scalarPartitionS

/-- The actual beta-integral coefficient, with the source normalization. -/
theorem scalarPartitionCoefficient_lower (d h : ℕ) (hd : 0 < d) (hh : h ≤ d) :
    1 / (3 * ((d : ℝ) + 1)) ≤ scalarPartitionCoefficient d h := by
  have hd0 : (0 : ℝ) < d := by exact_mod_cast hd
  have hi : scalarBetaTransform d h (fun _ => (1 / 3 : ℝ)) ≤
      scalarBetaTransform d h scalarPartitionS := by
    unfold scalarBetaTransform
    apply mul_le_mul_of_nonneg_left _ hd0.le
    apply intervalIntegral.integral_mono_on (by norm_num)
    · apply Continuous.intervalIntegrable
      exact (scalarBinomialWeight_continuous d h).mul continuous_const
    · exact scalarPartition_weight_intervalIntegrable d h
    · intro x hx
      apply mul_le_mul_of_nonneg_left (scalarPartitionS_lower hx)
      unfold scalarBinomialWeight
      have hx0 : 0 ≤ x := hx.1
      have hx1 : 0 ≤ 1 - x := by linarith [hx.2]
      positivity
  have hv : scalarBetaTransform d h (fun _ => (1 / 3 : ℝ)) =
      (1 / 3 : ℝ) * ((d : ℝ) / ((d : ℝ) + 1)) := by
    calc
      _ = scalarBetaTransform d h (fun _ => (1 / 3 : ℝ) * 1) := by simp only [mul_one]
      _ = (1 / 3 : ℝ) * scalarBetaTransform d h (fun _ => 1) :=
        scalarBetaTransform_const_mul d h (1 / 3) (fun _ => 1)
      _ = _ := by rw [scalarBetaTransform_one d h hh]
  rw [hv] at hi
  unfold scalarPartitionCoefficient
  apply (le_div_iff₀ hd0).2
  convert hi using 1 <;> field_simp <;> ring

end
end CGLMPBounds.Certificates
