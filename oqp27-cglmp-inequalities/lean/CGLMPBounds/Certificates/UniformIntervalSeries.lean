module

public import Mathlib.Analysis.Normed.Group.FunctionSeries
public import Mathlib.MeasureTheory.Integral.DominatedConvergence
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
public import Mathlib.Topology.Algebra.InfiniteSum.Ring

@[expose] public section


/-!
# Uniformly dominated real series on the unit interval

The hypotheses concern only `[0,1]`. No global continuity or global
integrability is imposed on the terms. A summable bound for their norms gives
pointwise summability, continuity of the sum, and interchange with the actual
Lebesgue interval integral.

Reuse: `continuousOn_tsum` supplies continuity, the unit-interval norm estimate
bounds each integral of a term's norm, and
`MeasureTheory.hasSum_integral_of_summable_integral_norm` supplies the integral
identity on `volume.restrict (Ioc 0 1)`. The weighted version applies exactly the
same argument with majorant `M * u i`.

This file is independent of the scalar-specific definitions and certificates.
-/

namespace CGLMPBounds.Certificates

open MeasureTheory Set

noncomputable section

/-- The uniform bound gives actual summability at every point of `[0,1]`. -/
theorem uniform_interval_summable (f : ℕ → ℝ → ℝ) (u : ℕ → ℝ)
    (hu : Summable u)
    (hfu : ∀ i x, x ∈ Icc (0 : ℝ) 1 → ‖f i x‖ ≤ u i)
    (x : ℝ) (hx : x ∈ Icc (0 : ℝ) 1) :
    Summable (fun i => f i x) :=
  hu.of_norm_bounded fun i => hfu i x hx

/-- A uniformly dominated series of continuous terms is continuous on `[0,1]`. -/
theorem uniform_interval_continuousOn (f : ℕ → ℝ → ℝ) (u : ℕ → ℝ)
    (hf : ∀ i, ContinuousOn (f i) (Icc (0 : ℝ) 1))
    (hu : Summable u)
    (hfu : ∀ i x, x ∈ Icc (0 : ℝ) 1 → ‖f i x‖ ≤ u i) :
    ContinuousOn (fun x => ∑' i, f i x) (Icc (0 : ℝ) 1) :=
  continuousOn_tsum hf hu hfu

/-- The sum is integrable with respect to volume restricted to `[0,1]`. -/
theorem uniform_interval_integrableOn (f : ℕ → ℝ → ℝ) (u : ℕ → ℝ)
    (hf : ∀ i, ContinuousOn (f i) (Icc (0 : ℝ) 1))
    (hu : Summable u)
    (hfu : ∀ i x, x ∈ Icc (0 : ℝ) 1 → ‖f i x‖ ≤ u i) :
    IntegrableOn (fun x => ∑' i, f i x) (Icc (0 : ℝ) 1) :=
  (uniform_interval_continuousOn f u hf hu hfu).integrableOn_Icc

/-- The sum is interval integrable from zero to one. -/
theorem uniform_interval_intervalIntegrable (f : ℕ → ℝ → ℝ) (u : ℕ → ℝ)
    (hf : ∀ i, ContinuousOn (f i) (Icc (0 : ℝ) 1))
    (hu : Summable u)
    (hfu : ∀ i x, x ∈ Icc (0 : ℝ) 1 → ‖f i x‖ ≤ u i) :
    IntervalIntegrable (fun x => ∑' i, f i x) volume 0 1 :=
  ContinuousOn.intervalIntegrable_of_Icc zero_le_one
    (uniform_interval_continuousOn f u hf hu hfu)

/-- The same majorant controls the integrals of the norms, since the interval
has length one. This estimate does not require continuity of the terms. -/
theorem uniform_interval_summable_integral_norm (f : ℕ → ℝ → ℝ) (u : ℕ → ℝ)
    (hu : Summable u)
    (hfu : ∀ i x, x ∈ Icc (0 : ℝ) 1 → ‖f i x‖ ≤ u i) :
    Summable (fun i => ∫ x in (0 : ℝ)..1, ‖f i x‖) := by
  apply hu.of_norm_bounded
  intro i
  have hbound := intervalIntegral.norm_integral_le_of_norm_le_const
    (a := (0 : ℝ)) (b := 1) (C := u i) (f := fun x => ‖f i x‖) (by
      intro x hx
      rw [uIoc_of_le (show (0 : ℝ) ≤ 1 from zero_le_one)] at hx
      simpa only [norm_norm] using hfu i x ⟨hx.1.le, hx.2⟩)
  simpa only [sub_zero, abs_one, mul_one] using hbound

/-- The series of term integrals converges to the integral of the series.
This is a `HasSum` assertion, not just an equality of totalized sums. -/
theorem uniform_interval_hasSum (f : ℕ → ℝ → ℝ) (u : ℕ → ℝ)
    (hf : ∀ i, ContinuousOn (f i) (Icc (0 : ℝ) 1))
    (hu : Summable u)
    (hfu : ∀ i x, x ∈ Icc (0 : ℝ) 1 → ‖f i x‖ ≤ u i) :
    HasSum (fun i => ∫ x in (0 : ℝ)..1, f i x)
      (∫ x in (0 : ℝ)..1, ∑' i, f i x) := by
  have hint : ∀ i, Integrable (f i) (volume.restrict (Ioc (0 : ℝ) 1)) := by
    intro i
    exact (ContinuousOn.intervalIntegrable_of_Icc
      (μ := volume) zero_le_one (hf i)).1
  have hnorm : Summable (fun i => ∫ x in Ioc (0 : ℝ) 1, ‖f i x‖) := by
    simpa only [intervalIntegral.integral_of_le
      (show (0 : ℝ) ≤ 1 from zero_le_one)] using
      uniform_interval_summable_integral_norm f u hu hfu
  have hsum := MeasureTheory.hasSum_integral_of_summable_integral_norm
    (μ := volume.restrict (Ioc (0 : ℝ) 1)) (F := f) hint hnorm
  simpa only [intervalIntegral.integral_of_le
    (show (0 : ℝ) ≤ 1 from zero_le_one)] using hsum

/-- Interchange the actual interval integral and the infinite series. -/
theorem uniform_interval_integral_tsum (f : ℕ → ℝ → ℝ) (u : ℕ → ℝ)
    (hf : ∀ i, ContinuousOn (f i) (Icc (0 : ℝ) 1))
    (hu : Summable u)
    (hfu : ∀ i x, x ∈ Icc (0 : ℝ) 1 → ‖f i x‖ ≤ u i) :
    (∫ x in (0 : ℝ)..1, ∑' i, f i x) =
      ∑' i, ∫ x in (0 : ℝ)..1, f i x :=
  (uniform_interval_hasSum f u hf hu hfu).tsum_eq.symm

/-- Multiplication by a continuous weight preserves interval integrability of
the sum. No explicit bound for the weight is needed for this conclusion. -/
theorem uniform_interval_weighted_intervalIntegrable
    (f : ℕ → ℝ → ℝ) (u : ℕ → ℝ) (w : ℝ → ℝ)
    (hf : ∀ i, ContinuousOn (f i) (Icc (0 : ℝ) 1))
    (hu : Summable u)
    (hfu : ∀ i x, x ∈ Icc (0 : ℝ) 1 → ‖f i x‖ ≤ u i)
    (hw : ContinuousOn w (Icc (0 : ℝ) 1)) :
    IntervalIntegrable (fun x => w x * ∑' i, f i x) volume 0 1 :=
  ContinuousOn.intervalIntegrable_of_Icc zero_le_one
    (hw.mul (uniform_interval_continuousOn f u hf hu hfu))

/-- Weighted series-to-integral interchange. The explicit bound is useful for
polynomial beta weights. Its nonnegativity follows from the bound at zero. -/
theorem uniform_interval_weighted_hasSum
    (f : ℕ → ℝ → ℝ) (u : ℕ → ℝ) (w : ℝ → ℝ) (M : ℝ)
    (hf : ∀ i, ContinuousOn (f i) (Icc (0 : ℝ) 1))
    (hu : Summable u)
    (hfu : ∀ i x, x ∈ Icc (0 : ℝ) 1 → ‖f i x‖ ≤ u i)
    (hw : ContinuousOn w (Icc (0 : ℝ) 1))
    (hwM : ∀ x, x ∈ Icc (0 : ℝ) 1 → ‖w x‖ ≤ M) :
    HasSum (fun i => ∫ x in (0 : ℝ)..1, w x * f i x)
      (∫ x in (0 : ℝ)..1, w x * ∑' i, f i x) := by
  have hM : 0 ≤ M :=
    (norm_nonneg (w 0)).trans (hwM 0 ⟨le_rfl, zero_le_one⟩)
  have hbound : ∀ i x, x ∈ Icc (0 : ℝ) 1 → ‖w x * f i x‖ ≤ M * u i := by
    intro i x hx
    rw [norm_mul]
    exact mul_le_mul (hwM x hx) (hfu i x hx) (norm_nonneg (f i x)) hM
  have hsum := uniform_interval_hasSum
    (fun i x => w x * f i x) (fun i => M * u i)
    (fun i => hw.mul (hf i)) (hu.mul_left M) hbound
  simpa only [tsum_mul_left] using hsum

/-- The weighted integral identity with the integral on the left. -/
theorem uniform_interval_weighted_integral_tsum
    (f : ℕ → ℝ → ℝ) (u : ℕ → ℝ) (w : ℝ → ℝ) (M : ℝ)
    (hf : ∀ i, ContinuousOn (f i) (Icc (0 : ℝ) 1))
    (hu : Summable u)
    (hfu : ∀ i x, x ∈ Icc (0 : ℝ) 1 → ‖f i x‖ ≤ u i)
    (hw : ContinuousOn w (Icc (0 : ℝ) 1))
    (hwM : ∀ x, x ∈ Icc (0 : ℝ) 1 → ‖w x‖ ≤ M) :
    (∫ x in (0 : ℝ)..1, w x * ∑' i, f i x) =
      ∑' i, ∫ x in (0 : ℝ)..1, w x * f i x :=
  (uniform_interval_weighted_hasSum f u w M hf hu hfu hw hwM).tsum_eq.symm

end

end CGLMPBounds.Certificates
