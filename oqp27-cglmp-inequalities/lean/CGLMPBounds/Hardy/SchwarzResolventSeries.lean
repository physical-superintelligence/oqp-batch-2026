module

public import CGLMPBounds.Hardy.Resolvent
public import Mathlib.Analysis.Analytic.OfScalars
public import Mathlib.Analysis.Analytic.Uniqueness
public import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
public import Mathlib.Analysis.Normed.Algebra.Spectrum

@[expose] public section


/-!
# Genuine affine resolvent coefficients toward (C.7)

At an actual resolvent point lambda of H, the inverse of lambda*I-H-t*Y
has the convergent noncommutative geometric expansion
sum_n t^n * (R_H(lambda)*Y)^n * R_H(lambda).
The multiplication order is retained throughout. The trace coefficients are
actual complex derivatives divided by factorials, identified by power-series
uniqueness. No log-determinant, residue or contour coefficient oracle is assumed.

This is a narrow local analytic ingredient of the source p.9 argument, not
the remaining positive-cluster coefficient identity of (C.7).
-/

open Complex Matrix Filter
open scoped Topology Matrix.Norms.Operator

namespace CGLMPBounds.Hardy
noncomputable section
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
attribute [-instance] CStarMatrix.instHMulOfFintypeOfMulOfAddCommMonoid

lemma hasSum_affine_resolvent (H Y : Matrix ι ι ℂ) {ξ t : ℂ}
    (hξ : ξ ∉ spectrum ℂ H)
    (ht : ‖t • (resolvent H ξ * Y)‖ < 1) :
    HasSum (fun n : ℕ => t ^ n • ((resolvent H ξ * Y) ^ n * resolvent H ξ))
      (resolvent (H + t • Y) ξ) := by
  let P : Matrix ι ι ℂ := algebraMap ℂ (Matrix ι ι ℂ) ξ - H
  have hu : IsUnit P := by
    simpa only [P, spectrum.mem_iff, not_not] using hξ
  have hfac : P * (1 - t • (Ring.inverse P * Y)) = P - t • Y := by
    rw [mul_sub, mul_one, mul_smul_comm, ← mul_assoc,
      Ring.mul_inverse_cancel _ hu, one_mul]
  have hg := hasSum_geom_series_inverse (t • (Ring.inverse P * Y)) ht
  have hm := hg.mul_right (Ring.inverse P)
  change HasSum (fun n : ℕ => t ^ n • ((Ring.inverse P * Y) ^ n * Ring.inverse P))
    (Ring.inverse (algebraMap ℂ (Matrix ι ι ℂ) ξ - (H + t • Y)))
  rw [sub_add_eq_sub_sub]
  change HasSum _ (Ring.inverse (P - t • Y))
  rw [← hfac, Ring.inverse_mul (Or.inl hu)]
  -- The geometric-series theorem uses the normed-ring topology. Recover the
  -- statement's product topology through actual continuous entry evaluations.
  apply Pi.hasSum.mpr
  intro i
  apply Pi.hasSum.mpr
  intro j
  letI : TopologicalSpace (Matrix ι ι ℂ) :=
    (Matrix.linftyOpNormedRing : NormedRing (Matrix ι ι ℂ)).toUniformSpace.toTopologicalSpace
  let ev : Matrix ι ι ℂ →ₗ[ℂ] ℂ :=
    { toFun := fun M => M i j
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  let evc : Matrix ι ι ℂ →L[ℂ] ℂ := ev.toContinuousLinearMap
  have hij := hm.map evc evc.continuous
  change HasSum
    (fun n : ℕ => ((t • (Ring.inverse P * Y)) ^ n * Ring.inverse P) i j)
    ((Ring.inverse (1 - t • (Ring.inverse P * Y)) * Ring.inverse P) i j) at hij
  simpa only [smul_pow, smul_mul_assoc] using hij

/-- A genuine neighborhood exists without requiring an explicit bound as a
source hypothesis. The only matrix condition is that lambda lies off spectrum. -/
theorem eventually_hasSum_affine_resolvent (H Y : Matrix ι ι ℂ) {ξ : ℂ}
    (hξ : ξ ∉ spectrum ℂ H) :
    ∀ᶠ t : ℂ in 𝓝 0,
      HasSum (fun n : ℕ => t ^ n • ((resolvent H ξ * Y) ^ n * resolvent H ξ))
        (resolvent (H + t • Y) ξ) := by
  have hc : ContinuousAt (fun t : ℂ => ‖t • (resolvent H ξ * Y)‖) 0 := by fun_prop
  have he : ∀ᶠ t : ℂ in 𝓝 0, ‖t • (resolvent H ξ * Y)‖ < 1 :=
    hc.eventually_lt continuousAt_const (by simp)
  filter_upwards [he] with t ht
  exact hasSum_affine_resolvent H Y hξ ht

/-- Taking the continuous matrix trace preserves the convergent series. -/
theorem eventually_hasSum_trace_affine_resolvent (H Y : Matrix ι ι ℂ) {ξ : ℂ}
    (hξ : ξ ∉ spectrum ℂ H) :
    ∀ᶠ t : ℂ in 𝓝 0,
      HasSum (fun n : ℕ => Matrix.trace ((resolvent H ξ * Y) ^ n * resolvent H ξ) * t ^ n)
        (Matrix.trace (resolvent (H + t • Y) ξ)) := by
  let tr : Matrix ι ι ℂ →L[ℂ] ℂ := (Matrix.traceLinearMap ι ℂ ℂ).toContinuousLinearMap
  filter_upwards [eventually_hasSum_affine_resolvent H Y hξ] with t ht
  have hs := ht.map tr tr.continuous
  change HasSum
    (fun n : ℕ => Matrix.trace (t ^ n • ((resolvent H ξ * Y) ^ n * resolvent H ξ)))
    (Matrix.trace (resolvent (H + t • Y) ξ)) at hs
  simpa only [Matrix.trace_smul, smul_eq_mul, mul_comm] using hs

theorem hasFPowerSeriesAt_trace_affine_resolvent (H Y : Matrix ι ι ℂ) {ξ : ℂ}
    (hξ : ξ ∉ spectrum ℂ H) :
    HasFPowerSeriesAt (fun t : ℂ => Matrix.trace (resolvent (H + t • Y) ξ))
      (FormalMultilinearSeries.ofScalars ℂ
        (fun n => Matrix.trace ((resolvent H ξ * Y) ^ n * resolvent H ξ))) 0 := by
  apply hasFPowerSeriesAt_iff.mpr
  filter_upwards [eventually_hasSum_trace_affine_resolvent H Y hξ] with t ht
  simpa only [FormalMultilinearSeries.coeff_ofScalars, smul_eq_mul, zero_add, mul_comm] using ht

/-- Literal derivative/factorial coefficient of the affine resolvent trace.
No commutation assumption on H and Y is needed or introduced. -/
theorem trace_affine_resolvent_taylor_coefficient (H Y : Matrix ι ι ℂ) {ξ : ℂ}
    (hξ : ξ ∉ spectrum ℂ H) (n : ℕ) :
    iteratedDeriv n (fun t : ℂ => Matrix.trace (resolvent (H + t • Y) ξ)) 0 /
        (n.factorial : ℂ) =
      Matrix.trace ((resolvent H ξ * Y) ^ n * resolvent H ξ) := by
  have hp := hasFPowerSeriesAt_trace_affine_resolvent H Y hξ
  have he := hp.analyticAt.hasFPowerSeriesAt.eq_formalMultilinearSeries hp
  simpa only [FormalMultilinearSeries.coeff_ofScalars] using
    congrArg (fun p : FormalMultilinearSeries ℂ ℂ ℂ => p.coeff n) he

end
end CGLMPBounds.Hardy
