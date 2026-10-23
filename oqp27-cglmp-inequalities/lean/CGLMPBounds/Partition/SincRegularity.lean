module

public import Mathlib

@[expose] public section


/-! A reusable analytic prerequisite for the removable point in D.5.
Mathlib's literal real sinc is analytic at zero via the divided-difference
power series and away from zero via its quotient formula. -/

namespace CGLMPBounds.Partition
open Filter
open scoped Topology
noncomputable section

theorem analyticAt_real_sinc (x : ℝ) : AnalyticAt ℝ Real.sinc x := by
  by_cases hx : x = 0
  · subst x
    rw [Real.sinc_eq_dslope]
    rcases (Real.analyticAt_sin : AnalyticAt ℝ Real.sin (0 : ℝ)) with ⟨p, hp⟩
    exact ⟨p.fslope, hp.has_fpower_series_dslope_fslope⟩
  · have hquot : AnalyticAt ℝ (fun y : ℝ => Real.sin y / y) x :=
      Real.analyticAt_sin.div analyticAt_id hx
    apply hquot.congr
    filter_upwards [eventually_ne_nhds hx] with y hy
    exact (Real.sinc_of_ne_zero hy).symm

theorem contDiff_real_sinc : ContDiff ℝ ⊤ Real.sinc := by
  rw [contDiff_iff_contDiffAt]
  exact fun x => (analyticAt_real_sinc x).contDiffAt

end
end CGLMPBounds.Partition
