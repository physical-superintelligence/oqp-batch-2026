module

public import CGLMPBounds.Hardy.DensityContinuity
public import CGLMPBounds.Hardy.Support

@[expose] public section


/-!
# Genuine integrability of all trace-density moments

Continuity and the exact compact spectral support give Lebesgue integrability.
-/

namespace CGLMPBounds.Hardy
noncomputable section
open MeasureTheory

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem traceDensity_moment_integrable {H Y : Matrix ι ι ℂ}
    (hH : H.IsHermitian) (hY : Y.IsHermitian) (hdet : IsUnit H.det) (m : ℕ) :
    Integrable (fun y : ℝ => y ^ m * traceDensity H Y y) volume := by
  have hc : Continuous (fun y : ℝ => y ^ m * traceDensity H Y y) :=
    (continuous_id.pow m).mul (continuous_traceDensity H Y)
  have hs : HasCompactSupport (fun y : ℝ => y ^ m * traceDensity H Y y) :=
    (traceDensity_hasCompactSupport hH hY hdet).mul_left
  exact hc.integrable_of_hasCompactSupport hs

theorem traceDensity_integrable {H Y : Matrix ι ι ℂ}
    (hH : H.IsHermitian) (hY : Y.IsHermitian) (hdet : IsUnit H.det) :
    Integrable (traceDensity H Y) volume := by
  simpa only [pow_zero, one_mul] using traceDensity_moment_integrable hH hY hdet 0

end
end CGLMPBounds.Hardy
