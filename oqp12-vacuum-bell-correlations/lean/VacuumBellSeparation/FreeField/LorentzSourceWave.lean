module

public import VacuumBellSeparation.FreeField.ComplexSourceCurve
public import VacuumBellSeparation.FreeField.TimeZeroRapidityWave
public import VacuumBellSeparation.FreeField.OneParticleLorentz

@[expose] public section


/-!
# Actual Cauchy-data waves on Lorentz-transformed boost contours

Physical L2 equality first gives pointwise equality of the continuous real
mass-shell waves. Real Lorentz covariance then identifies the real-rapidity
values, and the genuine entire-function identity theorem proves the full
complex contour identity. No pointwise evaluation of an L2 class is used.
-/

namespace VacuumBellSeparation

open MeasureTheory
open scoped InnerProductSpace

theorem complexShellBoost_ofReal (m η : ℝ) (p : EuclideanSpace ℝ (Fin 3)) :
    complexShellBoost m (η : ℂ) p = complexSpacetimeOfReal (onShell m (shellBoost m η p)) := by
  apply Prod.ext
  · exact complexShellBoost_energy_ofReal m η p
  · ext i
    fin_cases i <;>
      simp [complexShellBoost, complexSpacetimeOfReal, onShell, shellBoost, e₁,
        ← Complex.ofReal_cosh, ← Complex.ofReal_sinh,
        EuclideanSpace.inner_single_left] <;> push_cast <;> ring

theorem complexified_lorentzBoost_ofReal (m η : ℝ)
    (Λ : Spacetime ≃L[ℝ] Spacetime) (hΛ : IsLorentzMap Λ)
    (hfuture : IsOrthochronousMap Λ) (p : EuclideanSpace ℝ (Fin 3)) :
    complexifiedSpacetimeMap Λ (complexShellBoost m (η : ℂ) p) =
      complexSpacetimeOfReal (onShell m (lorentzShellMap m Λ (shellBoost m η p))) := by
  rw [complexShellBoost_ofReal, complexifiedSpacetimeMap_ofReal,
    lorentzMap_onShell m Λ hΛ hfuture]

theorem oneParticle_eq_timeZero_of_L2_eq {m : ℝ} (hm : 0 < m)
    (F : RealTestFunction) (u : TimeZeroSource) (heq : oneParticleL2 hm F = timeZeroL2 hm u) :
    oneParticle m F = timeZeroOneParticle m u := by
  have hae : oneParticle m F =ᵐ[oneParticleMeasure m] timeZeroOneParticle m u := by
    have hF := coeFn_oneParticleL2 hm F
    rw [heq] at hF
    exact hF.symm.trans (coeFn_timeZeroL2 hm u)
  exact Measure.eq_of_ae_eq ((ae_oneParticleMeasure_iff hm).mp hae)
    (continuous_oneParticle m F) (continuous_timeZeroOneParticle m u)

/-- The Lorentz-transformed source-wave identity holds at every complex
rapidity, for the original literal Cauchy-data integral. -/
theorem wedgeWave_compLorentz_eq_complexSourceWave {m : ℝ} (hm : 0 < m)
    (Λ : Spacetime ≃L[ℝ] Spacetime) (hΛ : IsLorentzMap Λ)
    (hfuture : IsOrthochronousMap Λ)
    (F : RealTestFunction) (u : TimeZeroSource) (heq : oneParticleL2 hm F = timeZeroL2 hm u)
    (ζ : ℂ) (p : EuclideanSpace ℝ (Fin 3)) :
    wedgeWave m (F.compCLE Λ) ζ p =
      complexSourceWave u (complexifiedSpacetimeMap Λ (complexShellBoost m ζ p)) := by
  have hreal := oneParticle_eq_timeZero_of_L2_eq hm F u heq
  have hall := entire_eq_of_real_eq (analyticOnNhd_wedgeWave m (F.compCLE Λ) p)
    (analyticOnNhd_complexSourceWave_lorentzBoost m Λ u p) (fun η => by
      rw [wedgeWave_ofReal, oneParticle_lorentzMap m Λ hΛ hfuture,
        complexified_lorentzBoost_ofReal m η Λ hΛ hfuture, hreal]
      exact (complexSourceWave_onShell m u _).symm)
  exact congrFun hall ζ

end VacuumBellSeparation
