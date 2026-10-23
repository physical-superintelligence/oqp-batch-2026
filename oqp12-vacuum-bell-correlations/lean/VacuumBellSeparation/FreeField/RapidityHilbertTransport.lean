module

public import VacuumBellSeparation.FreeField.RapidityJacobian
public import VacuumBellSeparation.FreeField.ShellBoostMeasure

@[expose] public section


/-!
# Exact Hilbert transport to rapidity coordinates

The target measure is explicitly [2(2π)^3]⁻¹ times three-dimensional
Lebesgue measure. Thus the unitary is literal pullback, with no omitted
normalizing factor. No statement here identifies the modular operator.
-/

namespace VacuumBellSeparation

open MeasureTheory

noncomputable abbrev RapidityL2 := Lp ℂ 2 rapidityMeasure

theorem measurePreserving_momentumRapidity {m : ℝ} (hm : 0 < m) :
    MeasurePreserving (momentumRapidity m) (oneParticleMeasure m) rapidityMeasure :=
  MeasurePreserving.symm (rapidityHomeomorph hm).toMeasurableEquiv
    (measurePreserving_rapidityMomentum hm)

noncomputable def rapidityPullback {m : ℝ} (hm : 0 < m) :
    Lp ℂ 2 (oneParticleMeasure m) →ₗᵢ[ℂ] RapidityL2 :=
  Lp.compMeasurePreservingₗᵢ ℂ (rapidityMomentum m) (measurePreserving_rapidityMomentum hm)

noncomputable def momentumPullback {m : ℝ} (hm : 0 < m) :
    RapidityL2 →ₗᵢ[ℂ] Lp ℂ 2 (oneParticleMeasure m) :=
  Lp.compMeasurePreservingₗᵢ ℂ (momentumRapidity m) (measurePreserving_momentumRapidity hm)

theorem rapidityPullback_momentumPullback {m : ℝ} (hm : 0 < m) (ψ : RapidityL2) :
    rapidityPullback hm (momentumPullback hm ψ) = ψ := by
  change Lp.compMeasurePreserving (rapidityMomentum m) _
    (Lp.compMeasurePreserving (momentumRapidity m) _ ψ) = ψ
  rw [← Lp.compMeasurePreserving_comp_apply]
  have he : momentumRapidity m ∘ rapidityMomentum m = id :=
    funext (momentumRapidity_rapidityMomentum hm)
  simp only [he, Lp.compMeasurePreserving_id_apply]

/-- The actual full one-particle Hilbert space in rapidity coordinates. -/
noncomputable def rapidityUnitary {m : ℝ} (hm : 0 < m) :
    Lp ℂ 2 (oneParticleMeasure m) ≃ₗᵢ[ℂ] RapidityL2 :=
  LinearIsometryEquiv.ofSurjective (rapidityPullback hm)
    (fun ψ => ⟨momentumPullback hm ψ, rapidityPullback_momentumPullback hm ψ⟩)

theorem rapidityUnitary_ae {m : ℝ} (hm : 0 < m) (ψ : Lp ℂ 2 (oneParticleMeasure m)) :
    rapidityUnitary hm ψ =ᵐ[rapidityMeasure] ψ ∘ rapidityMomentum m :=
  Lp.coeFn_compMeasurePreserving ψ (measurePreserving_rapidityMomentum hm)

/-- The inverse-label physical boost becomes translation by negative rapidity. -/
theorem rapidityUnitary_boost_ae {m : ℝ} (hm : 0 < m) (η : ℝ)
    (ψ : Lp ℂ 2 (oneParticleMeasure m)) :
    rapidityUnitary hm (oneParticleBoost hm η ψ) =ᵐ[rapidityMeasure]
      fun x => ψ (rapidityMomentum m (rapidityTranslate (-η) x)) := by
  have hcomp := (measurePreserving_rapidityMomentum hm).quasiMeasurePreserving.ae_eq_comp
    (oneParticleBoostIsometry_ae hm η ψ)
  filter_upwards [rapidityUnitary_ae hm (oneParticleBoost hm η ψ), hcomp] with x hx hx'
  rw [hx]
  change oneParticleBoostIsometry hm η ψ (rapidityMomentum m x) = _
  dsimp only [Function.comp_apply] at hx'
  rw [hx']
  exact congrArg ψ (shellBoost_rapidityMomentum hm (-η) x)

end VacuumBellSeparation
