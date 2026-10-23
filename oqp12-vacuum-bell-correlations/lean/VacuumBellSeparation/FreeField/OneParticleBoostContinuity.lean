module

public import VacuumBellSeparation.FreeField.ShellBoostMeasure
public import Mathlib.MeasureTheory.Function.LpSpace.ContinuousCompMeasurePreserving

@[expose] public section


/-!
# The actual strongly continuous one-particle boost group

Local finiteness follows from the continuous physical density. Pinned
Lp pullback continuity then gives strong continuity for every wave function,
not merely for smooth or compactly supported representatives.
-/

namespace VacuumBellSeparation

open MeasureTheory

variable {m : ℝ} (hm : 0 < m)

include hm in
theorem oneParticleBoostMeasure_isLocallyFinite : IsLocallyFiniteMeasure (oneParticleMeasure m) :=
  IsLocallyFiniteMeasure.withDensity_coe
    (continuous_real_toNNReal.comp (continuous_oneParticleWeightReal hm))

theorem continuous_shellBoost_joint (m : ℝ) :
    Continuous (fun q : ℝ × EuclideanSpace ℝ (Fin 3) => shellBoost m q.1 q.2) := by
  have hω := (continuous_dispersion m).comp (continuous_snd : Continuous
    (Prod.snd : ℝ × EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3)))
  unfold shellBoost
  fun_prop

theorem oneParticleBoostIsometry_zero (ψ : Lp ℂ 2 (oneParticleMeasure m)) :
    oneParticleBoostIsometry hm 0 ψ = ψ := by
  change Lp.compMeasurePreserving (shellBoost m (-0)) _ ψ = ψ
  have hz : shellBoost m (-0) = id := by funext p; simp only [neg_zero, shellBoost_zero, id_eq]
  simp only [hz, Lp.compMeasurePreserving_id_apply]

theorem oneParticleBoostIsometry_add (a b : ℝ) (ψ : Lp ℂ 2 (oneParticleMeasure m)) :
    oneParticleBoostIsometry hm a (oneParticleBoostIsometry hm b ψ) =
      oneParticleBoostIsometry hm (a + b) ψ := by
  change Lp.compMeasurePreserving (shellBoost m (-a)) _
    (Lp.compMeasurePreserving (shellBoost m (-b)) _ ψ) =
      Lp.compMeasurePreserving (shellBoost m (-(a + b))) _ ψ
  rw [← Lp.compMeasurePreserving_comp_apply]
  have he : shellBoost m (-b) ∘ shellBoost m (-a) = shellBoost m (-(a + b)) := by
    funext p
    simp only [Function.comp_apply, shellBoost_shellBoost, neg_add_rev]
  simp only [he]

theorem continuous_oneParticleBoostIsometry (ψ : Lp ℂ 2 (oneParticleMeasure m)) :
    Continuous (fun η : ℝ => oneParticleBoostIsometry hm η ψ) := by
  letI : IsLocallyFiniteMeasure (oneParticleMeasure m) := oneParticleBoostMeasure_isLocallyFinite hm
  let g : ℝ → C(EuclideanSpace ℝ (Fin 3), EuclideanSpace ℝ (Fin 3)) :=
    fun η => ⟨shellBoost m (-η), continuous_shellBoost hm (-η)⟩
  have hg : Continuous g := by
    apply ContinuousMap.continuous_of_continuous_uncurry
    exact (continuous_shellBoost_joint m).comp
      (continuous_fst.neg.prodMk continuous_snd)
  exact continuous_const.compMeasurePreservingLp hg
    (fun η => measurePreserving_shellBoost hm (-η)) (by norm_num)

theorem continuous_oneParticleBoost (ψ : Lp ℂ 2 (oneParticleMeasure m)) :
    Continuous (fun η : ℝ => oneParticleBoost hm η ψ) :=
  continuous_oneParticleBoostIsometry hm ψ

end VacuumBellSeparation
