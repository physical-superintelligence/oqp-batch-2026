module

public import VacuumBellSeparation.FreeField.SourcePhysicalResolvent
public import VacuumBellSeparation.FreeField.WedgeModularGraph

@[expose] public section


/-!
# The actual wedge source resolvent in rapidity Fourier coordinates

The proved full original Tomita square and its universal resolvent
identify κκ*/2 with the literal logistic frequency multiplier. This
retains the original completed halfspace source map and the maximal
exponential domain.
-/

namespace VacuumBellSeparation

open MeasureTheory

variable {m : ℝ} (hm : 0 < m)

theorem leftWedgePhysicalResolvent_mem_graph (ψ : Lp ℂ 2 (oneParticleMeasure m)) :
    (sourcePhysicalResolvent hm (leftWedgeTimeZero 0) ψ,
      ψ - sourcePhysicalResolvent hm (leftWedgeTimeZero 0) ψ) ∈
        (physicalRapidityExponential hm 1).graph :=
  (leftWedgeTomitaModularGraph_iff hm _ _).mp
    (sourcePhysicalResolvent_mem_square hm (leftWedgeTimeZero 0) ψ)

theorem leftWedgePhysicalResolvent_fourier (ψ : Lp ℂ 2 (oneParticleMeasure m)) :
    oneParticleRapidityFourier hm (sourcePhysicalResolvent hm (leftWedgeTimeZero 0) ψ) =
      exponentialResolvent rapidityMeasure (rapidityFrequencyExponent 1)
        (measurable_rapidityFrequencyExponent 1) (oneParticleRapidityFourier hm ψ) := by
  have hg := (physicalRapidityExponential_mem_graph_iff hm 1 _ _).mp
    (leftWedgePhysicalResolvent_mem_graph hm ψ)
  rw [LinearPMap.mem_graph_iff] at hg
  obtain ⟨y, hy, hv⟩ := hg
  change (y : RapidityL2) = oneParticleRapidityFourier hm
    (sourcePhysicalResolvent hm (leftWedgeTimeZero 0) ψ) at hy
  change rapidityExponential 1 y = oneParticleRapidityFourier hm
    (ψ - sourcePhysicalResolvent hm (leftWedgeTimeZero 0) ψ) at hv
  symm
  have hr : exponentialResolvent rapidityMeasure (rapidityFrequencyExponent 1)
      (measurable_rapidityFrequencyExponent 1) (oneParticleRapidityFourier hm ψ) = y := by
    apply (exponentialMultiplication_resolvent rapidityMeasure (rapidityFrequencyExponent 1)
      (measurable_rapidityFrequencyExponent 1) _ _).mp
    refine ⟨y.property, ?_⟩
    change (y : RapidityL2) + rapidityExponential 1 y = oneParticleRapidityFourier hm ψ
    rw [hv, map_sub, hy]
    abel
  exact hr.trans hy

end VacuumBellSeparation
