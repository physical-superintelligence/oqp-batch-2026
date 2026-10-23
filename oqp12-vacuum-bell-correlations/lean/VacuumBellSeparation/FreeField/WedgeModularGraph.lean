module

public import VacuumBellSeparation.FreeField.WedgeTomitaMultiplierEquality
public import VacuumBellSeparation.FreeField.AntilinearGraphAdjoint

@[expose] public section


/-!
# The actual full S*S graph of the original left wedge

The adjoint is defined by its universal antilinear pairing condition on the
entire original source graph. Exact Tomita graph equality and the genuine
maximal half-square identity identify S*S with exp(-4π²ξ₁).
-/

namespace VacuumBellSeparation

open MeasureTheory
open scoped ComplexConjugate

variable {m : ℝ} (hm : 0 < m)

theorem physicalWedgeReflection_inner (ψ χ : Lp ℂ 2 (oneParticleMeasure m)) :
    inner ℂ (physicalWedgeReflection hm ψ) (physicalWedgeReflection hm χ) =
      conj (inner ℂ ψ χ) := by
  rw [L2.inner_def, L2.inner_def, ← integral_conj]
  calc
    (∫ p, inner ℂ (physicalWedgeReflection hm ψ p) (physicalWedgeReflection hm χ p)
        ∂oneParticleMeasure m) =
      ∫ p, conj (inner ℂ (ψ (axisReflection p)) (χ (axisReflection p))) ∂oneParticleMeasure m := by
      apply integral_congr_ae
      filter_upwards [physicalWedgeReflection_ae hm ψ, physicalWedgeReflection_ae hm χ]
        with p hψ hχ
      simp only [hψ, hχ, RCLike.inner_apply, map_mul, Complex.conj_conj]
    _ = _ := (measurePreserving_massShell_rotation hm axisReflection).integral_comp
      axisReflection.toHomeomorph.measurableEmbedding (fun p => conj (inner ℂ (ψ p) (χ p)))

theorem physicalWedgeReflection_inner_swap (ψ χ : Lp ℂ 2 (oneParticleMeasure m)) :
    inner ℂ (physicalWedgeReflection hm ψ) χ = inner ℂ (physicalWedgeReflection hm χ) ψ := by
  have h := physicalWedgeReflection_inner hm ψ (physicalWedgeReflection hm χ)
  simpa only [physicalWedgeReflection_involutive, inner_conj_symm] using h

def leftWedgeTomitaAdjointGraph :
    Set (Lp ℂ 2 (oneParticleMeasure m) × Lp ℂ 2 (oneParticleMeasure m)) :=
  antilinearGraphAdjoint (sourceTomitaGraph hm (leftWedgeTimeZero 0))

def leftWedgeTomitaModularGraph :
    Set (Lp ℂ 2 (oneParticleMeasure m) × Lp ℂ 2 (oneParticleMeasure m)) :=
  antilinearGraphSquare (sourceTomitaGraph hm (leftWedgeTimeZero 0))

theorem leftWedgeTomitaAdjointGraph_iff (ψ χ : Lp ℂ 2 (oneParticleMeasure m)) :
    (ψ, χ) ∈ leftWedgeTomitaAdjointGraph hm ↔
      (physicalWedgeReflection hm ψ, χ) ∈ (physicalRapidityExponential hm (1 / 2)).graph := by
  rw [leftWedgeTomitaAdjointGraph, sourceTomitaGraph_eq_wedgeRapidityTomitaGraph]
  exact antilinearGraphAdjoint_reflected_selfAdjoint _
    (physicalRapidityExponential_isSelfAdjoint hm (1 / 2)) (physicalWedgeReflection hm)
    (physicalWedgeReflection_involutive hm) (physicalWedgeReflection_inner_swap hm) ψ χ

/-- Literal full-domain S*S, including its intermediate Tomita-domain vector. -/
theorem leftWedgeTomitaModularGraph_iff (ψ χ : Lp ℂ 2 (oneParticleMeasure m)) :
    (ψ, χ) ∈ leftWedgeTomitaModularGraph hm ↔
      (ψ, χ) ∈ (physicalRapidityExponential hm 1).graph := by
  rw [leftWedgeTomitaModularGraph, sourceTomitaGraph_eq_wedgeRapidityTomitaGraph]
  rw [wedgeRapidityTomitaGraph]
  rw [antilinearGraphSquare_reflected_selfAdjoint _
    (physicalRapidityExponential_isSelfAdjoint hm (1 / 2)) (physicalWedgeReflection hm)
    (physicalWedgeReflection_involutive hm) (physicalWedgeReflection_inner_swap hm)]
  exact (physicalRapidityExponential_graph_half_square hm 1 ψ χ).symm

theorem leftWedgeTomitaModularGraph_eq :
    leftWedgeTomitaModularGraph hm = (physicalRapidityExponential hm 1).graph := by
  ext p
  exact leftWedgeTomitaModularGraph_iff hm p.1 p.2

end VacuumBellSeparation
