module

public import VacuumBellSeparation.FreeField.SchwartzKleinGordon

@[expose] public section


namespace VacuumBellSeparation

open scoped SchwartzMap FourierTransform
open FourierTransform MeasureTheory

abbrev SpatialSchwartz := SchwartzMap (EuclideanSpace ℝ (Fin 3)) ℂ

/-- For positive mass, the phase is `exp(i t sqrt(m²+|2πξ|²))`.
For other masses this definition retains the existing massive-symbol convention. -/
noncomputable def massiveEvolutionPhase (m t : ℝ) (ξ : EuclideanSpace ℝ (Fin 3)) : ℂ :=
  Complex.exp (((t * massiveSchwartzSymbol m 1 ξ : ℝ) : ℂ) * Complex.I)

/-- The actual real-time Fourier evolution, acting on spatial Schwartz data. -/
noncomputable def massiveSchwartzEvolution (m t : ℝ) : SpatialSchwartz →L[ℂ] SpatialSchwartz :=
  SchwartzMap.fourierMultiplierCLM ℂ (massiveEvolutionPhase m t)

/-- The real cosine propagator on the Schwartz core. -/
noncomputable def massiveSchwartzCosine (m t : ℝ) : SpatialSchwartz →L[ℂ] SpatialSchwartz :=
  SchwartzMap.fourierMultiplierCLM ℂ
    (fun ξ => (Real.cos (t * massiveSchwartzSymbol m 1 ξ) : ℂ))

/-- At positive mass, the sine propagator divided by the strictly positive energy. -/
noncomputable def massiveSchwartzSine (m t : ℝ) : SpatialSchwartz →L[ℂ] SpatialSchwartz :=
  SchwartzMap.fourierMultiplierCLM ℂ (fun ξ =>
    ((massiveSchwartzSymbol m (-1) ξ * Real.sin (t * massiveSchwartzSymbol m 1 ξ) : ℝ) : ℂ))

/-- Literal solution candidate for initial position `f` and velocity `g`. -/
noncomputable def massiveSchwartzCauchy (m t : ℝ) (f g : SpatialSchwartz) : SpatialSchwartz :=
  massiveSchwartzCosine m t f + massiveSchwartzSine m t g

end VacuumBellSeparation
