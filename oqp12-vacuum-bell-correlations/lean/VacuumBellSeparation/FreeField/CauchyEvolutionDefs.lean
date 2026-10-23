module

public import VacuumBellSeparation.FreeField.EvolutionGenerator

@[expose] public section


namespace VacuumBellSeparation

set_option backward.isDefEq.respectTransparency false
open MeasureTheory FourierTransform
open scoped SchwartzMap FourierTransform

noncomputable def cauchyPositiveData (m : ℝ) (f g : SpatialSchwartz) : SpatialSchwartz :=
  (1 / 2 : ℂ) • (f - Complex.I • massiveSchwartzPower m (-1) g)

noncomputable def cauchyNegativeData (m : ℝ) (f g : SpatialSchwartz) : SpatialSchwartz :=
  (1 / 2 : ℂ) • (f + Complex.I • massiveSchwartzPower m (-1) g)

/-- The actual velocity, itself a spatial Schwartz function at every real time. -/
noncomputable def massiveSchwartzCauchyVelocity (m t : ℝ) (f g : SpatialSchwartz) :
    SpatialSchwartz :=
  Complex.I • massiveSchwartzEvolution m t (massiveSchwartzPower m 1 (cauchyPositiveData m f g)) -
    Complex.I • massiveSchwartzEvolution m (-t)
      (massiveSchwartzPower m 1 (cauchyNegativeData m f g))

end VacuumBellSeparation
