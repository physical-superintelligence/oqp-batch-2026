module

public import VacuumBellSeparation.Special.BesselKDefs
public import VacuumBellSeparation.FreeField.TimeZeroDefs

@[expose] public section


/-!
# Statement seed extracted from FreeField/SpatialMomentumCovarianceKernel

Literal declarations are unchanged; theorem conclusions remain in the implementation module.
-/

namespace VacuumBellSeparation

open MeasureTheory Set
open scoped ComplexConjugate

noncomputable def spatialMomentumBesselKernel (m : ℝ) (w : EuclideanSpace ℝ (Fin 3)) : ℝ :=
  -(m ^ 2) / (4 * Real.pi ^ 2 * ‖w‖ ^ 2) * besselKReal 2 (m * ‖w‖)


end VacuumBellSeparation
