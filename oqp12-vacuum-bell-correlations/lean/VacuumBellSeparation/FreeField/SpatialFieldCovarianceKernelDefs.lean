module

public import VacuumBellSeparation.Special.BesselKDefs
public import VacuumBellSeparation.FreeField.TimeZeroDefs

@[expose] public section


/-!
# Statement seed extracted from FreeField/SpatialFieldCovarianceKernel

Literal declarations are unchanged; theorem conclusions remain in the implementation module.
-/

namespace VacuumBellSeparation

open MeasureTheory Set
open scoped ComplexConjugate

noncomputable def spatialFieldBesselKernel (m : ℝ) (w : EuclideanSpace ℝ (Fin 3)) : ℝ :=
  m / (4 * Real.pi ^ 2 * ‖w‖) * besselKReal 1 (m * ‖w‖)


end VacuumBellSeparation
