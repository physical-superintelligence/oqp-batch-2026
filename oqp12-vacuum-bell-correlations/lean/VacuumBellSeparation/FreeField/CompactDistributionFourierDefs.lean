module

public import VacuumBellSeparation.FreeField.CutoffFourierKernel

@[expose] public section


open MeasureTheory Filter
open scoped SchwartzMap FourierTransform InnerProductSpace Topology

namespace VacuumBellSeparation

noncomputable def compactDistributionFourier
    (T : TemperedDistribution (EuclideanSpace ℝ (Fin 3)) ℂ)
    (χ : SchwartzMap (EuclideanSpace ℝ (Fin 3)) ℂ)
    (p : EuclideanSpace ℝ (Fin 3)) : ℂ := T (cutoffFourierKernel χ p)

end VacuumBellSeparation
