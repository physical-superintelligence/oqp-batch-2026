module

public import VacuumBellSeparation.FreeField.PolarUnitary
public import VacuumBellSeparation.FreeField.StandardSourceSpace

@[expose] public section


/-!
# Literal statement construction extracted from FreeField/SourcePolarUnitary

The moved declarations retain their original text. Later target proofs remain separate.
-/

namespace VacuumBellSeparation

open MeasureTheory

variable {m : ℝ} (hm : 0 < m) (U : Set (EuclideanSpace ℝ (Fin 3)))

noncomputable def sourcePolarUnitary (hU : Bornology.IsBounded U)
    (hopen : IsOpen U) (hne : U.Nonempty) :
    ComplexSourceHilbert hm U ≃ₗᵢ[ℂ] Lp ℂ 2 (oneParticleMeasure m) :=
  polarUnitary (complexSourceMap hm U) (complexSourceMap_injective hm U hU)
    (complexSourceMap_denseRange_of_open hm U hopen hne)


end VacuumBellSeparation
