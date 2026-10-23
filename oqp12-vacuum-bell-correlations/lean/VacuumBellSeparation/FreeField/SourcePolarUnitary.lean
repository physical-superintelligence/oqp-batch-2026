module

public import VacuumBellSeparation.FreeField.SourcePolarUnitaryDefs
public import VacuumBellSeparation.FreeField.PolarUnitary
public import VacuumBellSeparation.FreeField.StandardSourceSpace

@[expose] public section


/-!
# Polar decomposition of the actual completed local source map

The constructed unitary is obtained from the proved source-map injectivity
and dense range. The factorization uses the literal physical source Gram
operator and its CFC square root, including spectra accumulating at zero.
-/

namespace VacuumBellSeparation

open MeasureTheory

variable {m : ℝ} (hm : 0 < m) (U : Set (EuclideanSpace ℝ (Fin 3)))

theorem sourcePolarUnitary_sqrt_gram (hU : Bornology.IsBounded U)
    (hopen : IsOpen U) (hne : U.Nonempty) (z : ComplexSourceHilbert hm U) :
    sourcePolarUnitary hm U hU hopen hne (CFC.sqrt (sourceGram hm U) z) =
      complexSourceMap hm U z :=
  polarUnitary_polarGramRoot (complexSourceMap hm U) _ _ z

theorem sourcePolarUnitary_factorization (hU : Bornology.IsBounded U)
    (hopen : IsOpen U) (hne : U.Nonempty) :
    (sourcePolarUnitary hm U hU hopen hne).toContinuousLinearEquiv.toContinuousLinearMap.comp
      (CFC.sqrt (sourceGram hm U)) = complexSourceMap hm U := by
  apply ContinuousLinearMap.ext
  intro z
  exact sourcePolarUnitary_sqrt_gram hm U hU hopen hne z

end VacuumBellSeparation
