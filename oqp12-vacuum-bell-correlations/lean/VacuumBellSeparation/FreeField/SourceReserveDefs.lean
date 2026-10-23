module

public import VacuumBellSeparation.FreeField.SourceGramStrictness
public import VacuumBellSeparation.Gaussian.NormalizedCommutation

@[expose] public section


/-!
# Literal statement construction extracted from FreeField/SourceReserve

The moved declarations retain their original text. Later target proofs remain separate.
-/

namespace VacuumBellSeparation

open ContinuousLinearMap
open scoped InnerProductSpace

variable {m : ℝ} (hm : 0 < m) (U : Set (EuclideanSpace ℝ (Fin 3)))

noncomputable def conjugateSourceGram :
    ComplexSourceHilbert hm U →L[ℂ] ComplexSourceHilbert hm U :=
  Gaussian.conjugateOperator (sourceGram hm U)

noncomputable def sourceReserve :
    ComplexSourceHilbert hm U →L[ℂ] ComplexSourceHilbert hm U :=
  CFC.sqrt (sourceGram hm U * conjugateSourceGram hm U)


end VacuumBellSeparation
