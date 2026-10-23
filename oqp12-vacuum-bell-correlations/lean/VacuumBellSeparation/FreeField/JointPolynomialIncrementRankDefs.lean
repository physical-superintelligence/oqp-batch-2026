module

public import VacuumBellSeparation.FreeField.JointPolynomialIncrementNorm
public import VacuumBellSeparation.FreeField.JointPolynomialCombinedRange

@[expose] public section


/-!
# Literal statement construction extracted from FreeField/JointPolynomialIncrementNuclear

The moved declarations retain their original text. Later target proofs remain separate.
-/

noncomputable section
namespace VacuumBellSeparation
open Gaussian Gaussian.HilbertComplexification

def jointPolynomialIncrementRank (n : ℕ) : ℕ := 2 * (9 * (n + 1) + 1) ^ 3


end VacuumBellSeparation
