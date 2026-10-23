module

public import VacuumBellSeparation.Bell.GenericBellCorrelationDefs

@[expose] public section


/-! Literal signed-real Summers--Werner Bell quantity (SW88, p.219).
The real part only supplies a real codomain; positivity and commutation imply
that the actual expectation is real. That implication is proved separately. -/

namespace VacuumBellSeparation.Bipartite.HC00

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

def jointSignedBellValues (A B : VonNeumannAlgebra H)
    (f : (jointAlgebra A B).toStarSubalgebra → ℂ) : Set ℝ :=
  {r | ∃ X₀ X₁ Y₀ Y₁ : (jointAlgebra A B).toStarSubalgebra,
    (X₀ : H →L[ℂ] H) ∈ saContractions A ∧
    (X₁ : H →L[ℂ] H) ∈ saContractions A ∧
    (Y₀ : H →L[ℂ] H) ∈ saContractions B ∧
    (Y₁ : H →L[ℂ] H) ∈ saContractions B ∧
    r = (1 / 2 : ℝ) * (f (X₀ * (Y₀ + Y₁) + X₁ * (Y₀ - Y₁))).re}

noncomputable def jointSignedBellCorrelation (A B : VonNeumannAlgebra H)
    (f : (jointAlgebra A B).toStarSubalgebra → ℂ) : ℝ :=
  sSup (jointSignedBellValues A B f)

end VacuumBellSeparation.Bipartite.HC00
