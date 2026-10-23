module

public import Mathlib

@[expose] public section


/-!
# The explicit trace density of Lemma C.3

Eigenvalues are the multiset of characteristic-polynomial roots. Thus every
root is counted with its algebraic multiplicity, including defective pencils.
No moment identity, continuity or support property is part of the definition.
The source hypotheses are Hermitian H,Y, invertible H, and positive dimension.
-/

namespace CGLMPBounds

noncomputable section

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The matrix pencil H⁻¹(Y-zI) in the proof of C.3. -/
def traceDensityPencil (H Y : Matrix ι ι ℂ) (z : ℂ) : Matrix ι ι ℂ :=
  H⁻¹ * (Y - z • (1 : Matrix ι ι ℂ))

/-- The explicit density w_(H,Y), normalized by 2π times the matrix dimension. -/
def traceDensity (H Y : Matrix ι ι ℂ) (y : ℝ) : ℝ :=
  (((traceDensityPencil H Y (y : ℂ)).charpoly.roots).map
    (fun z : ℂ => |z.im|)).sum / (2 * Real.pi * Fintype.card ι)

end
end CGLMPBounds
