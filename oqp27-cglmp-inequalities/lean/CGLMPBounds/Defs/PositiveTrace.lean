module

public import CGLMPBounds.Defs.TraceDensity

@[expose] public section


/-! Literal normalized positive-part trace and its real Taylor coefficients
from (C.7). The maximum is applied to each characteristic root's real part
before taking its power. For Hermitian matrices these are the actual real
eigenvalues with algebraic multiplicity. No moment or contour identity is
encoded in the definitions. -/

namespace CGLMPBounds
noncomputable section
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def positiveTracePower (A : Matrix ι ι ℂ) (k : ℕ) : ℝ :=
  (A.charpoly.roots.map (fun z : ℂ => (max z.re 0) ^ k)).sum /
    (Fintype.card ι : ℝ)

def positiveTraceTaylorCoefficient (H Y : Matrix ι ι ℂ) (k q : ℕ) : ℝ :=
  iteratedDeriv q
    (fun t : ℝ => positiveTracePower (H + (t : ℂ) • Y) k) 0 /
      (q.factorial : ℝ)

end
end CGLMPBounds
