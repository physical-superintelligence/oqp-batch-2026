module

public import CGLMPBounds.Defs.Quantum

@[expose] public section


/-!
# The Fourier-phase measurements (definitions)

Equation (B.2) of the supplement (Letter equation (2)), in the tracial convention
`(P⁰, P¹, P², P³) = (A₀ᵀ, B₀, A₁ᵀ, B₁)`:
`|ψ_{t,a}⟩ = d^{-1/2} Σ_{j=0}^{d-1} e^{-2πi j (a - t/4)/d} |j⟩`, `Π^t_a = |ψ_{t,a}⟩⟨ψ_{t,a}|`,
`t = 0, 1, 2, 3`. The Fourier-phase behaviour `Q_d` is the behaviour of these measurements on `Φ_d`.
This file contains definitions only.
-/

namespace CGLMPBounds

noncomputable section

/-- The Fourier-phase vector `ψ_{t,a}` of (B.2): `ψ_{t,a}(j) = d^{-1/2} e^{-2πi j (a - t/4)/d}`
for `j ∈ {0, …, d-1}`; the outcome `a ∈ ℤ_d` enters through its representative
`a.val ∈ {0, …, d-1}`. -/
def fourierVector (d t : ℕ) (a : ZMod d) (j : Fin d) : ℂ :=
  (((Real.sqrt d)⁻¹ : ℝ) : ℂ) *
    Complex.exp (-(2 * Real.pi * Complex.I * ((j : ℕ) : ℂ) * (((a.val : ℕ) : ℂ) - (t : ℂ) / 4)) / d)

/-- The standard tracial projector `Π^t_a = |ψ_{t,a}⟩⟨ψ_{t,a}|` of (B.2). -/
def fourierProjector (d t : ℕ) (a : ZMod d) : Matrix (Fin d) (Fin d) ℂ :=
  Matrix.vecMulVec (fourierVector d t a) (star (fourierVector d t a))

/-- The Fourier-phase behaviour `Q_d`: Alice's tracial measurements `P^{2x} = Π^{2x}` and Bob's
measurements `P^{1+2y} = Π^{1+2y}` on `Φ_d`. -/
def fourierTable (d : ℕ) : Table (ZMod d) (ZMod d) :=
  tracialTable (fun x a => fourierProjector d (2 * x.val) a)
    (fun y b => fourierProjector d (1 + 2 * y.val) b)

end

end CGLMPBounds
