module

public import CGLMPBounds.Defs.Quantum
public import CGLMPBounds.Defs.CGLMPValue

@[expose] public section


/-!
# Source definitions for the finite-coordinate companion endpoint

The definitions below transcribe the C.1 statement in finite coordinates.
This module has definition imports only. No companion existence or gap identity is assumed.
-/


open scoped Matrix Kronecker
attribute [-instance] CStarMatrix.instHMulOfFintypeOfMulOfAddCommMonoid

namespace CGLMPBounds.CompanionFinite
noncomputable section

abbrev Physical (d n : ℕ) := ZMod d × Fin (4 * n)
abbrev PhysicalMat (d n : ℕ) := Matrix (Physical d n) (Physical d n) ℂ
abbrev MultiplicityMat (n : ℕ) := Matrix (Fin (4 * n)) (Fin (4 * n)) ℂ
abbrev Tuple (d n : ℕ) := Fin d → Matrix.unitaryGroup (Fin (4 * n)) ℂ

/-- Positive-exponent source Fourier convention, `F_aj=d^(-1/2)exp(2πiaj/d)`. -/
def fourierMatrix (d : ℕ) : Matrix (ZMod d) (Fin d) ℂ :=
  fun a j => (((Real.sqrt d)⁻¹ : ℝ) : ℂ) *
    Complex.exp (2 * Real.pi * Complex.I * (a.val : ℂ) * (j.val : ℂ) / d)

/-- Source phase `λ_j=exp(πij/(2d))`, for `0≤j<d`. -/
def phase {d : ℕ} (j : Fin d) : ℂ :=
  Complex.exp (Real.pi * Complex.I * (j.val : ℂ) / (2 * (d : ℂ)))

/-- `F ⊗ I_(4n)`; the physical dimension is `d*(4n)`. -/
def fourierLift (d n : ℕ) : Matrix (Physical d n) (Fin d × Fin (4 * n)) ℂ :=
  fourierMatrix d ⊗ₖ (1 : MultiplicityMat n)

/-- The block diagonal operator with frequency block `λ_j V_j`. -/
def frequencyOperator {d n : ℕ} (V : Tuple d n) :
    Matrix (Fin d × Fin (4 * n)) (Fin d × Fin (4 * n)) ℂ :=
  Matrix.compRingEquiv (Fin d) (Fin (4 * n)) ℂ
    (Matrix.diagonal fun j => phase j • (V j : MultiplicityMat n))

/-- The operator `R=(F⊗I)diag_j(λ_jV_j)(F†⊗I)` from p. 7. -/
def clock {d n : ℕ} [NeZero d] (V : Tuple d n) : PhysicalMat d n :=
  fourierLift d n * frequencyOperator V * (fourierLift d n)ᴴ

/-- `C_a^(4n)=|a⟩⟨a|⊗I_(4n)`. -/
def computational {d n : ℕ} [NeZero d] (a : ZMod d) : PhysicalMat d n :=
  Matrix.diagonal fun p => if p.1 = a then 1 else 0

/-- Source (C.4): `M_a^t(V)=R^t C_a^(4n) R^(-t)`.
Since `R` is constructed from unitaries, the negative power is written using `R†`. -/
def measurement {d n : ℕ} [NeZero d] (V : Tuple d n) (t : Fin 4) (a : ZMod d) :
    PhysicalMat d n :=
  clock V ^ t.val * computational a * (clock V)ᴴ ^ t.val

/-- `z_jk=τ_(4n)(V_j† V_k)`, normalized on the multiplicity space, not the physical space. -/
def correlation {d n : ℕ} (V : Tuple d n) (j k : Fin d) : ℂ :=
  Matrix.trace ((V j : MultiplicityMat n)ᴴ * (V k : MultiplicityMat n)) /
    ((4 * n : ℕ) : ℂ)

/-- `G_d=L_β`, with `β_h=sec(πh/(2d))/(2d²)` and the source oriented imaginary part. -/
def gap {d n : ℕ} (V : Tuple d n) : ℝ :=
  (∑ j : Fin d, ∑ k : Fin d,
    if j < k then
      (1 - (correlation V j k).re) /
          Real.cos (Real.pi * ((k.val - j.val : ℕ) : ℝ) / (2 * (d : ℝ))) +
        (correlation V j k).im /
          Real.cos (Real.pi * ((d - k.val + j.val : ℕ) : ℝ) / (2 * (d : ℝ)))
    else 0) / (2 * (d : ℝ) ^ 2)

end
end CGLMPBounds.CompanionFinite
