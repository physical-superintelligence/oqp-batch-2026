module

public import CGLMPBounds.Defs.Quantum

@[expose] public section


open scoped Matrix

/-!
# Finite companion construction: definitions

Supplement, Lemma C.1, pp. 6–7. The outcome shift has convention `J |a⟩ = |a−1⟩`.
Consequently the `(k,l)` block of `Z_t = Σ_c J^c ⊗ P_c^t` is `P_(l−k)^t`.
Outcome coordinates are `ZMod d`; the physical coordinate is `Fin n`.

These definitions describe the outcome-covariance stage and its common reducing embedding.
The clock, Fourier diagonalization, and Bell-value identity are separate construction stages;
none of those conclusions is stored as a structure field or an assumption here.
-/

namespace CGLMPBounds.Companion

noncomputable section

abbrev Base (n : ℕ) := Matrix (Fin n) (Fin n) ℂ
abbrev OutcomeSpace (d n : ℕ) := ZMod d × Fin n
abbrev OutcomeMat (d n : ℕ) := Matrix (OutcomeSpace d n) (OutcomeSpace d n) ℂ
abbrev Blocks (d n : ℕ) := Matrix (ZMod d) (ZMod d) (Base n)

variable {d n : ℕ} [NeZero d]

/-- Flatten an outcome-indexed matrix of physical matrix blocks. -/
abbrev flatten : Blocks d n ≃+* OutcomeMat d n :=
  Matrix.compRingEquiv (ZMod d) (Fin n) ℂ

/-- The source's `Z_t`, before flattening its physical blocks. -/
def conjugatorBlocks (P : ZMod d → Base n) : Blocks d n :=
  fun k l => P (l - k)

/-- `Z_t = Σ_c J^c ⊗ P_c^t`, in outcome/physical product coordinates. -/
def conjugator (P : ZMod d → Base n) : OutcomeMat d n :=
  flatten (conjugatorBlocks P)

/-- The computational outcome projector `|a⟩⟨a| ⊗ I_n`, in blocks. -/
def computationalBlocks (a : ZMod d) : Blocks d n :=
  Matrix.diagonal fun k => if k = a then 1 else 0

/-- The computational outcome projector `|a⟩⟨a| ⊗ I_n`. -/
def computational (a : ZMod d) : OutcomeMat d n :=
  flatten (computationalBlocks a)

/-- The outcome-covariant PVM has `k`th diagonal block `P_(a−k)`. -/
def covariantBlocks (P : ZMod d → Base n) (a : ZMod d) : Blocks d n :=
  Matrix.diagonal fun k => P (a - k)

/-- The outcome-covariant family on `C^d ⊗ C^n`. -/
def covariant (P : ZMod d → Base n) (a : ZMod d) : OutcomeMat d n :=
  flatten (covariantBlocks P a)

/-- The common coordinate-block inclusion `ξ ↦ |k⟩ ⊗ ξ`. -/
def blockEmbedding (k : ZMod d) : Matrix (OutcomeSpace d n) (Fin n) ℂ :=
  fun p j => if p.1 = k then (1 : Base n) p.2 j else 0

/-- The explicit measurement embedding `ξ ↦ Σ_a |a⟩ ⊗ P_a ξ`. -/
def measurementEmbedding (P : ZMod d → Base n) :
    Matrix (OutcomeSpace d n) (Fin n) ℂ :=
  fun p j => P p.1 p.2 j

/-- The transported family that appears in clock zero in (C.4). -/
def transported (P : Fin 4 → ZMod d → Base n) (t : Fin 4) (a : ZMod d) :
    OutcomeMat d n :=
  (conjugator (P 0))ᴴ * covariant (P t) a * conjugator (P 0)

/-- The four-step clock has block `U_t` in position `(t,t+1 mod 4)`. -/
def weightedClock {R : Type*} [Zero R] (U : Fin 4 → R) : Matrix (Fin 4) (Fin 4) R :=
  fun t s => if s = t + 1 then U t else 0

/-- Flatten the four-step clock into an ordinary complex matrix. -/
def clockMatrix {ι : Type*} [Fintype ι] (U : Fin 4 → Matrix ι ι ℂ) :
    Matrix (Fin 4 × ι) (Fin 4 × ι) ℂ :=
  Matrix.compRingEquiv (Fin 4) ι ℂ (weightedClock U)

/-- Repeat the same operator in each of the four clock blocks. -/
def clockLift {ι : Type*} [Fintype ι] (X : Matrix ι ι ℂ) :
    Matrix (Fin 4 × ι) (Fin 4 × ι) ℂ :=
  Matrix.compRingEquiv (Fin 4) ι ℂ (Matrix.diagonal fun _ : Fin 4 => X)

end
end CGLMPBounds.Companion
