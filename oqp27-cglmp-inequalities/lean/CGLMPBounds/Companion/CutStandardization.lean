module

public import CGLMPBounds.Companion.CutPhase
public import CGLMPBounds.Companion.FourierTrace

@[expose] public section


/-!
# Explicit scalar-cut standardization in the outcome coordinate

Supplement E.1, printed p. 16. The diagonal outcome gauge is the character
`a ↦ exp(-2*pi*i*a*s/d)`, with `s=d-1-j₀`. Definitions below retain the literal
fourth-root cut and the source Fourier clock. No PVM equivalence is assumed.
-/

open Matrix
attribute [-instance] CStarMatrix.instHMulOfFintypeOfMulOfAddCommMonoid

namespace CGLMPBounds.Companion
noncomputable section

variable {d : ℕ} [NeZero d]

/-- Scalar version of the source's frequency-block clock. -/
def scalarFourierClock (f : Fin d → ℂ) : Matrix (ZMod d) (ZMod d) ℂ :=
  outcomeFourier * Matrix.diagonal f * (outcomeFourier)ᴴ

/-- The actual scalar-cut clock, with the literal modulo-four labels from E.1. -/
def scalarCutClock (a : Fin 4) (j₀ : Fin d) : Matrix (ZMod d) (ZMod d) ℂ :=
  scalarFourierClock fun j =>
    sourcePhase j * Complex.I ^ (Circulation.fourthRootCutLabels a j₀ j).val

/-- The source measurement formula `R^t |b><b| (R†)^t` on one scalar summand. -/
def scalarClockMeasurement (R : Matrix (ZMod d) (ZMod d) ℂ)
    (t : ℕ) (b : ZMod d) : Matrix (ZMod d) (ZMod d) ℂ :=
  R ^ t * Matrix.single b b 1 * Rᴴ ^ t

def cutFrequencyShift (j₀ : Fin d) : Fin d :=
  ⟨d - 1 - j₀.val, by have := j₀.isLt; omega⟩

/-- The diagonal unitary implementing a positive shift of the frequency labels. -/
def cutOutcomeDiagonal (s : Fin d) : Matrix (ZMod d) (ZMod d) ℂ :=
  Matrix.diagonal fun a => ZMod.stdAddChar (-(a * (s.val : ZMod d)))

/-- The harmless global phase of the cut clock. -/
def cutClockScalar (a : Fin 4) (j₀ : Fin d) : ℂ :=
  Complex.I ^ a.val * (sourcePhase (cutFrequencyShift j₀))⁻¹

lemma fourthRootCut_phase (a : Fin 4) (j₀ j : Fin d) :
    Complex.I ^ (Circulation.fourthRootCutLabels a j₀ j).val =
      Complex.I ^ a.val * (if j₀ < j then -Complex.I else 1) := by
  unfold Circulation.fourthRootCutLabels
  split_ifs
  · fin_cases a <;> norm_num [Complex.I_sq]
  · simp

lemma scalarCut_frequency (a : Fin 4) (j₀ j : Fin d) :
    sourcePhase j * Complex.I ^ (Circulation.fourthRootCutLabels a j₀ j).val =
      cutClockScalar a j₀ * sourcePhase (j + cutFrequencyShift j₀) := by
  rw [fourthRootCut_phase]
  have hs := sourcePhase_cut_shift j₀ j
  change sourcePhase j * (if j₀ < j then -Complex.I else 1) =
    (sourcePhase (cutFrequencyShift j₀))⁻¹ *
      sourcePhase (j + cutFrequencyShift j₀) at hs
  calc
    _ = Complex.I ^ a.val *
        (sourcePhase j * (if j₀ < j then -Complex.I else 1)) := by ring
    _ = _ := by rw [hs]; simp only [cutClockScalar]; ring

lemma stdAddChar_star_mul_self (z : ZMod d) :
    star (ZMod.stdAddChar z) * ZMod.stdAddChar z = 1 := by
  rw [star_stdAddChar, ← AddChar.map_add_eq_mul, neg_add_cancel,
    AddChar.map_zero_eq_one]

lemma cutClockScalar_star_mul (a : Fin 4) (j₀ : Fin d) :
    star (cutClockScalar a j₀) * cutClockScalar a j₀ = 1 := by
  have hi : star (Complex.I ^ a.val) * Complex.I ^ a.val = 1 := by
    fin_cases a <;> norm_num [Complex.I_sq, Complex.star_def]
  have hs : star ((sourcePhase (cutFrequencyShift j₀))⁻¹) *
      (sourcePhase (cutFrequencyShift j₀))⁻¹ = 1 := by
    rw [star_inv₀, ← mul_inv, sourcePhase_star_mul, inv_one]
  calc
    _ = (star (Complex.I ^ a.val) * Complex.I ^ a.val) *
        (star ((sourcePhase (cutFrequencyShift j₀))⁻¹) *
          (sourcePhase (cutFrequencyShift j₀))⁻¹) := by
      simp only [cutClockScalar, star_mul']
      ring
    _ = 1 := by rw [hi, hs, one_mul]

lemma cutOutcomeDiagonal_star_mul (s : Fin d) :
    (cutOutcomeDiagonal s)ᴴ * cutOutcomeDiagonal s = 1 := by
  rw [cutOutcomeDiagonal, Matrix.diagonal_conjTranspose, Matrix.diagonal_mul_diagonal]
  simp only [Pi.star_apply, stdAddChar_star_mul_self]
  exact Matrix.diagonal_one

lemma cutOutcomeDiagonal_mul_star (s : Fin d) :
    cutOutcomeDiagonal s * (cutOutcomeDiagonal s)ᴴ = 1 :=
  (Matrix.mul_eq_one_comm_of_card_eq (ZMod d) (ZMod d) ℂ rfl).mp (cutOutcomeDiagonal_star_mul s)

lemma cutOutcomeDiagonal_fourier_shift (s j : Fin d) (a : ZMod d) :
    ZMod.stdAddChar (-(a * (s.val : ZMod d))) * outcomeFourier a (j + s) =
      outcomeFourier a j := by
  have hj : ((j + s).val : ZMod d) = (j.val : ZMod d) + (s.val : ZMod d) := by
    rw [Fin.val_add, ZMod.natCast_mod, Nat.cast_add]
  simp only [outcomeFourier, hj]
  calc
    _ = (((Real.sqrt d)⁻¹ : ℝ) : ℂ) *
        (ZMod.stdAddChar (-(a * (s.val : ZMod d))) *
          ZMod.stdAddChar (a * ((j.val : ZMod d) + (s.val : ZMod d)))) := by ring
    _ = _ := by rw [← AddChar.map_add_eq_mul]; congr 2; ring

lemma scalarFourierClock_apply (f : Fin d → ℂ) (a b : ZMod d) :
    scalarFourierClock f a b =
      ∑ j, outcomeFourier a j * f j * star (outcomeFourier b j) := by
  rw [scalarFourierClock, Matrix.mul_apply]
  simp only [Matrix.mul_diagonal, Matrix.conjTranspose_apply]

lemma scalarFourierClock_const_mul (c : ℂ) (f : Fin d → ℂ) :
    scalarFourierClock (fun j => c * f j) = c • scalarFourierClock f := by
  ext a b
  simp only [scalarFourierClock_apply, Matrix.smul_apply, smul_eq_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  ring

/-- Frequency translation is conjugation by the explicit diagonal outcome unitary. -/
theorem scalarFourierClock_shift (f : Fin d → ℂ) (s : Fin d) :
    scalarFourierClock (fun j => f (j + s)) =
      cutOutcomeDiagonal s * scalarFourierClock f * (cutOutcomeDiagonal s)ᴴ := by
  ext a b
  simp only [cutOutcomeDiagonal, Matrix.diagonal_conjTranspose,
    Matrix.diagonal_mul, Matrix.mul_diagonal, scalarFourierClock_apply,
    Pi.star_apply, Finset.mul_sum, Finset.sum_mul]
  apply Fintype.sum_equiv (Equiv.addRight s)
  intro j
  change outcomeFourier a j * f (j + s) * star (outcomeFourier b j) =
    (ZMod.stdAddChar (-(a * (s.val : ZMod d))) *
      (outcomeFourier a (j + s) * f (j + s) * star (outcomeFourier b (j + s)))) *
        star (ZMod.stdAddChar (-(b * (s.val : ZMod d))))
  calc
    _ = (ZMod.stdAddChar (-(a * (s.val : ZMod d))) * outcomeFourier a (j + s)) *
        f (j + s) *
        star (ZMod.stdAddChar (-(b * (s.val : ZMod d))) * outcomeFourier b (j + s)) := by
      rw [cutOutcomeDiagonal_fourier_shift, cutOutcomeDiagonal_fourier_shift]
    _ = _ := by simp only [star_mul']; ring

/-- The literal scalar-cut clock differs from the standard clock only by the
explicit outcome diagonal and a scalar of modulus one. -/
theorem scalarCutClock_eq (a : Fin 4) (j₀ : Fin d) :
    scalarCutClock a j₀ = cutClockScalar a j₀ •
      (cutOutcomeDiagonal (cutFrequencyShift j₀) * scalarFourierClock sourcePhase *
        (cutOutcomeDiagonal (cutFrequencyShift j₀))ᴴ) := by
  unfold scalarCutClock
  simp only [scalarCut_frequency]
  rw [scalarFourierClock_const_mul, scalarFourierClock_shift]

end
end CGLMPBounds.Companion
