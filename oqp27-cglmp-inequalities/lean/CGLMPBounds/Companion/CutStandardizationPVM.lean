module

public import CGLMPBounds.Companion.CutStandardization

@[expose] public section


/-!
# Scalar cuts give the literal Fourier-phase projectors

The final map is the explicit diagonal outcome unitary followed by the source
Fourier matrix. The target projectors are `fourierProjector` from B.2, with their
original outcome labels. No projector equality or irreducibility is an input.
-/

open Matrix
attribute [-instance] CStarMatrix.instHMulOfFintypeOfMulOfAddCommMonoid

namespace CGLMPBounds.Companion
noncomputable section

variable {d : ℕ} [NeZero d]

lemma cut_conjugate_pow {ι κ : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype κ] [DecidableEq κ] (Q : Matrix ι κ ℂ)
    (hQ : Qᴴ * Q = 1) (hQ' : Q * Qᴴ = 1) (A : Matrix κ κ ℂ) (t : ℕ) :
    (Q * A * Qᴴ) ^ t = Q * A ^ t * Qᴴ := by
  induction t with
  | zero => simp only [pow_zero, Matrix.mul_one, hQ']
  | succ t ih =>
    rw [pow_succ, ih, pow_succ]
    calc
      (Q * A ^ t * Qᴴ) * (Q * A * Qᴴ) =
          Q * (A ^ t * (Qᴴ * Q) * A) * Qᴴ := by simp only [Matrix.mul_assoc]
      _ = Q * (A ^ t * A) * Qᴴ := by rw [hQ, Matrix.mul_one]

lemma scalarFourierClock_pow (f : Fin d → ℂ) (t : ℕ) :
    scalarFourierClock f ^ t =
      outcomeFourier * Matrix.diagonal (fun j => f j ^ t) * (outcomeFourier)ᴴ := by
  rw [scalarFourierClock, cut_conjugate_pow outcomeFourier
    outcomeFourier_star_mul outcomeFourier_mul_star, Matrix.diagonal_pow]
  rfl

lemma scalarClockMeasurement_rankOne (R : Matrix (ZMod d) (ZMod d) ℂ)
    (t : ℕ) (b : ZMod d) :
    scalarClockMeasurement R t b =
      Matrix.vecMulVec (fun a => (R ^ t) a b) (star (fun a => (R ^ t) a b)) := by
  unfold scalarClockMeasurement
  rw [← Matrix.conjTranspose_pow]
  ext a c
  simp only [Matrix.mul_apply, Matrix.single_apply, Matrix.vecMulVec_apply,
    Matrix.conjTranspose_apply, Pi.star_apply]
  simp [ite_and]

lemma scalarClockMeasurement_smul (c : ℂ) (hc : star c * c = 1)
    (R : Matrix (ZMod d) (ZMod d) ℂ) (t : ℕ) (b : ZMod d) :
    scalarClockMeasurement (c • R) t b = scalarClockMeasurement R t b := by
  have hc' : c * star c = 1 := (mul_comm _ _).trans hc
  unfold scalarClockMeasurement
  rw [smul_pow, Matrix.conjTranspose_smul, smul_pow]
  calc
    _ = (c ^ t * star c ^ t) • (R ^ t * Matrix.single b b 1 * Rᴴ ^ t) := by
      simp only [smul_mul_assoc, mul_smul_comm, smul_smul]
      rw [mul_comm (star c ^ t) (c ^ t)]
    _ = _ := by rw [← mul_pow, hc', one_pow, one_smul]

lemma cutOutcomeDiagonal_fixes_computational (s : Fin d) (b : ZMod d) :
    (cutOutcomeDiagonal s)ᴴ * Matrix.single b b 1 * cutOutcomeDiagonal s =
      Matrix.single b b 1 := by
  ext i j
  by_cases hi : b = i <;> by_cases hj : b = j
  · subst i; subst j
    simp only [cutOutcomeDiagonal, Matrix.diagonal_conjTranspose,
      Matrix.diagonal_mul, Matrix.mul_diagonal, Pi.star_apply,
      Matrix.single_apply, and_self, ite_true, mul_one,
      stdAddChar_star_mul_self]
  · subst i
    simp [cutOutcomeDiagonal, Matrix.diagonal_conjTranspose,
      Matrix.diagonal_mul, Matrix.mul_diagonal, Matrix.diagonal_apply,
      Matrix.single_apply, hj, Ne.symm hj]
  · subst j
    simp [cutOutcomeDiagonal, Matrix.diagonal_conjTranspose,
      Matrix.diagonal_mul, Matrix.mul_diagonal, Matrix.diagonal_apply,
      Matrix.single_apply, hi, Ne.symm hi]
  · simp [cutOutcomeDiagonal, Matrix.diagonal_conjTranspose,
      Matrix.diagonal_mul, Matrix.mul_diagonal, Matrix.single_apply, hi, hj]

lemma scalarClockMeasurement_conjugate
    (Q R : Matrix (ZMod d) (ZMod d) ℂ)
    (hQ : Qᴴ * Q = 1) (hQ' : Q * Qᴴ = 1) (t : ℕ) (b : ZMod d)
    (hC : Qᴴ * Matrix.single b b 1 * Q = Matrix.single b b 1) :
    scalarClockMeasurement (Q * R * Qᴴ) t b =
      Q * scalarClockMeasurement R t b * Qᴴ := by
  have hadj : (Q * R * Qᴴ)ᴴ = Q * Rᴴ * Qᴴ := by
    simp only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose,
      Matrix.mul_assoc]
  unfold scalarClockMeasurement
  rw [hadj, cut_conjugate_pow Q hQ hQ', cut_conjugate_pow Q hQ hQ']
  calc
    _ = Q * (R ^ t * (Qᴴ * Matrix.single b b 1 * Q) * Rᴴ ^ t) * Qᴴ := by
      simp only [Matrix.mul_assoc]
    _ = _ := by rw [hC]

/-- The clock phase multiplies the first Fourier vector into the actual t-th vector. -/
lemma sourcePhase_pow_fourierVector (t : ℕ) (b : ZMod d) (j : Fin d) :
    sourcePhase j ^ t * fourierVector d 0 b j = fourierVector d t b j := by
  rw [sourcePhase_apply, ← Complex.exp_nat_mul, fourierVector_eq, fourierVector_eq]
  calc
    _ = (((Real.sqrt d)⁻¹ : ℝ) : ℂ) *
        (Complex.exp ((t : ℂ) * (((Real.pi * j.val / (2 * d) : ℝ) : ℂ) * Complex.I)) *
          Complex.exp ((fourierPhase d 0 b j : ℂ) * Complex.I)) := by ring
    _ = _ := by
      rw [← Complex.exp_add]
      congr 2
      unfold fourierPhase
      push_cast
      ring

lemma standardClock_pow_column (t : ℕ) (b : ZMod d) :
    (fun a => (scalarFourierClock sourcePhase ^ t) a b) =
      outcomeFourier *ᵥ fourierVector d t b := by
  funext a
  rw [scalarFourierClock_pow, Matrix.mul_apply]
  simp only [Matrix.mul_diagonal, Matrix.conjTranspose_apply, Matrix.mulVec, dotProduct]
  apply Finset.sum_congr rfl
  intro j _
  rw [outcomeFourier_eq_star_fourierVector b j, star_star, mul_assoc,
    sourcePhase_pow_fourierVector]

/-- Fourier conjugation of the uncut clock gives the actual B.2 PVMs. -/
theorem scalarClockMeasurement_standard (t : ℕ) (b : ZMod d) :
    scalarClockMeasurement (scalarFourierClock sourcePhase) t b =
      outcomeFourier * fourierProjector d t b * (outcomeFourier)ᴴ := by
  rw [scalarClockMeasurement_rankOne, standardClock_pow_column, fourierProjector,
    Matrix.mul_vecMulVec, Matrix.vecMulVec_mul, Matrix.star_mulVec]

/-- One common change of basis for every measurement and outcome on this scalar cut. -/
def cutStandardizer (j₀ : Fin d) : Matrix (ZMod d) (Fin d) ℂ :=
  cutOutcomeDiagonal (cutFrequencyShift j₀) * outcomeFourier

lemma cutStandardizer_star_mul (j₀ : Fin d) :
    (cutStandardizer j₀)ᴴ * cutStandardizer j₀ = 1 := by
  unfold cutStandardizer
  rw [Matrix.conjTranspose_mul]
  calc
    _ = (outcomeFourier)ᴴ *
        ((cutOutcomeDiagonal (cutFrequencyShift j₀))ᴴ *
          cutOutcomeDiagonal (cutFrequencyShift j₀)) * outcomeFourier := by
      simp only [Matrix.mul_assoc]
    _ = 1 := by rw [cutOutcomeDiagonal_star_mul, Matrix.mul_one, outcomeFourier_star_mul]

lemma cutStandardizer_mul_star (j₀ : Fin d) :
    cutStandardizer j₀ * (cutStandardizer j₀)ᴴ = 1 :=
  (Matrix.mul_eq_one_comm_of_card_eq (Fin d) (ZMod d) ℂ (by simp [ZMod.card])).mp
    (cutStandardizer_star_mul j₀)

/-- Literal scalar-cut PVM standardization from E.1. The global fourth-root
label affects the clock but cancels from all projectors. -/
theorem scalarCutMeasurement_standard (a : Fin 4) (j₀ : Fin d)
    (t : ℕ) (b : ZMod d) :
    scalarClockMeasurement (scalarCutClock a j₀) t b =
      cutStandardizer j₀ * fourierProjector d t b * (cutStandardizer j₀)ᴴ := by
  rw [scalarCutClock_eq, scalarClockMeasurement_smul _ (cutClockScalar_star_mul a j₀),
    scalarClockMeasurement_conjugate _ _ (cutOutcomeDiagonal_star_mul _)
      (cutOutcomeDiagonal_mul_star _) _ _ (cutOutcomeDiagonal_fixes_computational _ _),
    scalarClockMeasurement_standard]
  simp only [cutStandardizer, Matrix.conjTranspose_mul, Matrix.mul_assoc]

end
end CGLMPBounds.Companion
