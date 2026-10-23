module

public import CGLMPBounds.Companion.CutStandardizationSum

@[expose] public section


/-!
# Transporting cut standardization through a common multiplicity basis

This structural step accepts an actual unitary diagonalization of the tuple and
constructs the common standardizing matrix. The scalar-cut phase identity and
all projector identifications are supplied by the preceding modules, not assumed.
-/

open Matrix
open scoped Kronecker
attribute [-instance] CStarMatrix.instHMulOfFintypeOfMulOfAddCommMonoid

namespace CGLMPBounds.Companion
noncomputable section

variable {d : ℕ} [NeZero d]
variable {κ : Type*} [Fintype κ] [DecidableEq κ]

def cutMultiplicityLift (Q : Matrix κ κ ℂ) :
    Matrix (ZMod d × κ) (ZMod d × κ) ℂ :=
  (1 : Matrix (ZMod d) (ZMod d) ℂ) ⊗ₖ Q

lemma cutMultiplicityLift_star (Q : Matrix κ κ ℂ) :
    (cutMultiplicityLift (d := d) Q)ᴴ = cutMultiplicityLift Qᴴ := by
  simp only [cutMultiplicityLift, Matrix.conjTranspose_kronecker, Matrix.conjTranspose_one]

lemma cutMultiplicityLift_mul (Q S : Matrix κ κ ℂ) :
    cutMultiplicityLift (d := d) Q * cutMultiplicityLift S = cutMultiplicityLift (Q * S) := by
  simp only [cutMultiplicityLift, ← Matrix.mul_kronecker_mul, Matrix.one_mul]

lemma cutMultiplicityLift_one :
    cutMultiplicityLift (d := d) (1 : Matrix κ κ ℂ) = 1 :=
  Matrix.one_kronecker_one

lemma cutMultiplicityLift_star_mul (Q : Matrix κ κ ℂ) (hQ : Qᴴ * Q = 1) :
    (cutMultiplicityLift (d := d) Q)ᴴ * cutMultiplicityLift Q = 1 := by
  rw [cutMultiplicityLift_star, cutMultiplicityLift_mul, hQ, cutMultiplicityLift_one]

lemma cutMultiplicityLift_mul_star (Q : Matrix κ κ ℂ) (hQ : Q * Qᴴ = 1) :
    cutMultiplicityLift (d := d) Q * (cutMultiplicityLift Q)ᴴ = 1 := by
  rw [cutMultiplicityLift_star, cutMultiplicityLift_mul, hQ, cutMultiplicityLift_one]

lemma outcomeBlock_multiplicity_mul (Q : Matrix κ κ ℂ)
    (X : Matrix (ZMod d × κ) (ZMod d × κ) ℂ) (a b : ZMod d) :
    outcomeBlock (cutMultiplicityLift Q * X) a b = Q * outcomeBlock X a b := by
  ext u v
  simp [outcomeBlock, cutMultiplicityLift, Matrix.mul_apply, Fintype.sum_prod_type,
    Matrix.kronecker_apply, Matrix.one_apply, ite_mul, mul_ite]

lemma outcomeBlock_mul_multiplicity (Q : Matrix κ κ ℂ)
    (X : Matrix (ZMod d × κ) (ZMod d × κ) ℂ) (a b : ZMod d) :
    outcomeBlock (X * cutMultiplicityLift Q) a b = outcomeBlock X a b * Q := by
  ext u v
  simp [outcomeBlock, cutMultiplicityLift, Matrix.mul_apply, Fintype.sum_prod_type,
    Matrix.kronecker_apply, Matrix.one_apply, ite_mul, mul_ite]

lemma blockFourierOperator_multiplicity_conjugate (Q : Matrix κ κ ℂ)
    (B : Fin d → Matrix κ κ ℂ) :
    blockFourierOperator (fun j => Q * B j * Qᴴ) =
      cutMultiplicityLift Q * blockFourierOperator B * (cutMultiplicityLift Q)ᴴ := by
  have hb (a b : ZMod d) :
      outcomeBlock (blockFourierOperator (fun j => Q * B j * Qᴴ)) a b =
        outcomeBlock (cutMultiplicityLift Q * blockFourierOperator B *
          (cutMultiplicityLift Q)ᴴ) a b := by
    rw [cutMultiplicityLift_star, outcomeBlock_mul_multiplicity,
      outcomeBlock_multiplicity_mul, outcomeBlock_blockFourierOperator,
      outcomeBlock_blockFourierOperator]
    simp only [Matrix.mul_sum, Matrix.sum_mul, Matrix.mul_smul, Matrix.smul_mul]
  ext p q
  exact congrArg (fun M : Matrix κ κ ℂ => M p.2 q.2) (hb p.1 q.1)

lemma cutMultiplicityLift_fixes_computational (Q : Matrix κ κ ℂ)
    (hQ : Qᴴ * Q = 1) (b : ZMod d) :
    (cutMultiplicityLift Q)ᴴ * outcomeProjector b * cutMultiplicityLift Q =
      outcomeProjector (ι := κ) b := by
  rw [cutMultiplicityLift_star]
  simp only [outcomeProjector_eq_sum, cutSummandMatrix_const,
    cutMultiplicityLift, ← Matrix.mul_kronecker_mul, Matrix.one_mul, Matrix.mul_one, hQ]

lemma blockClockMeasurement_conjugate
    (Q R : Matrix (ZMod d × κ) (ZMod d × κ) ℂ)
    (hQ : Qᴴ * Q = 1) (hQ' : Q * Qᴴ = 1) (t : ℕ) (b : ZMod d)
    (hC : Qᴴ * outcomeProjector b * Q = outcomeProjector b) :
    blockClockMeasurement (Q * R * Qᴴ) t b =
      Q * blockClockMeasurement R t b * Qᴴ := by
  have hadj : (Q * R * Qᴴ)ᴴ = Q * Rᴴ * Qᴴ := by
    simp only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose,
      Matrix.mul_assoc]
  unfold blockClockMeasurement
  rw [hadj, cut_conjugate_pow Q hQ hQ', cut_conjugate_pow Q hQ hQ']
  calc
    _ = Q * (R ^ t * (Qᴴ * outcomeProjector b * Q) * Rᴴ ^ t) * Qᴴ := by
      simp only [Matrix.mul_assoc]
    _ = _ := by rw [hC]

/-- Full explicit change of basis, including the common multiplicity eigenbasis. -/
def cutBasisStandardizer (Q : Matrix κ κ ℂ) (j₀ : κ → Fin d) :
    Matrix (ZMod d × κ) (Fin d × κ) ℂ :=
  cutMultiplicityLift Q * cutSumStandardizer j₀

lemma cutBasisStandardizer_star_mul (Q : Matrix κ κ ℂ) (hQ : Qᴴ * Q = 1)
    (j₀ : κ → Fin d) : (cutBasisStandardizer Q j₀)ᴴ * cutBasisStandardizer Q j₀ = 1 := by
  unfold cutBasisStandardizer
  rw [Matrix.conjTranspose_mul]
  calc
    _ = (cutSumStandardizer j₀)ᴴ *
        ((cutMultiplicityLift Q)ᴴ * cutMultiplicityLift Q) * cutSumStandardizer j₀ := by
      simp only [Matrix.mul_assoc]
    _ = 1 := by rw [cutMultiplicityLift_star_mul Q hQ, Matrix.mul_one,
      cutSumStandardizer_star_mul]

lemma cutBasisStandardizer_mul_star (Q : Matrix κ κ ℂ) (hQ : Q * Qᴴ = 1)
    (j₀ : κ → Fin d) : cutBasisStandardizer Q j₀ * (cutBasisStandardizer Q j₀)ᴴ = 1 := by
  unfold cutBasisStandardizer
  rw [Matrix.conjTranspose_mul]
  calc
    _ = cutMultiplicityLift Q *
        (cutSumStandardizer j₀ * (cutSumStandardizer j₀)ᴴ) * (cutMultiplicityLift Q)ᴴ := by
      simp only [Matrix.mul_assoc]
    _ = 1 := by rw [cutSumStandardizer_mul_star, Matrix.mul_one,
      cutMultiplicityLift_mul_star Q hQ]

/-- Structural standardization for any tuple with a genuine common cut eigenbasis. -/
theorem blockMeasurement_standard_of_cut_diagonalization
    (V : Fin d → Matrix κ κ ℂ) (Q : Matrix κ κ ℂ)
    (hQ : Qᴴ * Q = 1) (hQ' : Q * Qᴴ = 1)
    (a : κ → Fin 4) (j₀ : κ → Fin d)
    (hV : ∀ j, V j = Q * diagonalCutTuple a j₀ j * Qᴴ)
    (t : ℕ) (b : ZMod d) :
    blockClockMeasurement (blockFourierOperator (fun j => sourcePhase j • V j)) t b =
      cutBasisStandardizer Q j₀ *
        (fourierProjector d t b ⊗ₖ (1 : Matrix κ κ ℂ)) * (cutBasisStandardizer Q j₀)ᴴ := by
  have hB : (fun j => sourcePhase j • V j) =
      (fun j => Q * (sourcePhase j • diagonalCutTuple a j₀ j) * Qᴴ) := by
    funext j
    rw [hV j, Matrix.mul_smul, Matrix.smul_mul]
  rw [hB, blockFourierOperator_multiplicity_conjugate,
    blockClockMeasurement_conjugate _ _ (cutMultiplicityLift_star_mul Q hQ)
      (cutMultiplicityLift_mul_star Q hQ') _ _ (cutMultiplicityLift_fixes_computational Q hQ b)]
  change cutMultiplicityLift Q * blockClockMeasurement (diagonalCutClock a j₀) t b *
      (cutMultiplicityLift Q)ᴴ = _
  rw [diagonalCutMeasurement_standard]
  simp only [cutBasisStandardizer, Matrix.conjTranspose_mul, Matrix.mul_assoc]

end
end CGLMPBounds.Companion
