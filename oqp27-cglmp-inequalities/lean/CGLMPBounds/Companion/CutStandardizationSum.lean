module

public import CGLMPBounds.Companion.CutStandardizationPVM

@[expose] public section


/-!
# A direct sum of scalar cuts is a standard amplification

The direct sum is written in outcome/multiplicity product coordinates. Each
summand uses its own explicit outcome diagonal, with the original outcome label
retained. The clock on the left is assembled from the literal diagonal cut tuple.
-/

open Matrix
open scoped Kronecker
attribute [-instance] CStarMatrix.instHMulOfFintypeOfMulOfAddCommMonoid

namespace CGLMPBounds.Companion
noncomputable section

section Blocks
variable {α β γ κ : Type*} [Fintype α] [DecidableEq α]
  [Fintype β] [DecidableEq β] [Fintype γ] [DecidableEq γ]
  [Fintype κ] [DecidableEq κ]

/-- A direct sum, with its summand coordinate placed second. -/
def cutSummandMatrix (A : κ → Matrix α β ℂ) : Matrix (α × κ) (β × κ) ℂ :=
  fun p q => if p.2 = q.2 then A p.2 p.1 q.1 else 0

lemma cutSummandMatrix_mul (A : κ → Matrix α β ℂ) (B : κ → Matrix β γ ℂ) :
    cutSummandMatrix A * cutSummandMatrix B = cutSummandMatrix (fun k => A k * B k) := by
  ext p q
  rcases p with ⟨a, u⟩
  rcases q with ⟨c, v⟩
  by_cases huv : u = v
  · subst v
    simp [cutSummandMatrix, Matrix.mul_apply, Fintype.sum_prod_type,
      ite_mul, mul_ite, Finset.sum_ite_eq, Finset.sum_ite_eq']
  · rw [Matrix.mul_apply]
    simp only [cutSummandMatrix, if_neg huv]
    apply Finset.sum_eq_zero
    intro p _
    by_cases hup : u = p.2
    · have hpv : p.2 ≠ v := fun h => huv (hup.trans h)
      simp [hpv]
    · simp [hup]

lemma cutSummandMatrix_star (A : κ → Matrix α β ℂ) :
    (cutSummandMatrix A)ᴴ = cutSummandMatrix (fun k => (A k)ᴴ) := by
  ext p q
  by_cases h : p.2 = q.2
  · simp [cutSummandMatrix, Matrix.conjTranspose_apply, h]
  · simp [cutSummandMatrix, Matrix.conjTranspose_apply, h, Ne.symm h]

lemma cutSummandMatrix_one :
    cutSummandMatrix (fun _ : κ => (1 : Matrix α α ℂ)) = 1 := by
  ext p q
  by_cases h : p.2 = q.2
  · simp [cutSummandMatrix, Matrix.one_apply, Prod.ext_iff, h]
  · simp [cutSummandMatrix, Matrix.one_apply, Prod.ext_iff, h]

lemma cutSummandMatrix_pow (A : κ → Matrix α α ℂ) (t : ℕ) :
    cutSummandMatrix A ^ t = cutSummandMatrix (fun k => A k ^ t) := by
  induction t with
  | zero => simp only [pow_zero, cutSummandMatrix_one]
  | succ t ih =>
    rw [pow_succ, ih, cutSummandMatrix_mul]
    congr 1

lemma cutSummandMatrix_const (A : Matrix α β ℂ) :
    cutSummandMatrix (fun _ : κ => A) = A ⊗ₖ (1 : Matrix κ κ ℂ) := by
  ext p q
  by_cases h : p.2 = q.2 <;>
    simp [cutSummandMatrix, Matrix.kronecker_apply, Matrix.one_apply, h]

end Blocks

variable {d : ℕ} [NeZero d]
variable {κ : Type*} [Fintype κ] [DecidableEq κ]

/-- A literal scalar cut on every multiplicity coordinate. -/
def diagonalCutTuple (a : κ → Fin 4) (j₀ : κ → Fin d) (j : Fin d) : Matrix κ κ ℂ :=
  Matrix.diagonal fun k => Complex.I ^ (Circulation.fourthRootCutLabels (a k) (j₀ k) j).val

/-- The actual C.4 clock of this diagonal tuple. -/
def diagonalCutClock (a : κ → Fin 4) (j₀ : κ → Fin d) :
    Matrix (ZMod d × κ) (ZMod d × κ) ℂ :=
  blockFourierOperator fun j => sourcePhase j • diagonalCutTuple a j₀ j

/-- The literal C.4 measurement formula, for an arbitrary finite multiplicity. -/
def blockClockMeasurement (R : Matrix (ZMod d × κ) (ZMod d × κ) ℂ)
    (t : ℕ) (b : ZMod d) : Matrix (ZMod d × κ) (ZMod d × κ) ℂ :=
  R ^ t * outcomeProjector b * Rᴴ ^ t

lemma diagonalCutClock_eq_sum (a : κ → Fin 4) (j₀ : κ → Fin d) :
    diagonalCutClock a j₀ = cutSummandMatrix (fun k => scalarCutClock (a k) (j₀ k)) := by
  ext p q
  rcases p with ⟨b, u⟩
  rcases q with ⟨c, v⟩
  rw [diagonalCutClock, blockFourierOperator_apply]
  by_cases huv : u = v
  · subst v
    simp only [diagonalCutTuple, Matrix.smul_apply, smul_eq_mul,
      Matrix.diagonal_apply_eq, cutSummandMatrix, if_pos rfl,
      scalarCutClock, scalarFourierClock_apply]
    apply Finset.sum_congr rfl
    intro j _
    unfold entryCoefficient
    ring
  · simp [diagonalCutTuple, Matrix.smul_apply, Matrix.diagonal_apply,
      cutSummandMatrix, huv]

lemma outcomeProjector_eq_sum (b : ZMod d) :
    outcomeProjector (ι := κ) b =
      cutSummandMatrix (fun _ : κ => (Matrix.single b b 1 : Matrix (ZMod d) (ZMod d) ℂ)) := by
  ext p q
  by_cases h : p.2 = q.2 <;> by_cases hp : p.1 = b <;> by_cases hq : q.1 = b <;>
    simp_all [outcomeProjector, cutSummandMatrix, Matrix.diagonal_apply,
      Matrix.single_apply, Prod.ext_iff, eq_comm]

lemma blockClockMeasurement_sum (R : κ → Matrix (ZMod d) (ZMod d) ℂ)
    (t : ℕ) (b : ZMod d) :
    blockClockMeasurement (cutSummandMatrix R) t b =
      cutSummandMatrix (fun k => scalarClockMeasurement (R k) t b) := by
  simp only [blockClockMeasurement, outcomeProjector_eq_sum, cutSummandMatrix_pow,
    cutSummandMatrix_star, cutSummandMatrix_mul, scalarClockMeasurement]

/-- Different cuts use different outcome diagonals, but one common product-space unitary. -/
def cutSumStandardizer (j₀ : κ → Fin d) : Matrix (ZMod d × κ) (Fin d × κ) ℂ :=
  cutSummandMatrix fun k => cutStandardizer (j₀ k)

lemma cutSumStandardizer_star_mul (j₀ : κ → Fin d) :
    (cutSumStandardizer j₀)ᴴ * cutSumStandardizer j₀ = 1 := by
  simp only [cutSumStandardizer, cutSummandMatrix_star, cutSummandMatrix_mul,
    cutStandardizer_star_mul, cutSummandMatrix_one]

lemma cutSumStandardizer_mul_star (j₀ : κ → Fin d) :
    cutSumStandardizer j₀ * (cutSumStandardizer j₀)ᴴ = 1 := by
  simp only [cutSumStandardizer, cutSummandMatrix_star, cutSummandMatrix_mul,
    cutStandardizer_mul_star, cutSummandMatrix_one]

/-- A direct sum of literal cuts is the standard amplification, with the
source outcome labels and all measurement indices unchanged. -/
theorem diagonalCutMeasurement_standard (a : κ → Fin 4) (j₀ : κ → Fin d)
    (t : ℕ) (b : ZMod d) :
    blockClockMeasurement (diagonalCutClock a j₀) t b =
      cutSumStandardizer j₀ *
        (fourierProjector d t b ⊗ₖ (1 : Matrix κ κ ℂ)) * (cutSumStandardizer j₀)ᴴ := by
  rw [diagonalCutClock_eq_sum, blockClockMeasurement_sum]
  simp only [scalarCutMeasurement_standard, cutSumStandardizer,
    ← cutSummandMatrix_const, cutSummandMatrix_star, cutSummandMatrix_mul]

end
end CGLMPBounds.Companion
