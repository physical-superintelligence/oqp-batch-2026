module

public import CGLMPBounds.Companion.Clock
public import CGLMPBounds.Companion.OutcomeValue

@[expose] public section


/-!
# Normalized trace averaging for the weighted clock

The clock has four blocks, so its normalized one-edge cost is the arithmetic mean
of the four transition costs. These identities do not require the transition
matrices to be unitary. The physical dimension is the actual cardinality of the
matrix index type; the factor four is therefore explicit.
-/

open Matrix
namespace CGLMPBounds.Companion
noncomputable section

section BlockRing
variable {R : Type*} [Ring R]

lemma weightedClock_diagonal_sandwich (U : Fin 4 → R) (A B : R) :
    (Matrix.diagonal fun _ : Fin 4 => A) * weightedClock U *
        (Matrix.diagonal fun _ : Fin 4 => B) =
      weightedClock (fun t => A * U t * B) := by
  ext t s
  fin_cases t <;> fin_cases s <;>
    simp [weightedClock, Matrix.mul_apply, Matrix.diagonal_apply, Fin.sum_univ_four]

variable [StarRing R]

lemma weightedClock_mul_star_diagonal (V U : Fin 4 → R) :
    weightedClock V * (weightedClock U)ᴴ =
      Matrix.diagonal (fun t => V t * star (U t)) := by
  ext t s
  fin_cases t <;> fin_cases s <;>
    simp [weightedClock, Matrix.mul_apply, Matrix.diagonal_apply,
      Matrix.conjTranspose_apply, Fin.sum_univ_four]

end BlockRing

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The real part of the trace divided by the dimension of its matrix index type. -/
def meanTraceReal (X : Matrix ι ι ℂ) : ℝ :=
  (Matrix.trace X).re / (Fintype.card ι : ℝ)

lemma trace_clock_flatten (X : Matrix (Fin 4) (Fin 4) (Matrix ι ι ℂ)) :
    Matrix.trace (Matrix.compRingEquiv (Fin 4) ι ℂ X) =
      ∑ t, Matrix.trace (X t t) := by
  simp only [Matrix.trace, Matrix.diag, Matrix.compRingEquiv_apply,
    Matrix.comp_apply, Fintype.sum_prod_type]

lemma clock_trace_pair (U : Fin 4 → Matrix ι ι ℂ) (A B : Matrix ι ι ℂ) :
    Matrix.trace (clockLift A * (clockMatrix U * clockLift B * (clockMatrix U)ᴴ)) =
      ∑ t, Matrix.trace (A * U t * B * (U t)ᴴ) := by
  simp only [clockLift, clockMatrix, ← clock_flatten_star, ← map_mul,
    ← Matrix.mul_assoc]
  rw [weightedClock_diagonal_sandwich, weightedClock_mul_star_diagonal,
    trace_clock_flatten]
  simp only [Matrix.diagonal_apply_eq, Matrix.star_eq_conjTranspose]

/-- Dividing by the enlarged dimension gives the average, with the exact factor `1/4`. -/
theorem meanTraceReal_clock_pair (U : Fin 4 → Matrix ι ι ℂ) (A B : Matrix ι ι ℂ) :
    meanTraceReal (clockLift A * (clockMatrix U * clockLift B * (clockMatrix U)ᴴ)) =
      (∑ t, meanTraceReal (A * U t * B * (U t)ᴴ)) / 4 := by
  unfold meanTraceReal
  rw [clock_trace_pair]
  simp only [Complex.re_sum, Fintype.card_prod, Fintype.card_fin, Nat.cast_mul,
    Nat.cast_ofNat, ← Finset.sum_div, div_div]
  rw [mul_comm (4 : ℝ)]

variable {d : ℕ} [NeZero d]

/-- The oriented residual cost of one ordered pair of outcome families. -/
def outcomeCost (A B : ZMod d → Matrix ι ι ℂ) : ℝ :=
  ∑ a, ∑ b, ((a - b).val : ℝ) * meanTraceReal (A a * B b)

/-- One clock edge is exactly the mean of the four source transition edges. -/
theorem outcomeCost_clock_average (U : Fin 4 → Matrix ι ι ℂ)
    (A B : ZMod d → Matrix ι ι ℂ) :
    outcomeCost (fun a => clockLift (A a))
        (fun b => clockMatrix U * clockLift (B b) * (clockMatrix U)ᴴ) =
      (∑ t, outcomeCost A (fun b => U t * B b * (U t)ᴴ)) / 4 := by
  unfold outcomeCost
  simp_rw [meanTraceReal_clock_pair]
  simp only [mul_div, Finset.mul_sum, ← Finset.sum_div]
  congr 1
  calc
    (∑ a, ∑ b, ∑ t, ((a - b).val : ℝ) *
        meanTraceReal (A a * U t * B b * (U t)ᴴ)) =
      ∑ a, ∑ t, ∑ b, ((a - b).val : ℝ) *
        meanTraceReal (A a * U t * B b * (U t)ᴴ) := by
      apply Finset.sum_congr rfl
      intro a _
      rw [Finset.sum_comm]
    _ = ∑ t, ∑ a, ∑ b, ((a - b).val : ℝ) *
        meanTraceReal (A a * U t * B b * (U t)ᴴ) := by rw [Finset.sum_comm]
    _ = _ := by simp only [Matrix.mul_assoc]

end
end CGLMPBounds.Companion
