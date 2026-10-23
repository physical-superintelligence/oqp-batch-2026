module

public import CGLMPBounds.Companion.ClockCost
public import CGLMPBounds.Companion.Transitions

@[expose] public section


/-!
# The transition costs and the twisted closing edge

Cyclic trace telescopes each transition `Z_t† Z_(t+1)` to the corresponding
covariant pair. For the last transition, `Z₄ = Z₀ J` produces outcome `b−1`.
Combining this with clock averaging retains the source's normalized factor four.
-/

open Matrix
namespace CGLMPBounds.Companion
noncomputable section

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

lemma trace_transition_pair (A B Z W : Matrix ι ι ℂ) :
    Matrix.trace (A * ((Zᴴ * W) * B * (Zᴴ * W)ᴴ)) =
      Matrix.trace ((Z * A * Zᴴ) * (W * B * Wᴴ)) := by
  rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose]
  calc
    Matrix.trace (A * (Zᴴ * W * B * (Wᴴ * Z))) =
        Matrix.trace ((A * Zᴴ * W * B * Wᴴ) * Z) := by
      simp only [Matrix.mul_assoc]
    _ = Matrix.trace (Z * (A * Zᴴ * W * B * Wᴴ)) := Matrix.trace_mul_comm _ _
    _ = Matrix.trace ((Z * A * Zᴴ) * (W * B * Wᴴ)) := by
      simp only [Matrix.mul_assoc]

lemma meanTraceReal_transition_pair (A B Z W : Matrix ι ι ℂ) :
    meanTraceReal (A * ((Zᴴ * W) * B * (Zᴴ * W)ᴴ)) =
      meanTraceReal ((Z * A * Zᴴ) * (W * B * Wᴴ)) := by
  unfold meanTraceReal
  rw [trace_transition_pair]

variable {d n : ℕ} [NeZero d]

/-- The source's next conjugator, including `Z₄=Z₀J`. -/
def nextConjugator (P : Fin 4 → ZMod d → Base n) : Fin 4 → OutcomeMat d n :=
  ![conjugator (P 1), conjugator (P 2), conjugator (P 3),
    conjugator (P 0) * shift]

/-- The next covariant outcome family, including the final outcome shift. -/
def nextCovariant (P : Fin 4 → ZMod d → Base n) : Fin 4 → ZMod d → OutcomeMat d n :=
  ![covariant (P 1), covariant (P 2), covariant (P 3),
    fun b => covariant (P 0) (b - 1)]

lemma nextConjugator_covariance (P : Fin 4 → ZMod d → Base n)
    (hP : ∀ t, IsPVM (P t)) (t : Fin 4) (b : ZMod d) :
    nextConjugator P t * computational b * (nextConjugator P t)ᴴ =
      nextCovariant P t b := by
  fin_cases t
  · exact conjugator_covariance (P 1) (hP 1) b
  · exact conjugator_covariance (P 2) (hP 2) b
  · exact conjugator_covariance (P 3) (hP 3) b
  · change (conjugator (P 0) * shift) * computational b *
        (conjugator (P 0) * shift)ᴴ = covariant (P 0) (b - 1)
    rw [Matrix.conjTranspose_mul]
    calc
      (conjugator (P 0) * shift) * computational b *
          ((shift)ᴴ * (conjugator (P 0))ᴴ) =
        conjugator (P 0) * (shift * computational b * (shift)ᴴ) *
          (conjugator (P 0))ᴴ := by simp only [Matrix.mul_assoc]
      _ = covariant (P 0) (b - 1) := by
        rw [shift_computational, conjugator_covariance (P 0) (hP 0)]

lemma transition_matrix_eq (P : Fin 4 → ZMod d → Base n)
    (hP : ∀ t, IsPVM (P t)) (t : Fin 4) :
    (transitions (G := Matrix.unitaryGroup (OutcomeSpace d n) ℂ)
            (fun s => unitaryConjugator (P s) (hP s))
            (unitaryShift (d := d) (n := n)) t :
        OutcomeMat d n) = (conjugator (P t))ᴴ * nextConjugator P t := by
  fin_cases t
  · rfl
  · rfl
  · rfl
  · change (conjugator (P 3))ᴴ * conjugator (P 0) * shift =
      (conjugator (P 3))ᴴ * (conjugator (P 0) * shift)
    exact Matrix.mul_assoc _ _ _

/-- The normalized cost of each source transition is its covariant edge cost. -/
theorem outcomeCost_transition (P : Fin 4 → ZMod d → Base n)
    (hP : ∀ t, IsPVM (P t)) (t : Fin 4) :
    outcomeCost (computational (n := n))
        (fun b =>
          (transitions (G := Matrix.unitaryGroup (OutcomeSpace d n) ℂ)
            (fun s => unitaryConjugator (P s) (hP s))
            (unitaryShift (d := d) (n := n)) t :
              OutcomeMat d n) * computational b *
          (transitions (G := Matrix.unitaryGroup (OutcomeSpace d n) ℂ)
            (fun s => unitaryConjugator (P s) (hP s))
            (unitaryShift (d := d) (n := n)) t :
              OutcomeMat d n)ᴴ) =
      outcomeCost (covariant (P t)) (nextCovariant P t) := by
  unfold outcomeCost
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro b _
  simp only [transition_matrix_eq]
  rw [meanTraceReal_transition_pair,
    conjugator_covariance (P t) (hP t), nextConjugator_covariance P hP]

/-- One companion-clock edge equals one quarter of the covariant four-edge cycle. -/
theorem companionClock_cost_average (P : Fin 4 → ZMod d → Base n)
    (hP : ∀ t, IsPVM (P t)) :
    outcomeCost (fun a => clockLift (computational (n := n) a))
        (fun b => companionClock P hP * clockLift (computational b) *
          (companionClock P hP)ᴴ) =
      (∑ t, outcomeCost (covariant (P t)) (nextCovariant P t)) / 4 := by
  simp only [companionClock, outcomeCost_clock_average]
  congr 1
  apply Finset.sum_congr rfl
  intro t _
  exact outcomeCost_transition P hP t

/-- Simultaneous outcome covariance preserves each oriented pair cost. -/
theorem outcomeCost_covariant (P Q : ZMod d → Base n) :
    outcomeCost (covariant P) (covariant Q) = outcomeCost P Q := by
  have h := context_cost_average (tracialTable (fun _ => P) (fun _ => Q)) 0 0
  rw [← covariantTable_eq_average] at h
  simpa only [outcomeCost, meanTraceReal, covariantTable, tracialTable, residual,
    ite_true, Fintype.card_prod, Fintype.card_fin, ZMod.card, Nat.cast_mul] using h

lemma covariant_relabel_sub_one (P : ZMod d → Base n) :
    covariant (fun a => P (a - 1)) = fun b => covariant P (b - 1) := by
  funext b
  unfold covariant covariantBlocks
  congr 1
  congr 1
  funext k
  congr 1
  abel

/-- The four oriented costs in cyclic PVM order, with the closing residual shift. -/
def cycleCost (P : Fin 4 → ZMod d → Base n) : ℝ :=
  outcomeCost (P 0) (P 1) + outcomeCost (P 1) (P 2) +
    outcomeCost (P 2) (P 3) + outcomeCost (P 3) (fun b => P 0 (b - 1))

lemma covariant_cycleCost (P : Fin 4 → ZMod d → Base n) :
    (∑ t, outcomeCost (covariant (P t)) (nextCovariant P t)) = cycleCost P := by
  simp only [Fin.sum_univ_four, nextCovariant, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons]
  rw [← covariant_relabel_sub_one]
  simp only [outcomeCost_covariant, cycleCost, add_assoc]

/-- The source's clock averaging, including the covariant and twisted-edge identifications. -/
theorem companionClock_cost_original (P : Fin 4 → ZMod d → Base n)
    (hP : ∀ t, IsPVM (P t)) :
    outcomeCost (fun a => clockLift (computational (n := n) a))
        (fun b => companionClock P hP * clockLift (computational b) *
          (companionClock P hP)ᴴ) = cycleCost P / 4 := by
  rw [companionClock_cost_average, covariant_cycleCost]

end
end CGLMPBounds.Companion
