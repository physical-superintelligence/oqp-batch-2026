module

public import CGLMPBounds.Companion.BlockNormalization
public import CGLMPBounds.Companion.ClockReduction

@[expose] public section


/-!
# The actual companion tuple and its common reducing embedding

Reorder the already constructed clock into outcome / clock / physical coordinates,
then apply frequency-block normalization. The multiplicity space has dimension
`4*n`. The resulting tuple retains the source's common isometry. The Bell-gap
coefficient identity is a separate, still required part of Lemma C.1.
-/

open Matrix
open scoped Kronecker
attribute [-instance] CStarMatrix.instHMulOfFintypeOfMulOfAddCommMonoid

namespace CGLMPBounds.Companion
noncomputable section

variable {d n : ℕ} [NeZero d]

abbrev CompanionMultiplicity (n : ℕ) := Fin 4 × Fin n
abbrev CompanionSpace (d n : ℕ) := ZMod d × CompanionMultiplicity n
abbrev CompanionMat (d n : ℕ) := Matrix (CompanionSpace d n) (CompanionSpace d n) ℂ

lemma card_companionMultiplicity : Fintype.card (CompanionMultiplicity n) = 4 * n := by
  simp [CompanionMultiplicity]

/-- Swap only the clock and outcome factors, retaining the original physical coordinate. -/
def clockOutcomeEquiv : (Fin 4 × OutcomeSpace d n) ≃ CompanionSpace d n where
  toFun p := (p.2.1, (p.1, p.2.2))
  invFun p := (p.2.1, (p.1, p.2.2))
  left_inv := by rintro ⟨t, a, i⟩; rfl
  right_inv := by rintro ⟨a, t, i⟩; rfl

def clockReindex :
    Matrix (Fin 4 × OutcomeSpace d n) (Fin 4 × OutcomeSpace d n) ℂ ≃+* CompanionMat d n :=
  Matrix.reindexRingEquiv ℂ clockOutcomeEquiv

lemma clockReindex_apply
    (X : Matrix (Fin 4 × OutcomeSpace d n) (Fin 4 × OutcomeSpace d n) ℂ)
    (a b : ZMod d) (t s : Fin 4) (i j : Fin n) :
    clockReindex X (a, (t, i)) (b, (s, j)) = X (t, (a, i)) (s, (b, j)) := rfl

lemma clockReindex_star
    (X : Matrix (Fin 4 × OutcomeSpace d n) (Fin 4 × OutcomeSpace d n) ℂ) :
    clockReindex Xᴴ = (clockReindex X)ᴴ := rfl

lemma clockLift_apply {κ : Type*} [Fintype κ] [DecidableEq κ]
    (C : Matrix κ κ ℂ) (t s : Fin 4) (u v : κ) :
    clockLift C (t, u) (s, v) = if t = s then C u v else 0 := by
  simp [clockLift, Matrix.compRingEquiv_apply, Matrix.comp_apply, Matrix.diagonal_apply,
    Matrix.ite_apply]

lemma shift_apply (a b : ZMod d) (i j : Fin n) :
    shift (a, i) (b, j) = outcomeShift a b * (1 : Base n) i j := by
  change (((Equiv.addRight (1 : ZMod d)).permMatrix (Base n)) a b) i j =
    ((Equiv.addRight (1 : ZMod d)).permMatrix ℂ) a b * (1 : Base n) i j
  unfold Equiv.Perm.permMatrix
  rw [PEquiv.toMatrix_toPEquiv_apply, PEquiv.toMatrix_toPEquiv_apply]
  by_cases h : (Equiv.addRight (1 : ZMod d)) a = b
  · simp [Pi.single_apply, Matrix.ite_apply, h, eq_comm]
  · simp [Pi.single_apply, Matrix.ite_apply, h, Ne.symm h]

lemma clockReindex_lift_shift :
    clockReindex (clockLift (shift (d := d) (n := n))) =
      outcomeShift ⊗ₖ (1 : Matrix (CompanionMultiplicity n) (CompanionMultiplicity n) ℂ) := by
  ext p q
  rcases p with ⟨a, t, i⟩
  rcases q with ⟨b, s, j⟩
  rw [clockReindex_apply, clockLift_apply, shift_apply, Matrix.kronecker_apply]
  by_cases h : t = s
  · subst s
    simp [Matrix.one_apply, Prod.mk.injEq]
  · simp [Matrix.one_apply, Prod.mk.injEq, h]

/-- The source's computational projectors in the outcome / clock / physical ordering. -/
def sourceComputational (a : ZMod d) : CompanionMat d n :=
  Matrix.diagonal fun p => if p.1 = a then 1 else 0

lemma clockReindex_computational (a : ZMod d) :
    clockReindex (clockLift (computational (n := n) a)) = sourceComputational a := by
  ext p q
  rcases p with ⟨k, t, i⟩
  rcases q with ⟨l, s, j⟩
  rw [clockReindex_apply, clockLift_apply]
  by_cases hts : t = s <;> by_cases hkl : k = l <;> by_cases hij : i = j <;>
    by_cases hka : k = a <;>
    simp [computational, computationalBlocks, flatten_apply, Matrix.diagonal_apply,
      Matrix.ite_apply, Matrix.one_apply, sourceComputational, Prod.mk.injEq, hts, hkl, hij, hka]

def sourceClock (P : Fin 4 → ZMod d → Base n) (hP : ∀ t, IsPVM (P t)) : CompanionMat d n :=
  clockReindex (companionClock P hP)

lemma sourceClock_star_mul (P : Fin 4 → ZMod d → Base n) (hP : ∀ t, IsPVM (P t)) :
    (sourceClock P hP)ᴴ * sourceClock P hP = 1 := by
  simpa only [map_mul, map_one, clockReindex_star, sourceClock] using
    congrArg (clockReindex (d := d) (n := n)) (companionClock_star_mul P hP)

lemma sourceClock_mul_star (P : Fin 4 → ZMod d → Base n) (hP : ∀ t, IsPVM (P t)) :
    sourceClock P hP * (sourceClock P hP)ᴴ = 1 := by
  simpa only [map_mul, map_one, clockReindex_star, sourceClock] using
    congrArg (clockReindex (d := d) (n := n)) (companionClock_mul_star P hP)

lemma sourceClock_fourth (P : Fin 4 → ZMod d → Base n) (hP : ∀ t, IsPVM (P t)) :
    sourceClock P hP ^ 4 =
      outcomeShift ⊗ₖ (1 : Matrix (CompanionMultiplicity n) (CompanionMultiplicity n) ℂ) := by
  simpa only [map_pow, sourceClock, clockReindex_lift_shift] using
    congrArg (clockReindex (d := d) (n := n)) (companionClock_fourth P hP)

def sourceMeasurement (P : Fin 4 → ZMod d → Base n) (hP : ∀ t, IsPVM (P t))
    (t : Fin 4) (a : ZMod d) : CompanionMat d n :=
  sourceClock P hP ^ t.val * sourceComputational a * (sourceClock P hP)ᴴ ^ t.val

lemma clockReindex_measurement (P : Fin 4 → ZMod d → Base n) (hP : ∀ t, IsPVM (P t))
    (t : Fin 4) (a : ZMod d) :
    clockReindex (clockMeasurement P hP t a) = sourceMeasurement P hP t a := by
  simp only [clockMeasurement, sourceMeasurement, map_mul, map_pow,
    clockReindex_computational, clockReindex_star, sourceClock]

/-- The same original-strategy embedding, after swapping clock and outcome coordinates. -/
def sourceEmbedding (P : Fin 4 → ZMod d → Base n) :
    Matrix (CompanionSpace d n) (Fin n) ℂ :=
  (commonEmbedding P).submatrix clockOutcomeEquiv.symm id

lemma sourceEmbedding_apply (P : Fin 4 → ZMod d → Base n)
    (a : ZMod d) (t : Fin 4) (i j : Fin n) :
    sourceEmbedding P (a, (t, i)) j = if t = 0 then P 0 a i j else 0 :=
  commonEmbedding_apply P (t, (a, i)) j

lemma sourceEmbedding_star_mul (P : Fin 4 → ZMod d → Base n) (hP : ∀ t, IsPVM (P t)) :
    (sourceEmbedding P)ᴴ * sourceEmbedding P = 1 := by
  simp only [sourceEmbedding, Matrix.conjTranspose_submatrix, Matrix.submatrix_mul_equiv,
    commonEmbedding_star_mul P hP, Matrix.submatrix_id_id]

lemma sourceMeasurement_intertwines (P : Fin 4 → ZMod d → Base n)
    (hP : ∀ t, IsPVM (P t)) (t : Fin 4) (a : ZMod d) :
    sourceMeasurement P hP t a * sourceEmbedding P = sourceEmbedding P * P t a := by
  rw [← clockReindex_measurement]
  change (clockMeasurement P hP t a).submatrix clockOutcomeEquiv.symm clockOutcomeEquiv.symm *
      (commonEmbedding P).submatrix clockOutcomeEquiv.symm id =
    (commonEmbedding P).submatrix clockOutcomeEquiv.symm id * P t a
  rw [Matrix.submatrix_mul_equiv, clockMeasurement_intertwines P hP t a]
  exact (Matrix.submatrix_mul_equiv (commonEmbedding P) (P t a)
    clockOutcomeEquiv.symm (Equiv.refl (Fin n)) id).symm

lemma sourceMeasurement_isHermitian (P : Fin 4 → ZMod d → Base n)
    (hP : ∀ t, IsPVM (P t)) (t : Fin 4) (a : ZMod d) :
    (sourceMeasurement P hP t a).IsHermitian := by
  change (sourceMeasurement P hP t a)ᴴ = sourceMeasurement P hP t a
  rw [← clockReindex_measurement, ← clockReindex_star,
    (clockMeasurement_isHermitian P hP t a).eq]

/-- The tuple-clock formula in the coordinates of (C.4). -/
def tupleClock (V : Fin d → Matrix.unitaryGroup (CompanionMultiplicity n) ℂ) : CompanionMat d n :=
  liftedFourier * frequencyDiagonal (fun j => sourcePhase j •
    (V j : Matrix (CompanionMultiplicity n) (CompanionMultiplicity n) ℂ)) * (liftedFourier)ᴴ

def tupleMeasurement (V : Fin d → Matrix.unitaryGroup (CompanionMultiplicity n) ℂ)
    (t : Fin 4) (a : ZMod d) : CompanionMat d n :=
  tupleClock V ^ t.val * sourceComputational a * (tupleClock V)ᴴ ^ t.val

/-- The actual tuple, its fourth-root equations, and the common original reducing summand.
This is the representation part of C.1. -/
theorem exists_companion_tuple_reducing (P : Fin 4 → ZMod d → Base n)
    (hP : ∀ t, IsPVM (P t)) :
    ∃ V : Fin d → Matrix.unitaryGroup (CompanionMultiplicity n) ℂ,
      (∀ j, (V j : Matrix (CompanionMultiplicity n) (CompanionMultiplicity n) ℂ) ^ 4 = 1) ∧
      sourceClock P hP = tupleClock V ∧
      (sourceEmbedding P)ᴴ * sourceEmbedding P = 1 ∧
      (∀ t a, tupleMeasurement V t a * sourceEmbedding P = sourceEmbedding P * P t a) ∧
      (∀ t a, Commute (tupleMeasurement V t a) (sourceEmbedding P * (sourceEmbedding P)ᴴ)) := by
  obtain ⟨V, hVfour, hVclock⟩ := fourthRoot_frequency_representation (sourceClock P hP)
    (sourceClock_star_mul P hP) (sourceClock_mul_star P hP) (sourceClock_fourth P hP)
  change sourceClock P hP = tupleClock V at hVclock
  have hM : ∀ t a, tupleMeasurement V t a = sourceMeasurement P hP t a := by
    intro t a
    simp only [tupleMeasurement, sourceMeasurement, hVclock]
  refine ⟨V, hVfour, hVclock, sourceEmbedding_star_mul P hP, ?_, ?_⟩
  · intro t a
    rw [hM]
    exact sourceMeasurement_intertwines P hP t a
  · intro t a
    rw [hM]
    have hi := sourceMeasurement_intertwines P hP t a
    have hadj : (sourceEmbedding P)ᴴ * sourceMeasurement P hP t a =
        P t a * (sourceEmbedding P)ᴴ := by
      simpa only [Matrix.conjTranspose_mul, (sourceMeasurement_isHermitian P hP t a).eq,
        ((hP t).isHermitian a).eq] using congrArg Matrix.conjTranspose hi
    change sourceMeasurement P hP t a * (sourceEmbedding P * (sourceEmbedding P)ᴴ) =
      (sourceEmbedding P * (sourceEmbedding P)ᴴ) * sourceMeasurement P hP t a
    rw [← Matrix.mul_assoc, hi, Matrix.mul_assoc, ← hadj, ← Matrix.mul_assoc]

end
end CGLMPBounds.Companion
