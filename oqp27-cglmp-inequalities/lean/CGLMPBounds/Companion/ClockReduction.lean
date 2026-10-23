module

public import CGLMPBounds.Companion.Transitions
public import CGLMPBounds.Companion.Reducing

@[expose] public section


/-!
# The common reducing embedding in the four-dimensional clock

This proves the isometry and all four intertwining identities of (C.5) for the
pre-Fourier clock construction. Reordering tensor factors and diagonalizing the
outcome shift remain subsequent stages of the full companion representation.
-/

open Matrix
attribute [-instance] CStarMatrix.instHMulOfFintypeOfMulOfAddCommMonoid
-- The CStarMatrix fallback is separately registered as a default instance.
attribute [default_instance 110] Matrix.instHMulOfFintypeOfMulOfAddCommMonoid

namespace CGLMPBounds.Companion
noncomputable section

/-- The products of zero, one, two, or three consecutive transitions starting at clock zero. -/
def stepPrefix {M : Type*} [Monoid M] (U : Fin 4 → M) : Fin 4 → M :=
  ![1, U 0, U 0 * U 1, U 0 * U 1 * U 2]

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Include a vector into one clock coordinate. -/
def clockEmbedding (t : Fin 4) : Matrix (Fin 4 × ι) ι ℂ :=
  fun p j => if p.1 = t then (1 : Matrix ι ι ℂ) p.2 j else 0

lemma clockEmbedding_star_mul (t : Fin 4) :
    (clockEmbedding (ι := ι) t)ᴴ * clockEmbedding (ι := ι) t = (1 : Matrix ι ι ℂ) := by
  ext i j
  simp only [Matrix.mul_apply, Fintype.sum_prod_type, Matrix.conjTranspose_apply,
    clockEmbedding]
  rw [Finset.sum_eq_single_of_mem t (Finset.mem_univ t)]
  · simp only [ite_true]
    change (((1 : Matrix ι ι ℂ)ᴴ * (1 : Matrix ι ι ℂ) : Matrix ι ι ℂ)) i j =
      (1 : Matrix ι ι ℂ) i j
    simp
  · intro s _ hs
    simp [hs]

lemma comp_mul_clockEmbedding (B : Matrix (Fin 4) (Fin 4) (Matrix ι ι ℂ))
    (t : Fin 4) :
    (Matrix.compRingEquiv (Fin 4) ι ℂ B * clockEmbedding (ι := ι) t :
      Matrix (Fin 4 × ι) ι ℂ) =
      fun p j => B p.1 t p.2 j := by
  ext p j
  simp [Matrix.mul_apply, Fintype.sum_prod_type, Matrix.compRingEquiv_apply,
    Matrix.comp_apply, clockEmbedding, Matrix.one_apply, mul_ite, ite_mul]

lemma clockMatrix_mul_embedding (U : Fin 4 → Matrix ι ι ℂ) (t : Fin 4) :
    clockMatrix U * clockEmbedding (ι := ι) (t + 1) = clockEmbedding (ι := ι) t * U t := by
  rw [clockMatrix, comp_mul_clockEmbedding]
  ext p j
  rcases p with ⟨s, i⟩
  fin_cases s <;> fin_cases t <;>
    simp [weightedClock, clockEmbedding, Matrix.mul_apply, Matrix.one_apply,
      mul_ite, ite_mul]

lemma clockMatrix_star_mul_embedding (U : Fin 4 → Matrix ι ι ℂ) (t : Fin 4) :
    (clockMatrix U)ᴴ * clockEmbedding (ι := ι) t = clockEmbedding (ι := ι) (t + 1) * (U t)ᴴ := by
  rw [clockMatrix, ← clock_flatten_star, comp_mul_clockEmbedding]
  ext p j
  rcases p with ⟨s, i⟩
  fin_cases s <;> fin_cases t <;>
    simp [weightedClock, clockEmbedding, Matrix.mul_apply, Matrix.one_apply,
      Matrix.conjTranspose_apply, mul_ite, ite_mul]

lemma clockLift_mul_embedding (C : Matrix ι ι ℂ) (t : Fin 4) :
    clockLift C * clockEmbedding (ι := ι) t = clockEmbedding (ι := ι) t * C := by
  rw [clockLift, comp_mul_clockEmbedding]
  ext p j
  by_cases hp : p.1 = t
  · simp [Matrix.diagonal_apply, clockEmbedding, Matrix.mul_apply,
      Matrix.one_apply, hp, mul_ite, ite_mul]
  · simp [Matrix.diagonal_apply, clockEmbedding, Matrix.mul_apply,
      Matrix.one_apply, hp, mul_ite, ite_mul]

lemma clockMatrix_pow_mul_embedding (U : Fin 4 → Matrix ι ι ℂ) (t : Fin 4) :
    clockMatrix U ^ t.val * clockEmbedding (ι := ι) t = clockEmbedding (ι := ι) 0 * stepPrefix U t := by
  have h0 : clockMatrix U * clockEmbedding (ι := ι) 1 =
      clockEmbedding (ι := ι) 0 * U 0 := clockMatrix_mul_embedding U 0
  have h1 : clockMatrix U * clockEmbedding (ι := ι) 2 =
      clockEmbedding (ι := ι) 1 * U 1 := clockMatrix_mul_embedding U 1
  have h2 : clockMatrix U * clockEmbedding (ι := ι) 3 =
      clockEmbedding (ι := ι) 2 * U 2 := clockMatrix_mul_embedding U 2
  have hp2 : clockMatrix U ^ 2 * clockEmbedding (ι := ι) 2 = clockEmbedding (ι := ι) 0 * (U 0 * U 1) := by
    rw [pow_two, Matrix.mul_assoc, h1, ← Matrix.mul_assoc, h0, Matrix.mul_assoc]
  have hp3 : clockMatrix U ^ 3 * clockEmbedding (ι := ι) 3 =
      clockEmbedding (ι := ι) 0 * (U 0 * U 1 * U 2) := by
    rw [pow_succ, Matrix.mul_assoc, h2, ← Matrix.mul_assoc, hp2, Matrix.mul_assoc]
  fin_cases t
  · simp [stepPrefix]
  · change clockMatrix U ^ 1 * clockEmbedding (ι := ι) 1 =
      clockEmbedding (ι := ι) 0 * U 0
    simpa only [pow_one] using h0
  · exact hp2
  · exact hp3

lemma clockMatrix_star_pow_mul_embedding (U : Fin 4 → Matrix ι ι ℂ) (t : Fin 4) :
    (clockMatrix U)ᴴ ^ t.val * clockEmbedding (ι := ι) 0 = clockEmbedding (ι := ι) t * (stepPrefix U t)ᴴ := by
  have h0 : (clockMatrix U)ᴴ * clockEmbedding (ι := ι) 0 =
      clockEmbedding (ι := ι) 1 * (U 0)ᴴ := clockMatrix_star_mul_embedding U 0
  have h1 : (clockMatrix U)ᴴ * clockEmbedding (ι := ι) 1 =
      clockEmbedding (ι := ι) 2 * (U 1)ᴴ := clockMatrix_star_mul_embedding U 1
  have h2 : (clockMatrix U)ᴴ * clockEmbedding (ι := ι) 2 =
      clockEmbedding (ι := ι) 3 * (U 2)ᴴ := clockMatrix_star_mul_embedding U 2
  have hp2 : (clockMatrix U)ᴴ ^ 2 * clockEmbedding (ι := ι) 0 =
      clockEmbedding (ι := ι) 2 * (U 1)ᴴ * (U 0)ᴴ := by
    rw [pow_two, Matrix.mul_assoc, h0, ← Matrix.mul_assoc, h1]
  have hp3 : (clockMatrix U)ᴴ ^ 3 * clockEmbedding (ι := ι) 0 =
      clockEmbedding (ι := ι) 3 * (U 2)ᴴ * (U 1)ᴴ * (U 0)ᴴ := by
    rw [pow_succ', Matrix.mul_assoc, hp2, ← Matrix.mul_assoc, ← Matrix.mul_assoc, h2]
  fin_cases t
  · simp [stepPrefix]
  · change (clockMatrix U)ᴴ ^ 1 * clockEmbedding (ι := ι) 0 =
      clockEmbedding (ι := ι) 1 * (U 0)ᴴ
    simpa only [pow_one] using h0
  · change (clockMatrix U)ᴴ ^ 2 * clockEmbedding (ι := ι) 0 =
      clockEmbedding (ι := ι) 2 * (U 0 * U 1)ᴴ
    simpa only [Matrix.conjTranspose_mul, Matrix.mul_assoc] using hp2
  · change (clockMatrix U)ᴴ ^ 3 * clockEmbedding (ι := ι) 0 =
      clockEmbedding (ι := ι) 3 * (U 0 * U 1 * U 2)ᴴ
    simpa only [Matrix.conjTranspose_mul, Matrix.mul_assoc] using hp3

/-- Conjugating a clock-independent operator gives the source prefix conjugation in clock zero. -/
theorem clock_conjugation_zero (U : Fin 4 → Matrix ι ι ℂ) (C : Matrix ι ι ℂ)
    (t : Fin 4) :
    (clockMatrix U ^ t.val * clockLift C * (clockMatrix U)ᴴ ^ t.val) * clockEmbedding (ι := ι) 0 =
      clockEmbedding (ι := ι) 0 * (stepPrefix U t * C * (stepPrefix U t)ᴴ) := by
  rw [Matrix.mul_assoc, Matrix.mul_assoc, clockMatrix_star_pow_mul_embedding,
    ← Matrix.mul_assoc (clockLift C), clockLift_mul_embedding]
  rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, clockMatrix_pow_mul_embedding]
  simp only [Matrix.mul_assoc]

lemma stepPrefix_transitions {G : Type*} [Group G] (Z : Fin 4 → G) (J : G) (t : Fin 4) :
    stepPrefix (transitions Z J) t = (Z 0)⁻¹ * Z t := by
  fin_cases t <;> simp [stepPrefix, transitions, mul_assoc]

variable {d n : ℕ} [NeZero d]

/-- The source measurements (C.4), in the original clock/outcome/physical ordering. -/
def clockMeasurement (P : Fin 4 → ZMod d → Base n) (hP : ∀ t, IsPVM (P t))
    (t : Fin 4) (a : ZMod d) :
    Matrix (Fin 4 × OutcomeSpace d n) (Fin 4 × OutcomeSpace d n) ℂ :=
  companionClock P hP ^ t.val * clockLift (computational (n := n) a) *
    (companionClock P hP)ᴴ ^ t.val

/-- The common isometry (C.5), before swapping the clock and outcome coordinates. -/
def commonEmbedding (P : Fin 4 → ZMod d → Base n) :
    Matrix (Fin 4 × OutcomeSpace d n) (Fin n) ℂ :=
  clockEmbedding 0 * measurementEmbedding (P 0)

/-- In coordinates this is exactly the sum in (C.5), with clock and outcome factors swapped. -/
lemma commonEmbedding_apply (P : Fin 4 → ZMod d → Base n)
    (p : Fin 4 × OutcomeSpace d n) (j : Fin n) :
    commonEmbedding P p j = if p.1 = 0 then P 0 p.2.1 p.2.2 j else 0 := by
  simp [commonEmbedding, clockEmbedding, measurementEmbedding, Matrix.mul_apply,
    Matrix.one_apply, mul_ite, ite_mul]

lemma source_prefix (P : Fin 4 → ZMod d → Base n) (hP : ∀ t, IsPVM (P t)) (t : Fin 4) :
    stepPrefix (fun s =>
      (transitions (G := Matrix.unitaryGroup (OutcomeSpace d n) ℂ)
        (fun u => unitaryConjugator (P u) (hP u))
        (unitaryShift (d := d) (n := n)) s : OutcomeMat d n)) t =
      (conjugator (P 0))ᴴ * conjugator (P t) := by
  have h := congrArg (fun U : Matrix.unitaryGroup (OutcomeSpace d n) ℂ =>
      (U : OutcomeMat d n))
    (stepPrefix_transitions (fun u => unitaryConjugator (P u) (hP u))
      (unitaryShift (d := d) (n := n)) t)
  fin_cases t <;> exact h

lemma clockMeasurement_zero (P : Fin 4 → ZMod d → Base n) (hP : ∀ t, IsPVM (P t))
    (t : Fin 4) (a : ZMod d) :
    clockMeasurement P hP t a * clockEmbedding 0 = clockEmbedding 0 * transported P t a := by
  rw [clockMeasurement, companionClock, clock_conjugation_zero, source_prefix]
  congr 1
  rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose]
  calc
    (conjugator (P 0))ᴴ * conjugator (P t) * computational a *
        ((conjugator (P t))ᴴ * conjugator (P 0)) =
      (conjugator (P 0))ᴴ *
        (conjugator (P t) * computational a * (conjugator (P t))ᴴ) * conjugator (P 0) := by
          simp only [Matrix.mul_assoc]
    _ = transported P t a := by rw [conjugator_covariance (P t) (hP t) a]; rfl

/-- The clock/outcome embedding is an isometry, with no restriction on outcome ranks. -/
theorem commonEmbedding_star_mul (P : Fin 4 → ZMod d → Base n) (hP : ∀ t, IsPVM (P t)) :
    (commonEmbedding P)ᴴ * commonEmbedding P = 1 := by
  simp only [commonEmbedding, Matrix.conjTranspose_mul, Matrix.mul_assoc]
  rw [← Matrix.mul_assoc (clockEmbedding 0)ᴴ (clockEmbedding 0), clockEmbedding_star_mul,
    Matrix.one_mul, measurementEmbedding_star_mul (P 0) (hP 0)]

/-- All four measurements preserve the same embedded original PVMs, as required in (C.5). -/
theorem clockMeasurement_intertwines (P : Fin 4 → ZMod d → Base n)
    (hP : ∀ t, IsPVM (P t)) (t : Fin 4) (a : ZMod d) :
    clockMeasurement P hP t a * commonEmbedding P = commonEmbedding P * P t a := by
  unfold commonEmbedding
  rw [← Matrix.mul_assoc, clockMeasurement_zero, Matrix.mul_assoc,
    transported_intertwines P (hP 0) t a, ← Matrix.mul_assoc]

lemma computational_isHermitian (a : ZMod d) :
    (computational (n := n) a).IsHermitian := by
  change (flatten (computationalBlocks a))ᴴ = flatten (computationalBlocks a)
  rw [← flatten_star]
  congr 1
  simp only [computationalBlocks, Matrix.diagonal_conjTranspose]
  congr 1
  funext k
  split_ifs with h <;> simp [h]

lemma clockMeasurement_isHermitian (P : Fin 4 → ZMod d → Base n)
    (hP : ∀ t, IsPVM (P t)) (t : Fin 4) (a : ZMod d) :
    (clockMeasurement P hP t a).IsHermitian := by
  have hC : (clockLift (computational (n := n) a)).IsHermitian := by
    change (Matrix.compRingEquiv (Fin 4) (OutcomeSpace d n) ℂ
      (Matrix.diagonal fun _ : Fin 4 => computational a))ᴴ = _
    rw [← clock_flatten_star]
    congr 1
    simp only [Matrix.diagonal_conjTranspose]
    congr 1
    funext k
    exact (computational_isHermitian a).eq
  change (clockMeasurement P hP t a)ᴴ = clockMeasurement P hP t a
  simp only [clockMeasurement, Matrix.conjTranspose_mul, Matrix.conjTranspose_pow,
    Matrix.conjTranspose_conjTranspose, hC.eq, Matrix.mul_assoc]

/-- Self-adjointness turns the shared intertwining subspace into a common reducing subspace. -/
theorem clockMeasurement_commutes_range (P : Fin 4 → ZMod d → Base n)
    (hP : ∀ t, IsPVM (P t)) (t : Fin 4) (a : ZMod d) :
    Commute (clockMeasurement P hP t a) (commonEmbedding P * (commonEmbedding P)ᴴ) := by
  have hi := clockMeasurement_intertwines P hP t a
  have hadj : (commonEmbedding P)ᴴ * clockMeasurement P hP t a =
      P t a * (commonEmbedding P)ᴴ := by
    simpa only [Matrix.conjTranspose_mul, (clockMeasurement_isHermitian P hP t a).eq,
      ((hP t).isHermitian a).eq] using congrArg Matrix.conjTranspose hi
  change clockMeasurement P hP t a * (commonEmbedding P * (commonEmbedding P)ᴴ) =
    (commonEmbedding P * (commonEmbedding P)ᴴ) * clockMeasurement P hP t a
  rw [← Matrix.mul_assoc, hi, Matrix.mul_assoc, ← hadj, ← Matrix.mul_assoc]

end
end CGLMPBounds.Companion
