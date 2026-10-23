module

public import CGLMPBounds.Companion.Covariance

@[expose] public section


/-!
# The original measurements as a common reducing summand

The embedding here is `ξ ↦ Σ_a |a⟩ ⊗ P_a^0 ξ`, the outcome/physical part of (C.5).
The transported family is the clock-zero block of the eventual companion family.
Identification with that clock block remains a separate theorem; this module alone
does not claim the full fourth-root or Bell-value conclusion of Lemma C.1.
-/

open Matrix
attribute [-instance] CStarMatrix.instHMulOfFintypeOfMulOfAddCommMonoid

namespace CGLMPBounds.Companion
noncomputable section

variable {d n : ℕ} [NeZero d]

@[simp] lemma conjugator_apply (P : ZMod d → Base n) (p q : OutcomeSpace d n) :
    conjugator P p q = P (q.1 - p.1) p.2 q.2 := rfl

lemma conjugator_star_apply (P : ZMod d → Base n) (hP : IsPVM P)
    (p q : OutcomeSpace d n) : (conjugator P)ᴴ p q = P (p.1 - q.1) p.2 q.2 := by
  exact congrArg (fun X : Base n => X p.2 q.2) (hP.isHermitian (p.1 - q.1)).eq

@[simp] lemma covariant_apply (P : ZMod d → Base n) (a : ZMod d)
    (p q : OutcomeSpace d n) :
    covariant P a p q = if p.1 = q.1 then P (a - p.1) p.2 q.2 else 0 := by
  simp only [covariant, flatten_apply, covariantBlocks, Matrix.diagonal_apply]
  split_ifs <;> rfl

/-- Each coordinate-block inclusion is an isometry. -/
lemma blockEmbedding_star_mul (k : ZMod d) :
    (blockEmbedding (n := n) k)ᴴ * blockEmbedding (n := n) k = (1 : Base n) := by
  ext i j
  simp only [Matrix.mul_apply, Fintype.sum_prod_type, Matrix.conjTranspose_apply,
    blockEmbedding]
  rw [Finset.sum_eq_single_of_mem k (Finset.mem_univ k)]
  · simp only [if_pos rfl]
    change ((1 : Base n)ᴴ * (1 : Base n) : Base n) i j = (1 : Base n) i j
    simp
  · intro a _ ha
    simp [ha]

/-- The `k`th diagonal block of the covariant family is the shifted original family. -/
lemma covariant_mul_blockEmbedding (P : ZMod d → Base n) (a k : ZMod d) :
    covariant P a * blockEmbedding (n := n) k = blockEmbedding (n := n) k * P (a - k) := by
  ext p j
  simp only [Matrix.mul_apply]
  rcases p with ⟨l, i⟩
  by_cases hl : l = k
  · subst l
    simp [Fintype.sum_prod_type, covariant_apply, blockEmbedding,
      Matrix.one_apply, mul_ite, ite_mul]
  · simp [Fintype.sum_prod_type, covariant_apply, blockEmbedding,
      Matrix.one_apply, mul_ite, ite_mul, hl]

/-- The explicit embedding in (C.5) is `Z_0†` applied to the outcome-zero inclusion. -/
lemma conjugator_star_mul_blockEmbedding (P : ZMod d → Base n) (hP : IsPVM P) :
    (conjugator P)ᴴ * blockEmbedding (n := n) (0 : ZMod d) = measurementEmbedding P := by
  ext p j
  simp only [Matrix.mul_apply, Fintype.sum_prod_type]
  simp only [conjugator_star_apply P hP]
  simp [blockEmbedding, measurementEmbedding, Matrix.one_apply, mul_ite, ite_mul]

/-- The outcome/physical part of the reducing isometry in (C.5). -/
theorem measurementEmbedding_star_mul (P : ZMod d → Base n) (hP : IsPVM P) :
    (measurementEmbedding P)ᴴ * measurementEmbedding P = 1 := by
  rw [← conjugator_star_mul_blockEmbedding P hP, Matrix.conjTranspose_mul,
    Matrix.conjTranspose_conjTranspose]
  calc
    ((blockEmbedding (n := n) (0 : ZMod d))ᴴ * conjugator P) *
        ((conjugator P)ᴴ * blockEmbedding (n := n) (0 : ZMod d)) =
      (blockEmbedding (n := n) (0 : ZMod d))ᴴ *
        (conjugator P * (conjugator P)ᴴ) * blockEmbedding (n := n) (0 : ZMod d) := by
          simp only [Matrix.mul_assoc]
    _ = 1 := by rw [conjugator_mul_star P hP, Matrix.mul_one, blockEmbedding_star_mul]

/-- Every transported measurement intertwines with the same original-space embedding. -/
theorem transported_intertwines (P : Fin 4 → ZMod d → Base n) (h0 : IsPVM (P 0))
    (t : Fin 4) (a : ZMod d) :
    transported P t a * measurementEmbedding (P 0) = measurementEmbedding (P 0) * P t a := by
  have hcancel : conjugator (P 0) *
      ((conjugator (P 0))ᴴ * blockEmbedding (n := n) (0 : ZMod d)) =
        blockEmbedding (n := n) (0 : ZMod d) := by
    rw [← Matrix.mul_assoc, conjugator_mul_star (P 0) h0, Matrix.one_mul]
  rw [← conjugator_star_mul_blockEmbedding (P 0) h0]
  simp only [transported, Matrix.mul_assoc]
  rw [hcancel, covariant_mul_blockEmbedding]
  simp only [sub_zero, Matrix.mul_assoc] <;> rfl

lemma transported_isHermitian (P : Fin 4 → ZMod d → Base n)
    (hP : ∀ t, IsPVM (P t)) (t : Fin 4) (a : ZMod d) :
    (transported P t a).IsHermitian := by
  change (transported P t a)ᴴ = transported P t a
  simp only [transported, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose,
    (covariant_isHermitian (P t) (hP t) a).eq, Matrix.mul_assoc]

/-- The range of the common embedding reduces every transported measurement. -/
theorem transported_commutes_range (P : Fin 4 → ZMod d → Base n)
    (hP : ∀ t, IsPVM (P t)) (t : Fin 4) (a : ZMod d) :
    Commute (transported P t a)
      (measurementEmbedding (P 0) * (measurementEmbedding (P 0))ᴴ) := by
  have hi := transported_intertwines P (hP 0) t a
  have hadj : (measurementEmbedding (P 0))ᴴ * transported P t a =
      P t a * (measurementEmbedding (P 0))ᴴ := by
    simpa only [Matrix.conjTranspose_mul, (transported_isHermitian P hP t a).eq,
      ((hP t).isHermitian a).eq] using congrArg Matrix.conjTranspose hi
  change transported P t a *
      (measurementEmbedding (P 0) * (measurementEmbedding (P 0))ᴴ) =
    (measurementEmbedding (P 0) * (measurementEmbedding (P 0))ᴴ) * transported P t a
  rw [← Matrix.mul_assoc, hi, Matrix.mul_assoc, ← hadj, ← Matrix.mul_assoc]

end
end CGLMPBounds.Companion
