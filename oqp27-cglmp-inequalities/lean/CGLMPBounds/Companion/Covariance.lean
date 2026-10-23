module

public import CGLMPBounds.Defs.Companion
public import CGLMPBounds.LocalContent.Tracial

@[expose] public section


/-!
# Outcome covariance in the companion construction

This is the first finite-algebra stage of Lemma C.1 (supplement p. 6).
It proves unitarity of `Z_t` and the exact conjugation formula. No Bell-value or
fourth-root-companion conclusion is claimed in this module.
-/

open Matrix
namespace CGLMPBounds.Companion
noncomputable section

variable {d n : ℕ} [NeZero d]

@[simp] lemma flatten_apply (X : Blocks d n) (p q : OutcomeSpace d n) :
    flatten X p q = X p.1 q.1 p.2 q.2 := rfl

@[simp] lemma flatten_star (X : Blocks d n) : flatten Xᴴ = (flatten X)ᴴ := by
  rfl

lemma sum_sub_right (P : ZMod d → Base n) (k : ZMod d) :
    (∑ a, P (a - k)) = ∑ a, P a := by
  exact Fintype.sum_equiv (Equiv.subRight k) _ _ (fun _ => rfl)

lemma sum_sub_left (P : ZMod d → Base n) (k : ZMod d) :
    (∑ a, P (k - a)) = ∑ a, P a := by
  exact Fintype.sum_equiv (Equiv.subLeft k) _ _ (fun _ => rfl)

lemma conjugatorBlocks_star_apply (P : ZMod d → Base n) (hP : IsPVM P)
    (a b : ZMod d) : (conjugatorBlocks P)ᴴ a b = P (a - b) := by
  change (P (a - b))ᴴ = P (a - b)
  exact (hP.isHermitian _).eq

lemma conjugatorBlocks_mul_star (P : ZMod d → Base n) (hP : IsPVM P) :
    conjugatorBlocks P * (conjugatorBlocks P)ᴴ = 1 := by
  apply Matrix.ext
  intro a b
  simp only [Matrix.mul_apply, conjugatorBlocks_star_apply P hP, conjugatorBlocks]
  by_cases hab : a = b
  · subst b
    simp only [hP.mul_self, Matrix.one_apply_eq]
    rw [sum_sub_right, hP.sum_eq_one]
  · rw [Matrix.one_apply_ne hab]
    apply Finset.sum_eq_zero
    intro c _
    apply hP.mul_eq_zero
    intro h
    exact hab (sub_right_inj.mp h).symm

lemma conjugatorBlocks_star_mul (P : ZMod d → Base n) (hP : IsPVM P) :
    (conjugatorBlocks P)ᴴ * conjugatorBlocks P = 1 := by
  apply Matrix.ext
  intro a b
  simp only [Matrix.mul_apply, conjugatorBlocks_star_apply P hP, conjugatorBlocks]
  by_cases hab : a = b
  · subst b
    simp only [hP.mul_self, Matrix.one_apply_eq]
    rw [sum_sub_left, hP.sum_eq_one]
  · rw [Matrix.one_apply_ne hab]
    apply Finset.sum_eq_zero
    intro c _
    apply hP.mul_eq_zero
    intro h
    exact hab (sub_left_inj.mp h).symm

lemma conjugator_mul_star (P : ZMod d → Base n) (hP : IsPVM P) :
    conjugator P * (conjugator P)ᴴ = 1 := by
  simpa only [map_mul, map_one, flatten_star, conjugator] using
    congrArg (flatten (d := d) (n := n)) (conjugatorBlocks_mul_star P hP)

lemma conjugator_star_mul (P : ZMod d → Base n) (hP : IsPVM P) :
    (conjugator P)ᴴ * conjugator P = 1 := by
  simpa only [map_mul, map_one, flatten_star, conjugator] using
    congrArg (flatten (d := d) (n := n)) (conjugatorBlocks_star_mul P hP)

lemma conjugatorBlocks_covariance (P : ZMod d → Base n) (hP : IsPVM P)
    (a : ZMod d) :
    conjugatorBlocks P * computationalBlocks a * (conjugatorBlocks P)ᴴ =
      covariantBlocks P a := by
  apply Matrix.ext
  intro k l
  have hentry :
      (conjugatorBlocks P * computationalBlocks a * (conjugatorBlocks P)ᴴ : Blocks d n) k l =
        P (a - k) * P (a - l) := by
    rw [Matrix.mul_apply]
    simp only [computationalBlocks, Matrix.mul_diagonal,
      conjugatorBlocks_star_apply P hP]
    simp [conjugatorBlocks, mul_ite, ite_mul]
  rw [hentry]
  by_cases hkl : k = l
  · subst l
    simp [covariantBlocks, hP.mul_self]
  · rw [show covariantBlocks P a k l = 0 by simp [covariantBlocks, hkl]]
    apply hP.mul_eq_zero
    intro h
    exact hkl (sub_right_inj.mp h).symm

/-- The source's exact covariance formula `Z_t C_a Z_t† = diag_k P^t_(a−k)`. -/
theorem conjugator_covariance (P : ZMod d → Base n) (hP : IsPVM P)
    (a : ZMod d) :
    conjugator P * computational a * (conjugator P)ᴴ = covariant P a := by
  simpa only [map_mul, flatten_star, conjugator, computational, covariant] using
    congrArg (flatten (d := d) (n := n)) (conjugatorBlocks_covariance P hP a)

lemma covariantBlocks_isHermitian (P : ZMod d → Base n) (hP : IsPVM P)
    (a : ZMod d) : (covariantBlocks P a).IsHermitian := by
  change (covariantBlocks P a)ᴴ = covariantBlocks P a
  simp only [covariantBlocks, Matrix.diagonal_conjTranspose]
  congr 1
  funext k
  exact (hP.isHermitian _).eq

lemma covariantBlocks_mul_self (P : ZMod d → Base n) (hP : IsPVM P)
    (a : ZMod d) : covariantBlocks P a * covariantBlocks P a = covariantBlocks P a := by
  simp only [covariantBlocks, Matrix.diagonal_mul_diagonal, hP.mul_self]

lemma sum_covariantBlocks (P : ZMod d → Base n) (hP : IsPVM P) :
    ∑ a, covariantBlocks P a = 1 := by
  apply Matrix.ext
  intro k l
  by_cases hkl : k = l
  · subst l
    simp only [Matrix.sum_apply, covariantBlocks, Matrix.diagonal_apply_eq,
      Matrix.one_apply_eq]
    rw [sum_sub_right, hP.sum_eq_one]
  · simp [Matrix.sum_apply, covariantBlocks, hkl]

lemma covariant_isHermitian (P : ZMod d → Base n) (hP : IsPVM P)
    (a : ZMod d) : (covariant P a).IsHermitian := by
  change (flatten (covariantBlocks P a))ᴴ = flatten (covariantBlocks P a)
  rw [← flatten_star, (covariantBlocks_isHermitian P hP a).eq]

lemma covariant_mul_self (P : ZMod d → Base n) (hP : IsPVM P)
    (a : ZMod d) : covariant P a * covariant P a = covariant P a := by
  simpa only [map_mul, covariant] using
    congrArg (flatten (d := d) (n := n)) (covariantBlocks_mul_self P hP a)

lemma sum_covariant (P : ZMod d → Base n) (hP : IsPVM P) :
    ∑ a, covariant P a = 1 := by
  simpa only [map_sum, map_one, covariant] using
    congrArg (flatten (d := d) (n := n)) (sum_covariantBlocks P hP)

end
end CGLMPBounds.Companion
