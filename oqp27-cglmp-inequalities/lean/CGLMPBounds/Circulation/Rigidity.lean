module

public import CGLMPBounds.Circulation.Spectral

@[expose] public section


/-!
# Vanishing forbidden overlaps force commutativity

Appendix E, the first equality-case argument: the two forbidden cyclic
successors vanish, and two distinct rows of the allowed overlap graph have
at most one common column. Orthogonality then kills every off-diagonal
sandwich. No simultaneous diagonalization is assumed here.
-/

open Matrix
open scoped ComplexOrder

namespace CGLMPBounds
noncomputable section

/-- A pair of PVMs whose allowed overlap graph has no four-cycle commutes.
The graph hypothesis says that distinct rows share at most one column. -/
theorem IsPVM.commute_of_sparse_overlap {r : ℕ} {α β : Type*}
    [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β]
    {P : α → Matrix (Fin r) (Fin r) ℂ} {Q : β → Matrix (Fin r) (Fin r) ℂ}
    (hP : IsPVM P) (hQ : IsPVM Q) (R : α → β → Prop)
    (hz : ∀ a b, ¬ R a b → P a * Q b = 0)
    (hunique : ∀ a c, a ≠ c → ∀ b b',
      R a b → R c b → R a b' → R c b' → b = b') :
    ∀ a b, P a * Q b = Q b * P a := by
  classical
  have hzrev (a : α) (b : β) (h : ¬ R a b) : Q b * P a = 0 := by
    have he := congrArg Matrix.conjTranspose (hz a b h)
    simpa only [Matrix.conjTranspose_mul, (hP.isHermitian a).eq,
      (hQ.isHermitian b).eq, Matrix.conjTranspose_zero] using he
  have hoff (a c : α) (hac : a ≠ c) (b : β) : P a * Q b * P c = 0 := by
    by_cases hab : R a b
    · by_cases hcb : R c b
      · have hsum : (∑ k, P a * Q k * P c) = 0 := by
          rw [← Finset.sum_mul, ← Finset.mul_sum, hQ.sum_eq_one, Matrix.mul_one]
          exact hP.mul_eq_zero (Ne.symm hac)
        have hone : (∑ k, P a * Q k * P c) = P a * Q b * P c := by
          apply Finset.sum_eq_single b
          · intro k _ hkb
            by_cases hak : R a k
            · have hck : ¬ R c k := fun h => hkb (hunique a c hac b k hab hcb hak h).symm
              rw [Matrix.mul_assoc, hzrev c k hck, Matrix.mul_zero]
            · rw [hz a k hak, Matrix.zero_mul]
          · simp
        exact hone.symm.trans hsum
      · rw [Matrix.mul_assoc, hzrev c b hcb, Matrix.mul_zero]
    · rw [hz a b hab, Matrix.zero_mul]
  intro a b
  have hsand : P a * Q b = P a * Q b * P a := by
    calc
      P a * Q b = (P a * Q b) * ∑ c, P c := by rw [hP.sum_eq_one, Matrix.mul_one]
      _ = ∑ c, P a * Q b * P c := Finset.mul_sum _ _ _
      _ = P a * Q b * P a := by
        apply Finset.sum_eq_single a
        · intro c _ hca
          exact hoff a c (Ne.symm hca) b
        · simp
  have hadj := congrArg Matrix.conjTranspose hsand
  have hsandrev : Q b * P a = P a * Q b * P a := by
    simpa only [Matrix.conjTranspose_mul, (hP.isHermitian a).eq,
      (hQ.isHermitian b).eq, ← Matrix.mul_assoc] using hadj
  exact hsand.trans hsandrev.symm

namespace Circulation
variable {r : ℕ}

lemma hsSq_eq_zero_iff [NeZero r] (X : Mat r) : hsSq X = 0 ↔ X = 0 := by
  constructor
  · intro h
    have hr : (r : ℝ) ≠ 0 := by exact_mod_cast NeZero.ne r
    have hre : (Matrix.trace (Xᴴ * X)).re = 0 := by
      have hd : (Matrix.trace (Xᴴ * X)).re / (r : ℝ) = 0 := by
        simpa only [hsSq, reTr_eq] using h
      exact (div_eq_zero_iff.mp hd).resolve_right hr
    have him := (Complex.nonneg_iff.mp
      (Matrix.posSemidef_conjTranspose_mul_self X).trace_nonneg).2
    apply Matrix.trace_conjTranspose_mul_self_eq_zero_iff.mp
    apply Complex.ext
    · simpa only [Complex.zero_re] using hre
    · simpa only [Complex.zero_im] using him.symm
  · rintro rfl
    simp [hsSq]

/-- The two forbidden successors vanish separately when their total vanishes. -/
lemma forbidden_root_eq_zero_overlaps [NeZero r] (E F : Fin 4 → Mat r)
    (hE : IsPVM E) (hF : IsPVM F) (hzero : forbidden (root E) (root F) = 0) :
    (∀ a, E a * F (a + 1) = 0) ∧ (∀ a, E a * F (a + 2) = 0) := by
  rw [forbidden_root E F hE hF] at hzero
  have h1 : 0 ≤ ∑ a, hsSq (E a * F (a + 1)) :=
    Finset.sum_nonneg fun _ _ => hsSq_nonneg _
  have h2 : 0 ≤ ∑ a, hsSq (E a * F (a + 2)) :=
    Finset.sum_nonneg fun _ _ => hsSq_nonneg _
  constructor
  · intro a
    apply (hsSq_eq_zero_iff _).mp
    have ha := Finset.single_le_sum (fun b (_ : b ∈ (Finset.univ : Finset (Fin 4))) =>
      hsSq_nonneg (E b * F (b + 1))) (Finset.mem_univ a)
    exact le_antisymm (by linarith) (hsSq_nonneg _)
  · intro a
    apply (hsSq_eq_zero_iff _).mp
    have ha := Finset.single_le_sum (fun b (_ : b ∈ (Finset.univ : Finset (Fin 4))) =>
      hsSq_nonneg (E b * F (b + 2))) (Finset.mem_univ a)
    exact le_antisymm (by linarith) (hsSq_nonneg _)

/-- The actual four-outcome spectral PVMs commute at zero forbidden mass. -/
theorem forbidden_root_eq_zero_commute [NeZero r] (E F : Fin 4 → Mat r)
    (hE : IsPVM E) (hF : IsPVM F) (hzero : forbidden (root E) (root F) = 0) :
    ∀ a b, E a * F b = F b * E a := by
  obtain ⟨h1, h2⟩ := forbidden_root_eq_zero_overlaps E F hE hF hzero
  apply hE.commute_of_sparse_overlap hF (fun a b => b = a ∨ b = a + 3)
  · intro a b hab
    have hcases : b = a + 1 ∨ b = a + 2 := by
      exact (by decide : ∀ a b : Fin 4, ¬(b = a ∨ b = a + 3) →
        b = a + 1 ∨ b = a + 2) a b hab
    rcases hcases with h | h
    · simpa only [h] using h1 a
    · simpa only [h] using h2 a
  · decide

lemma root_commute_of_projections (E F : Fin 4 → Mat r)
    (h : ∀ a b, E a * F b = F b * E a) : root E * root F = root F * root E := by
  simp only [root, Finset.sum_mul, Finset.mul_sum,
    Matrix.smul_mul, Matrix.mul_smul, smul_smul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro b _
  apply Finset.sum_congr rfl
  intro a _
  rw [h b a, mul_comm (Complex.I ^ a.val)]

/-- Equality in the forbidden-overlap constraint forces the original
fourth-root unitaries to commute, not only auxiliary spectral data. -/
theorem fourth_root_commute_of_forbidden_eq_zero [NeZero r] (U V : Mat r)
    (hU : Uᴴ * U = 1) (hV : Vᴴ * V = 1)
    (hU4 : U ^ 4 = 1) (hV4 : V ^ 4 = 1) (hzero : forbidden U V = 0) :
    U * V = V * U := by
  have hp := forbidden_root_eq_zero_commute (spectral U) (spectral V)
    (spectral_isPVM hU hU4) (spectral_isPVM hV hV4)
    (by simpa only [root_spectral] using hzero)
  simpa only [root_spectral] using root_commute_of_projections (spectral U) (spectral V) hp

end Circulation
end
end CGLMPBounds
