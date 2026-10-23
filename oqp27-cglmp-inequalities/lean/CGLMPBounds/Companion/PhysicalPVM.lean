module

public import CGLMPBounds.Companion.BellGap

@[expose] public section


/-!
# Physical companion PVMs and the full conclusion in product coordinates

The finite matrix index for the multiplicity is `Fin 4 × Fin n` here. This file
packages the projection equations, exact Bell gap, and one common reducing isometry.
A later coordinate equivalence identifies this multiplicity with `Fin (4*n)`.
-/

open Matrix
attribute [-instance] CStarMatrix.instHMulOfFintypeOfMulOfAddCommMonoid
namespace CGLMPBounds.Companion
noncomputable section

variable {d n : ℕ} [NeZero d]

lemma sourceComputational_mul_self (a : ZMod d) :
    sourceComputational (n := n) a * sourceComputational a = sourceComputational a := by
  unfold sourceComputational
  rw [Matrix.diagonal_mul_diagonal]
  congr 1
  funext p
  split_ifs <;> simp

lemma sourceComputational_sum :
    ∑ a : ZMod d, sourceComputational (n := n) a = 1 := by
  ext p q
  by_cases h : p = q
  · subst q
    simp [sourceComputational, Matrix.sum_apply, Matrix.diagonal_apply, Matrix.one_apply,
      Finset.sum_ite_eq, Finset.sum_ite_eq']
  · simp [sourceComputational, Matrix.sum_apply, Matrix.diagonal_apply, Matrix.one_apply, h]

lemma matrix_pow_mul_pow_of_mul_eq_one {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A B : Matrix ι ι ℂ) (h : A * B = 1) (m : ℕ) : A ^ m * B ^ m = 1 := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [pow_succ A, pow_succ' B]
    calc
      _ = A ^ m * (A * B) * B ^ m := by noncomm_ring
      _ = 1 := by rw [h, mul_one, ih]

lemma sourceMeasurement_mul_self (P : Fin 4 → ZMod d → Base n)
    (hP : ∀ t, IsPVM (P t)) (t : Fin 4) (a : ZMod d) :
    sourceMeasurement P hP t a * sourceMeasurement P hP t a =
      sourceMeasurement P hP t a := by
  have hleft := matrix_pow_mul_pow_of_mul_eq_one (sourceClock P hP)ᴴ
    (sourceClock P hP) (sourceClock_star_mul P hP) t.val
  unfold sourceMeasurement
  calc
    _ = sourceClock P hP ^ t.val * sourceComputational a *
        ((sourceClock P hP)ᴴ ^ t.val * sourceClock P hP ^ t.val) *
        sourceComputational a * (sourceClock P hP)ᴴ ^ t.val := by noncomm_ring
    _ = sourceClock P hP ^ t.val *
        (sourceComputational a * sourceComputational a) * (sourceClock P hP)ᴴ ^ t.val := by
      rw [hleft, mul_one]
      noncomm_ring
    _ = _ := by rw [sourceComputational_mul_self]

lemma sourceMeasurement_sum (P : Fin 4 → ZMod d → Base n)
    (hP : ∀ t, IsPVM (P t)) (t : Fin 4) :
    ∑ a : ZMod d, sourceMeasurement P hP t a = 1 := by
  unfold sourceMeasurement
  rw [← Matrix.sum_mul, ← Matrix.mul_sum, sourceComputational_sum, mul_one]
  exact matrix_pow_mul_pow_of_mul_eq_one (sourceClock P hP) (sourceClock P hP)ᴴ
    (sourceClock_mul_star P hP) t.val

/-- All source C.1 conclusions, with multiplicity written as a product of finite indices.
No gap identity, representation, or common-summand conclusion is assumed as input. -/
theorem exists_companion_full_product (hd : 2 ≤ d) (hn : 1 ≤ n)
    (P : Fin 4 → ZMod d → Base n) (hP : ∀ t, IsPVM (P t)) :
    ∃ V : Fin d → Matrix.unitaryGroup (CompanionMultiplicity n) ℂ,
      (∀ j, (V j : Matrix (CompanionMultiplicity n) (CompanionMultiplicity n) ℂ) ^ 4 = 1) ∧
      cglmpFourierValue d - cglmp d (tracialTable ![P 0, P 2] ![P 1, P 3]) =
        (8 * (d : ℝ) / ((d : ℝ) - 1)) * companionGap V ∧
      (∀ t a, (tupleMeasurement V t a).IsHermitian ∧
        tupleMeasurement V t a * tupleMeasurement V t a = tupleMeasurement V t a) ∧
      (∀ t, ∑ a, tupleMeasurement V t a = 1) ∧
      ∃ Z : Matrix (CompanionSpace d n) (Fin n) ℂ,
        Zᴴ * Z = 1 ∧
        (∀ t a, tupleMeasurement V t a * Z = Z * P t a) ∧
        (∀ t a, Commute (tupleMeasurement V t a) (Z * Zᴴ)) := by
  obtain ⟨V, hfour, hgap, hclock, hiso, hinter, hcomm⟩ :=
    exists_companion_tuple_gap_reducing hd hn P hP
  have hM : ∀ t a, tupleMeasurement V t a = sourceMeasurement P hP t a := by
    intro t a
    simp only [tupleMeasurement, sourceMeasurement, hclock]
  refine ⟨V, hfour, hgap, ?_, ?_, sourceEmbedding P, hiso, hinter, hcomm⟩
  · intro t a
    rw [hM]
    exact ⟨sourceMeasurement_isHermitian P hP t a, sourceMeasurement_mul_self P hP t a⟩
  · intro t
    simp only [hM]
    exact sourceMeasurement_sum P hP t

end
end CGLMPBounds.Companion
