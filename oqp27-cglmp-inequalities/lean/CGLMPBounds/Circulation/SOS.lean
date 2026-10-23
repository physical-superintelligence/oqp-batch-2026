module

public import CGLMPBounds.Circulation.Projection

@[expose] public section


/-!
# The circulation sum of squares

The identity is exactly (H.1), with the six triples of Table H.1. The proof reduces
normalized real traces of products to the signed triple array
`T(a,b,c)=Re tau(A_a B_b C_c)`. No positivity is asserted or assumed for this array.
Completeness gives its three pair marginals. All remaining equalities are finite
polynomial identities proved in the kernel, not evaluations of an external oracle.
-/

open Matrix
namespace CGLMPBounds.Circulation
noncomputable section
variable {r : ℕ}

set_option maxRecDepth 4000 in
set_option maxHeartbeats 1600000 in
/-- The exact sum-of-squares identity (H.1), for either real sign `σ`. -/
theorem sos_identity (A B C : Fin 4 → Mat r) (hA : IsPVM A) (hB : IsPVM B)
    (hC : IsPVM C) (σ : ℝ) (hσ : σ ^ 2 = 1) :
    2 * positiveMass A B C + 5 * oppositeMass A B C -
      σ * circulation (root A) (root B) (root C) = sos A B C σ := by
  let T : Fin 4 → Fin 4 → Fin 4 → ℝ := fun a b c => reTr (A a * B b * C c)
  have ha : ∀ a, (A a)ᴴ = A a := fun a => (hA.isHermitian a).eq
  have hb : ∀ b, (B b)ᴴ = B b := fun b => (hB.isHermitian b).eq
  have hc : ∀ c, (C c)ᴴ = C c := fun c => (hC.isHermitian c).eq
  have qab : ∀ a b, hsSq (A a * B b) = reTr (A a * B b) :=
    fun a b => hsSq_proj_mul (hA.isHermitian a) (hA.mul_self a) (hB.isHermitian b) (hB.mul_self b)
  have qbc : ∀ b c, hsSq (B b * C c) = reTr (B b * C c) :=
    fun b c => hsSq_proj_mul (hB.isHermitian b) (hB.mul_self b) (hC.isHermitian c) (hC.mul_self c)
  have qac : ∀ a c, hsSq (A a * C c) = reTr (A a * C c) :=
    fun a c => hsSq_proj_mul (hA.isHermitian a) (hA.mul_self a) (hC.isHermitian c) (hC.mul_self c)
  have ma : ∀ a (X Y : Mat r), X * (A a * (A a * Y)) = X * (A a * Y) := by
    intro a X Y
    rw [← Matrix.mul_assoc (A a) (A a) Y, hA.mul_self]
  have mb : ∀ b (X Y : Mat r), X * (B b * (B b * Y)) = X * (B b * Y) := by
    intro b X Y
    rw [← Matrix.mul_assoc (B b) (B b) Y, hB.mul_self]
  have mc : ∀ c (X Y : Mat r), X * (C c * (C c * Y)) = X * (C c * Y) := by
    intro c X Y
    rw [← Matrix.mul_assoc (C c) (C c) Y, hC.mul_self]
  have abc : ∀ a b c, reTr (A a * (B b * C c)) = T a b c := by
    intro a b c
    simp only [T, Matrix.mul_assoc]
  have bac : ∀ a b c, reTr (B b * (A a * C c)) = T a b c := by
    intro a b c
    simpa only [T, Matrix.mul_assoc] using
      reTr_swap_first (hB.isHermitian b) (hA.isHermitian a) (hC.isHermitian c)
  have bca : ∀ a b c, reTr (B b * (C c * A a)) = T a b c := by
    intro a b c
    dsimp [T]
    rw [← Matrix.mul_assoc, reTr_cycle, reTr_cycle]
  have cab : ∀ a b c, reTr (C c * (A a * B b)) = T a b c := by
    intro a b c
    dsimp [T]
    rw [← Matrix.mul_assoc, reTr_cycle]
  have acb : ∀ a b c, reTr (A a * (C c * B b)) = T a b c := by
    intro a b c
    dsimp [T]
    rw [← Matrix.mul_assoc, reTr_cycle,
      reTr_reverse (hC.isHermitian c) (hB.isHermitian b) (hA.isHermitian a)]
  have cba : ∀ a b c, reTr (C c * (B b * A a)) = T a b c := by
    intro a b c
    simpa only [T, Matrix.mul_assoc] using
      reTr_reverse (hC.isHermitian c) (hB.isHermitian b) (hA.isHermitian a)
  have pab : ∀ a b, reTr (A a * B b) = ∑ c, T a b c := by
    intro a b
    simp only [T, ← reTr_sum, ← Finset.mul_sum, hC.sum_eq_one, Matrix.mul_one]
  have pbc : ∀ b c, reTr (B b * C c) = ∑ a, T a b c := by
    intro b c
    simp only [T, ← reTr_sum, ← Finset.sum_mul, hA.sum_eq_one, Matrix.one_mul]
  have pac : ∀ a c, reTr (A a * C c) = ∑ b, T a b c := by
    intro a c
    simp only [T, ← reTr_sum, ← Finset.sum_mul, ← Finset.mul_sum,
      hB.sum_eq_one, Matrix.mul_one]
  rw [circulation_root A B C hA hB hC]
  unfold positiveMass oppositeMass sos
  -- Remove adjoints of whole norms before expanding adjoints inside cross terms.
  -- Otherwise simplification turns these norms into reversed products first.
  simp only [hsSq_sub_smul, hsSq_add_smul, hsSq_star]
  simp only [Matrix.conjTranspose_conjTranspose,
    qab, qbc, qac, Matrix.conjTranspose_mul, ha, hb, hc, Matrix.mul_assoc, ma, mb, mc,
    abc, bac, bca, cab, acb, cba, pab, pbc, pac, div_pow, hσ]
  norm_num [Fin.sum_univ_four]
  <;> ring

/-- Every term in (H.1) is nonnegative for both allowed signs. -/
lemma sos_nonneg (A B C : Fin 4 → Mat r) (σ : ℝ) (hσ : σ = 1 ∨ σ = -1) :
    0 ≤ sos A B C σ := by
  unfold sos
  apply Finset.sum_nonneg
  intro l _
  have hcoeff : 0 ≤ (7 / 3 : ℝ) + 2 * σ := by rcases hσ with rfl | rfl <;> norm_num
  exact (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (hsSq_nonneg _) (hsSq_nonneg _)) (hsSq_nonneg _)) (hsSq_nonneg _)) (hsSq_nonneg _)) (hsSq_nonneg _)) (mul_nonneg (by norm_num) (hsSq_nonneg _))) (mul_nonneg (by norm_num) (hsSq_nonneg _))) (mul_nonneg hcoeff (hsSq_nonneg _)))

lemma positiveMass_nonneg (A B C : Fin 4 → Mat r) : 0 ≤ positiveMass A B C := by
  unfold positiveMass
  apply Finset.sum_nonneg
  intro l _
  exact add_nonneg (add_nonneg (hsSq_nonneg _) (hsSq_nonneg _)) (hsSq_nonneg _)

lemma oppositeMass_nonneg (A B C : Fin 4 → Mat r) : 0 ≤ oppositeMass A B C := by
  unfold oppositeMass
  apply Finset.sum_nonneg
  intro l _
  exact add_nonneg (add_nonneg (hsSq_nonneg _) (hsSq_nonneg _)) (hsSq_nonneg _)

/-- The sharper intermediate estimate immediately following (H.1). -/
theorem abs_circulation_le (A B C : Fin 4 → Mat r) (hA : IsPVM A) (hB : IsPVM B)
    (hC : IsPVM C) :
    |circulation (root A) (root B) (root C)| ≤ 2 * positiveMass A B C + 5 * oppositeMass A B C := by
  have hp := sos_nonneg A B C 1 (Or.inl rfl)
  have hm := sos_nonneg A B C (-1) (Or.inr rfl)
  rw [← sos_identity A B C hA hB hC 1 (by norm_num)] at hp
  rw [← sos_identity A B C hA hB hC (-1) (by norm_num)] at hm
  apply abs_le.mpr
  constructor <;> linarith

/-- The overlap identity `P + O = pᵢⱼ + pⱼₖ + pᵢₖ` stated before (H.1). -/
lemma mass_eq_forbidden_sum [NeZero r] (A B C : Fin 4 → Mat r)
    (hA : IsPVM A) (hB : IsPVM B) (hC : IsPVM C) :
    positiveMass A B C + oppositeMass A B C =
      forbidden (root A) (root B) + forbidden (root B) (root C) +
        forbidden (root A) (root C) := by
  rw [forbidden_root A B hA hB, forbidden_root B C hB hC, forbidden_root A C hA hC]
  simp only [positiveMass, oppositeMass, Finset.sum_add_distrib]
  ring

/-- Lemma D.4 / (D.12) in spectral-PVM coordinates. -/
theorem circulation_bound [NeZero r] (A B C : Fin 4 → Mat r)
    (hA : IsPVM A) (hB : IsPVM B) (hC : IsPVM C) :
    |circulation (root A) (root B) (root C)| ≤
      5 * (forbidden (root A) (root B) + forbidden (root B) (root C) + forbidden (root A) (root C)) := by
  have habs := abs_circulation_le A B C hA hB hC
  have hpos := positiveMass_nonneg A B C
  rw [← mass_eq_forbidden_sum A B C hA hB hC]
  linarith

end
end CGLMPBounds.Circulation
