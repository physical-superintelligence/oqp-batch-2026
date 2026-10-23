module

public import CGLMPBounds.Defs.LocalContentWeights
public import CGLMPBounds.LocalContent.Scalar
public import CGLMPBounds.LocalContent.Bessel
public import CGLMPBounds.Statistics.Ceiling
public import CGLMPBounds.Scenario.HiddenVariable

@[expose] public section


/-!
# Positive local content: the vector form of Theorem F.3

Supplement, Appendix F.4, proof of Theorem F.3, after purification and dilation: "We may therefore
use a vector `ψ`, Alice projections `A_a, C_c`, and Bob projections `B^y_b`." The proof only uses
the vectors `u^y_{ab} = A_a B^y_b ψ`, `v^y_{cb} = C_c B^y_b ψ` and the following facts, which are the
hypotheses of `lowRoot_le_localFraction`:

* `q(a,b|0,y) = ‖u^y_{ab}‖²`, `q(c,b|1,y) = ‖v^y_{cb}‖²`;
* at fixed `y, b` the `u^y_{ab}` are pairwise orthogonal in `a` and the `v^y_{cb}` in `c`;
* `Σ_b ⟨u^y_{ab}, v^y_{cb}⟩ = k_{ac}`, `Σ_b ‖u^y_{ab}‖² = q_A(a|0)`, `Σ_b ‖v^y_{cb}‖² = q_A(c|1)`;
* `|k_{ac}|² ≤ q_A(a|0) q_A(c|1)` and `Σ_{a,c} k_{ac} = 1`.

From these it builds the local hidden-variable model (F.12): the hidden pair `(a, c)` has weight
`h_{ac} = (w - √(w² - 4|k_{ac}|²))/2` with `w = q_A(a|0) + q_A(c|1)`, Alice answers `a` on input `0`
and `c` on input `1`, and Bob answers `b` on input `y` with probability `t^y_{acb} / T_y`. The
result is entrywise below `q`, so `LF(q) ≥ Σ_{a,c} h_{ac} ≥ (m_A - √(m_A² - 4))/2` with
`m_A = 2|α|` (the reverse Minkowski form of the source's weighted Jensen step).

* `tWeight`, `tTotal` : `t^y_{acb}` and `T_y = Σ_b t^y_{acb}`;
* `sum_tWeight_le_left`, `sum_tWeight_le_right` : (F.11), by Bessel's inequality;
* `lowRoot_le_tTotal` : `h_{ac} ≤ T_y`;
* `lowRoot_le_sum_lowRoot` : `Σ_{a,c} h_{ac} ≥ (m_A - √(m_A² - 4))/2`;
* `lowRoot_le_localFraction` : the bound `LF(q) ≥ (m_A - √(m_A² - 4))/2`.
-/

namespace CGLMPBounds

noncomputable section

open Finset

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
variable {α β : Type*} [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β]

theorem tWeight_nonneg (u v : Fin 2 → α → β → E) (y : Fin 2) (a c : α) (b : β) :
    0 ≤ tWeight u v y a c b :=
  div_nonneg (sq_nonneg _) (le_max_of_le_left (sq_nonneg _))

theorem tTotal_nonneg (u v : Fin 2 → α → β → E) (y : Fin 2) (a c : α) :
    0 ≤ tTotal u v y a c :=
  Finset.sum_nonneg (fun b _ => tWeight_nonneg u v y a c b)

theorem div_le_div_of_zero_imp {a r M : ℝ} (ha : 0 ≤ a) (hr : 0 ≤ r) (hrM : r ≤ M)
    (h0 : r = 0 → a = 0) : a / M ≤ a / r := by
  rcases eq_or_lt_of_le hr with h | h
  · rw [h0 h.symm]
    simp
  · exact div_le_div_of_nonneg_left ha h hrM

/-- (F.11), first inequality: `Σ_c t^y_{acb} ≤ p^y_{ab}`. -/
theorem sum_tWeight_le_left {u v : Fin 2 → α → β → E}
    (hv : ∀ y b c c', c ≠ c' → inner ℂ (v y c b) (v y c' b) = 0) (y : Fin 2) (a : α) (b : β) :
    ∑ c, tWeight u v y a c b ≤ ‖u y a b‖ ^ 2 := by
  refine le_trans (Finset.sum_le_sum (fun c _ => ?_))
    (bessel_orthogonal (fun c => v y c b) (fun c c' h => hv y b c c' h) (u y a b))
  show ‖inner ℂ (u y a b) (v y c b)‖ ^ 2 / max (‖u y a b‖ ^ 2) (‖v y c b‖ ^ 2)
    ≤ ‖inner ℂ (v y c b) (u y a b)‖ ^ 2 / ‖v y c b‖ ^ 2
  rw [norm_inner_symm (𝕜 := ℂ) (v y c b) (u y a b)]
  refine div_le_div_of_zero_imp (sq_nonneg _) (sq_nonneg _) (le_max_right _ _) (fun h => ?_)
  have hv0 : v y c b = 0 := norm_eq_zero.mp ((pow_eq_zero_iff two_ne_zero).mp h)
  rw [hv0]
  simp

/-- (F.11), second inequality: `Σ_a t^y_{acb} ≤ r^y_{cb}`. -/
theorem sum_tWeight_le_right {u v : Fin 2 → α → β → E}
    (hu : ∀ y b a a', a ≠ a' → inner ℂ (u y a b) (u y a' b) = 0) (y : Fin 2) (c : α) (b : β) :
    ∑ a, tWeight u v y a c b ≤ ‖v y c b‖ ^ 2 := by
  refine le_trans (Finset.sum_le_sum (fun a _ => ?_))
    (bessel_orthogonal (fun a => u y a b) (fun a a' h => hu y b a a' h) (v y c b))
  show ‖inner ℂ (u y a b) (v y c b)‖ ^ 2 / max (‖u y a b‖ ^ 2) (‖v y c b‖ ^ 2)
    ≤ ‖inner ℂ (u y a b) (v y c b)‖ ^ 2 / ‖u y a b‖ ^ 2
  refine div_le_div_of_zero_imp (sq_nonneg _) (sq_nonneg _) (le_max_left _ _) (fun h => ?_)
  have hu0 : u y a b = 0 := norm_eq_zero.mp ((pow_eq_zero_iff two_ne_zero).mp h)
  rw [hu0]
  simp

/-- The smaller root `h_{ac}` is at most `T_y` (proof of Theorem F.3: `z_y ≥ h_{ac}` and the
weighted Cauchy–Schwarz inequality `T_y ≥ k²/(w - z_y) ≥ k²/(w - h_{ac}) = h_{ac}`). -/
theorem lowRoot_le_tTotal {u v : Fin 2 → α → β → E} {k : α → α → ℂ} {pA pC : α → ℝ}
    (hk : ∀ y a c, ∑ b, inner ℂ (u y a b) (v y c b) = k a c)
    (hpA : ∀ y a, ∑ b, ‖u y a b‖ ^ 2 = pA a) (hpC : ∀ y c, ∑ b, ‖v y c b‖ ^ 2 = pC c)
    (hkA : ∀ a c, 2 * ‖k a c‖ ≤ pA a + pC c) (y : Fin 2) (a c : α) :
    lowRoot (pA a + pC c) ‖k a c‖ ≤ tTotal u v y a c := by
  show lowRoot (pA a + pC c) ‖k a c‖ ≤ ∑ b, tWeight u v y a c b
  have hZ : ∀ b, ‖inner ℂ (u y a b) (v y c b)‖ ^ 2
      ≤ min (‖u y a b‖ ^ 2) (‖v y c b‖ ^ 2) * max (‖u y a b‖ ^ 2) (‖v y c b‖ ^ 2) := by
    intro b
    rw [min_mul_max]
    exact norm_inner_sq_le _ _
  have hmin0 : ∀ b, 0 ≤ min (‖u y a b‖ ^ 2) (‖v y c b‖ ^ 2) := fun b =>
    le_min (sq_nonneg _) (sq_nonneg _)
  have hmax0 : ∀ b, 0 ≤ max (‖u y a b‖ ^ 2) (‖v y c b‖ ^ 2) := fun b =>
    le_max_of_le_left (sq_nonneg _)
  have hsum : ∑ b, min (‖u y a b‖ ^ 2) (‖v y c b‖ ^ 2)
      + ∑ b, max (‖u y a b‖ ^ 2) (‖v y c b‖ ^ 2) = pA a + pC c := by
    rw [← Finset.sum_add_distrib]
    simp only [min_add_max]
    rw [Finset.sum_add_distrib, hpA y a, hpC y c]
  have hMx : ∑ b, max (‖u y a b‖ ^ 2) (‖v y c b‖ ^ 2)
      = pA a + pC c - ∑ b, min (‖u y a b‖ ^ 2) (‖v y c b‖ ^ 2) := by linarith
  have hzA : ∑ b, min (‖u y a b‖ ^ 2) (‖v y c b‖ ^ 2) ≤ pA a := by
    rw [← hpA y a]
    exact Finset.sum_le_sum (fun b _ => min_le_left _ _)
  have hzC : ∑ b, min (‖u y a b‖ ^ 2) (‖v y c b‖ ^ 2) ≤ pC c := by
    rw [← hpC y c]
    exact Finset.sum_le_sum (fun b _ => min_le_right _ _)
  have hk0 : 0 ≤ ‖k a c‖ := norm_nonneg _
  have hkZ : ‖k a c‖ ≤ ∑ b, ‖inner ℂ (u y a b) (v y c b)‖ := by
    rw [← hk y a c]
    exact norm_sum_le _ _
  have hkZ2 : ‖k a c‖ ^ 2 ≤ (∑ b, ‖inner ℂ (u y a b) (v y c b)‖) ^ 2 := by
    have := mul_self_le_mul_self hk0 hkZ
    nlinarith [this]
  have hCS1 := Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul Finset.univ
    (fun b _ => hmin0 b) (fun b _ => hmax0 b) (fun b _ => hZ b)
  rw [hMx] at hCS1
  have hT : ∀ b, ‖inner ℂ (u y a b) (v y c b)‖ ^ 2
      ≤ tWeight u v y a c b * max (‖u y a b‖ ^ 2) (‖v y c b‖ ^ 2) := by
    intro b
    unfold tWeight
    rcases eq_or_lt_of_le (hmax0 b) with h | h
    · have h1 := hZ b
      rw [← h, mul_zero] at h1 ⊢
      exact h1
    · exact (div_mul_cancel₀ _ h.ne').symm.le
  have hCS2 := Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul Finset.univ
    (fun b _ => tWeight_nonneg u v y a c b) (fun b _ => hmax0 b) (fun b _ => hT b)
  rw [hMx] at hCS2
  have hw2 := hkA a c
  have hroot := lowRoot_mul hk0 hw2
  have hhalf := lowRoot_le_half (pA a + pC c) ‖k a c‖
  have hh0 := lowRoot_nonneg hk0 hw2
  have hzle : lowRoot (pA a + pC c) ‖k a c‖ ≤ ∑ b, min (‖u y a b‖ ^ 2) (‖v y c b‖ ^ 2) :=
    lowRoot_le_of (by linarith) (le_trans hkZ2 hCS1)
  have hT0 : 0 ≤ ∑ b, tWeight u v y a c b :=
    Finset.sum_nonneg (fun b _ => tWeight_nonneg u v y a c b)
  have key : lowRoot (pA a + pC c) ‖k a c‖ * (pA a + pC c - lowRoot (pA a + pC c) ‖k a c‖)
      ≤ (∑ b, tWeight u v y a c b) * (pA a + pC c - lowRoot (pA a + pC c) ‖k a c‖) := by
    rw [hroot]
    calc ‖k a c‖ ^ 2 ≤ (∑ b, ‖inner ℂ (u y a b) (v y c b)‖) ^ 2 := hkZ2
      _ ≤ (∑ b, tWeight u v y a c b)
          * (pA a + pC c - ∑ b, min (‖u y a b‖ ^ 2) (‖v y c b‖ ^ 2)) := hCS2
      _ ≤ (∑ b, tWeight u v y a c b) * (pA a + pC c - lowRoot (pA a + pC c) ‖k a c‖) :=
          mul_le_mul_of_nonneg_left (by linarith) hT0
  by_cases hpos : 0 < pA a + pC c - lowRoot (pA a + pC c) ‖k a c‖
  · exact le_of_mul_le_mul_right key hpos
  · have := not_lt.mp hpos
    linarith

/-- Alice's deterministic response for the hidden pair `l = (a, c)`: `a` on input `0`, `c` on
input `1`. -/
def aliceResp (l : α × α) (x : Fin 2) (a : α) : ℝ :=
  if a = (if x = 0 then l.1 else l.2) then 1 else 0

/-- Bob's response for the hidden pair `l = (a, c)` on input `y`: `t^y_{acb} / T_y`, and a point mass
at `b₀` when `T_y = 0`. -/
def bobResp (u v : Fin 2 → α → β → E) (b₀ : β) (l : α × α) (y : Fin 2) (b : β) : ℝ :=
  if tTotal u v y l.1 l.2 = 0 then (if b = b₀ then 1 else 0)
  else tWeight u v y l.1 l.2 b / tTotal u v y l.1 l.2

theorem aliceResp_nonneg (l : α × α) (x : Fin 2) (a : α) : 0 ≤ aliceResp l x a := by
  unfold aliceResp
  split_ifs <;> norm_num

theorem sum_aliceResp (l : α × α) (x : Fin 2) : ∑ a, aliceResp l x a = 1 := by
  unfold aliceResp
  rw [Finset.sum_ite_eq']
  simp

theorem bobResp_nonneg (u v : Fin 2 → α → β → E) (b₀ : β) (l : α × α) (y : Fin 2) (b : β) :
    0 ≤ bobResp u v b₀ l y b := by
  unfold bobResp
  split_ifs
  · norm_num
  · norm_num
  · exact div_nonneg (tWeight_nonneg u v y l.1 l.2 b) (tTotal_nonneg u v y l.1 l.2)

theorem sum_bobResp (u v : Fin 2 → α → β → E) (b₀ : β) (l : α × α) (y : Fin 2) :
    ∑ b, bobResp u v b₀ l y b = 1 := by
  by_cases hT : tTotal u v y l.1 l.2 = 0
  · have h : ∀ b, bobResp u v b₀ l y b = if b = b₀ then 1 else 0 := fun b => by
      unfold bobResp
      rw [if_pos hT]
    simp only [h]
    rw [Finset.sum_ite_eq']
    simp
  · have h : ∀ b, bobResp u v b₀ l y b = tWeight u v y l.1 l.2 b / tTotal u v y l.1 l.2 :=
      fun b => by
        unfold bobResp
        rw [if_neg hT]
    simp only [h]
    rw [← Finset.sum_div]
    exact div_self hT

theorem lowRoot_mul_bobResp_le {u v : Fin 2 → α → β → E} {k : α → α → ℂ} {pA pC : α → ℝ}
    (hk : ∀ y a c, ∑ b, inner ℂ (u y a b) (v y c b) = k a c)
    (hpA : ∀ y a, ∑ b, ‖u y a b‖ ^ 2 = pA a) (hpC : ∀ y c, ∑ b, ‖v y c b‖ ^ 2 = pC c)
    (hkA : ∀ a c, 2 * ‖k a c‖ ≤ pA a + pC c) (b₀ : β) (l : α × α) (y : Fin 2) (b : β) :
    lowRoot (pA l.1 + pC l.2) ‖k l.1 l.2‖ * bobResp u v b₀ l y b ≤ tWeight u v y l.1 l.2 b := by
  have hle := lowRoot_le_tTotal hk hpA hpC hkA y l.1 l.2
  have h0 := lowRoot_nonneg (norm_nonneg (k l.1 l.2)) (hkA l.1 l.2)
  unfold bobResp
  by_cases hT : tTotal u v y l.1 l.2 = 0
  · have hz : lowRoot (pA l.1 + pC l.2) ‖k l.1 l.2‖ = 0 :=
      le_antisymm (le_of_le_of_eq hle hT) h0
    rw [hz, zero_mul]
    exact tWeight_nonneg u v y l.1 l.2 b
  · rw [if_neg hT]
    have hTpos : 0 < tTotal u v y l.1 l.2 :=
      lt_of_le_of_ne (tTotal_nonneg u v y l.1 l.2) (Ne.symm hT)
    calc lowRoot (pA l.1 + pC l.2) ‖k l.1 l.2‖
          * (tWeight u v y l.1 l.2 b / tTotal u v y l.1 l.2)
        ≤ tTotal u v y l.1 l.2 * (tWeight u v y l.1 l.2 b / tTotal u v y l.1 l.2) :=
          mul_le_mul_of_nonneg_right hle
            (div_nonneg (tWeight_nonneg u v y l.1 l.2 b) hTpos.le)
      _ = tWeight u v y l.1 l.2 b := mul_div_cancel₀ _ hTpos.ne'

/-- The weighted Jensen step of the proof of Theorem F.3, in reverse Minkowski form:
`Σ_{a,c} h_{ac} ≥ (m_A - √(m_A² - 4))/2` with `m_A = 2|α|`. -/
theorem lowRoot_le_sum_lowRoot {k : α → α → ℂ} {pA pC : α → ℝ}
    (hkA : ∀ a c, 2 * ‖k a c‖ ≤ pA a + pC c) (hpA1 : ∑ a, pA a = 1) (hpC1 : ∑ c, pC c = 1)
    (hk1 : ∑ a, ∑ c, k a c = 1) :
    lowRoot (2 * Fintype.card α) 1
      ≤ ∑ l : α × α, lowRoot (pA l.1 + pC l.2) ‖k l.1 l.2‖ := by
  have hW : ∑ l : α × α, (pA l.1 + pC l.2) = 2 * Fintype.card α := by
    rw [Finset.sum_add_distrib, Fintype.sum_prod_type' (fun (a : α) (_ : α) => pA a),
      Fintype.sum_prod_type' (fun (_ : α) (c : α) => pC c)]
    simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, ← Finset.mul_sum, hpA1, hpC1]
    ring
  have hK : 1 ≤ ∑ l : α × α, ‖k l.1 l.2‖ := by
    have h1 : ‖∑ l : α × α, k l.1 l.2‖ ≤ ∑ l : α × α, ‖k l.1 l.2‖ := norm_sum_le _ _
    rw [Fintype.sum_prod_type' k, hk1, norm_one] at h1
    exact h1
  have hM : ∑ l : α × α, Real.sqrt ((pA l.1 + pC l.2) ^ 2 - 4 * ‖k l.1 l.2‖ ^ 2)
      ≤ Real.sqrt ((∑ l : α × α, (pA l.1 + pC l.2)) ^ 2 - 4 * (∑ l : α × α, ‖k l.1 l.2‖) ^ 2) :=
    revMinkowski_sum (fun l : α × α => pA l.1 + pC l.2) (fun l => ‖k l.1 l.2‖)
      Finset.univ (fun l _ => norm_nonneg _) (fun l _ => hkA l.1 l.2)
  rw [hW] at hM
  have hmono : Real.sqrt ((2 * (Fintype.card α : ℝ)) ^ 2 - 4 * (∑ l : α × α, ‖k l.1 l.2‖) ^ 2)
      ≤ Real.sqrt ((2 * (Fintype.card α : ℝ)) ^ 2 - 4 * 1 ^ 2) :=
    Real.sqrt_le_sqrt (by nlinarith [hK])
  have hsum : ∑ l : α × α, lowRoot (pA l.1 + pC l.2) ‖k l.1 l.2‖
      = ((∑ l : α × α, (pA l.1 + pC l.2))
        - ∑ l : α × α, Real.sqrt ((pA l.1 + pC l.2) ^ 2 - 4 * ‖k l.1 l.2‖ ^ 2)) / 2 := by
    unfold lowRoot
    rw [← Finset.sum_sub_distrib, Finset.sum_div]
  rw [hsum, hW]
  unfold lowRoot
  exact div_le_div_of_nonneg_right (sub_le_sub_left (hM.trans hmono) _) (by norm_num)

/-- Consequences of the Gram structure: `q_A(a|0), q_A(c|1) ≥ 0`, both sum to one, and
`2|k_{ac}| ≤ q_A(a|0) + q_A(c|1)` (Cauchy–Schwarz). -/
theorem gram_facts {u v : Fin 2 → α → β → E} {k : α → α → ℂ} {pA pC : α → ℝ}
    {q : Table α β} (hq : IsNoSignalling q)
    (hq0 : ∀ y a b, q 0 y a b = ‖u y a b‖ ^ 2) (hq1 : ∀ y c b, q 1 y c b = ‖v y c b‖ ^ 2)
    (hpA : ∀ y a, ∑ b, ‖u y a b‖ ^ 2 = pA a) (hpC : ∀ y c, ∑ b, ‖v y c b‖ ^ 2 = pC c)
    (hkCS : ∀ a c, ‖k a c‖ ^ 2 ≤ pA a * pC c) :
    (∀ a, 0 ≤ pA a) ∧ (∀ c, 0 ≤ pC c) ∧ ∑ a, pA a = 1 ∧ ∑ c, pC c = 1 ∧
      ∀ a c, 2 * ‖k a c‖ ≤ pA a + pC c := by
  have hpA0 : ∀ a, 0 ≤ pA a := fun a => by
    rw [← hpA 0 a]
    exact Finset.sum_nonneg (fun b _ => sq_nonneg _)
  have hpC0 : ∀ c, 0 ≤ pC c := fun c => by
    rw [← hpC 0 c]
    exact Finset.sum_nonneg (fun b _ => sq_nonneg _)
  have hpA1 : ∑ a, pA a = 1 := by
    rw [← hq.isBehaviour.sum_eq_one 0 0]
    refine Finset.sum_congr rfl (fun a _ => ?_)
    rw [← hpA 0 a]
    exact Finset.sum_congr rfl (fun b _ => (hq0 0 a b).symm)
  have hpC1 : ∑ c, pC c = 1 := by
    rw [← hq.isBehaviour.sum_eq_one 1 0]
    refine Finset.sum_congr rfl (fun c _ => ?_)
    rw [← hpC 0 c]
    exact Finset.sum_congr rfl (fun b _ => (hq1 0 c b).symm)
  have hkA : ∀ a c, 2 * ‖k a c‖ ≤ pA a + pC c := by
    intro a c
    have h1 : ‖k a c‖ ^ 2 ≤ ((pA a + pC c) / 2) ^ 2 := by
      nlinarith [hkCS a c, sq_nonneg (pA a - pC c)]
    have h2 : ‖k a c‖ ≤ (pA a + pC c) / 2 :=
      calc ‖k a c‖ = Real.sqrt (‖k a c‖ ^ 2) := (Real.sqrt_sq (norm_nonneg _)).symm
        _ ≤ Real.sqrt (((pA a + pC c) / 2) ^ 2) := Real.sqrt_le_sqrt h1
        _ = (pA a + pC c) / 2 := Real.sqrt_sq (by linarith [hpA0 a, hpC0 c])
    linarith
  exact ⟨hpA0, hpC0, hpA1, hpC1, hkA⟩

/-- **The local model (F.12).** If a behaviour `q` arises from vectors `u^y_{ab}`, `v^y_{cb}` with the
Gram structure of the module docstring, then `LF(q) ≥ Σ_{a,c} h_{ac}`. -/
theorem sum_lowRoot_le_localFraction {u v : Fin 2 → α → β → E} {k : α → α → ℂ} {pA pC : α → ℝ}
    {q : Table α β} (hq : IsNoSignalling q)
    (hq0 : ∀ y a b, q 0 y a b = ‖u y a b‖ ^ 2) (hq1 : ∀ y c b, q 1 y c b = ‖v y c b‖ ^ 2)
    (hu : ∀ y b a a', a ≠ a' → inner ℂ (u y a b) (u y a' b) = 0)
    (hv : ∀ y b c c', c ≠ c' → inner ℂ (v y c b) (v y c' b) = 0)
    (hk : ∀ y a c, ∑ b, inner ℂ (u y a b) (v y c b) = k a c)
    (hpA : ∀ y a, ∑ b, ‖u y a b‖ ^ 2 = pA a) (hpC : ∀ y c, ∑ b, ‖v y c b‖ ^ 2 = pC c)
    (hkA : ∀ a c, 2 * ‖k a c‖ ≤ pA a + pC c) :
    ∑ l : α × α, lowRoot (pA l.1 + pC l.2) ‖k l.1 l.2‖ ≤ localFraction q := by
  obtain ⟨a₀, -, ha₀⟩ := Finset.exists_ne_zero_of_sum_ne_zero
    (show ∑ a, ∑ b, q 0 0 a b ≠ 0 by rw [hq.isBehaviour.sum_eq_one 0 0]; exact one_ne_zero)
  obtain ⟨b₀, -, -⟩ := Finset.exists_ne_zero_of_sum_ne_zero ha₀
  -- the total weight `H = Σ_{a,c} h_{ac}` of the local component
  obtain ⟨H, hHdef⟩ : ∃ H : ℝ, H = ∑ l : α × α, lowRoot (pA l.1 + pC l.2) ‖k l.1 l.2‖ :=
    ⟨_, rfl⟩
  rw [← hHdef]
  have hH0 : 0 ≤ H := by
    rw [hHdef]
    exact Finset.sum_nonneg (fun l _ => lowRoot_nonneg (norm_nonneg _) (hkA l.1 l.2))
  rcases eq_or_lt_of_le hH0 with h0 | hHpos
  · rw [← h0]
    exact localFraction_nonneg hq
  have hp1 : ∑ l : α × α, lowRoot (pA l.1 + pC l.2) ‖k l.1 l.2‖ / H = 1 := by
    rw [← Finset.sum_div, ← hHdef, div_self hHpos.ne']
  -- the local hidden-variable model (F.12), normalised
  have hL := lhv_mem_localSet (fun l : α × α => lowRoot (pA l.1 + pC l.2) ‖k l.1 l.2‖ / H)
    (fun l => div_nonneg (lowRoot_nonneg (norm_nonneg _) (hkA l.1 l.2)) hHpos.le) hp1
    aliceResp (bobResp u v b₀) aliceResp_nonneg sum_aliceResp
    (bobResp_nonneg u v b₀) (sum_bobResp u v b₀)
  -- `H · L(a,b|x,y) ≤ Σ_{(a',c')} A_{(a',c')}(a|x) t^y_{a'c'b}`
  have hgen : ∀ x y a b, H * ∑ l : α × α, (lowRoot (pA l.1 + pC l.2) ‖k l.1 l.2‖ / H)
        * (aliceResp l x a * bobResp u v b₀ l y b)
      ≤ ∑ l : α × α, aliceResp l x a * tWeight u v y l.1 l.2 b := by
    intro x y a b
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum (fun l _ => ?_)
    have h1 := lowRoot_mul_bobResp_le hk hpA hpC hkA b₀ l y b
    have h2 := aliceResp_nonneg l x a
    have h3 : H * (lowRoot (pA l.1 + pC l.2) ‖k l.1 l.2‖ / H)
        = lowRoot (pA l.1 + pC l.2) ‖k l.1 l.2‖ := mul_div_cancel₀ _ hHpos.ne'
    calc H * (lowRoot (pA l.1 + pC l.2) ‖k l.1 l.2‖ / H
          * (aliceResp l x a * bobResp u v b₀ l y b))
        = aliceResp l x a * ((H * (lowRoot (pA l.1 + pC l.2) ‖k l.1 l.2‖ / H))
          * bobResp u v b₀ l y b) := by ring
      _ = aliceResp l x a * (lowRoot (pA l.1 + pC l.2) ‖k l.1 l.2‖ * bobResp u v b₀ l y b) := by
          rw [h3]
      _ ≤ aliceResp l x a * tWeight u v y l.1 l.2 b := mul_le_mul_of_nonneg_left h1 h2
  -- input `0`: only the hidden pairs `(a, c')` contribute, and (F.11) bounds the sum by `q`
  have hsum0 : ∀ y a b, ∑ l : α × α, aliceResp l 0 a * tWeight u v y l.1 l.2 b ≤ q 0 y a b := by
    intro y a b
    rw [Fintype.sum_prod_type, Finset.sum_eq_single_of_mem a (Finset.mem_univ a)]
    · have hA : ∀ c' : α, aliceResp (a, c') 0 a = 1 := by
        intro c'
        unfold aliceResp
        simp
      simp only [hA, one_mul]
      rw [hq0 y a b]
      exact sum_tWeight_le_left hv y a b
    · intro a' _ ha'
      refine Finset.sum_eq_zero (fun c' _ => ?_)
      have hA : aliceResp (a', c') 0 a = 0 := by
        unfold aliceResp
        simp [Ne.symm ha']
      rw [hA, zero_mul]
  -- input `1`: only the hidden pairs `(a', c)` contribute
  have hsum1 : ∀ y c b, ∑ l : α × α, aliceResp l 1 c * tWeight u v y l.1 l.2 b ≤ q 1 y c b := by
    intro y c b
    rw [Fintype.sum_prod_type, Finset.sum_comm, Finset.sum_eq_single_of_mem c (Finset.mem_univ c)]
    · have hA : ∀ a' : α, aliceResp (a', c) 1 c = 1 := by
        intro a'
        unfold aliceResp
        simp
      simp only [hA, one_mul]
      rw [hq1 y c b]
      exact sum_tWeight_le_right hu y c b
    · intro c' _ hc'
      refine Finset.sum_eq_zero (fun a' _ => ?_)
      have hA : aliceResp (a', c') 1 c = 0 := by
        unfold aliceResp
        simp [Ne.symm hc']
      rw [hA, zero_mul]
  refine le_csSup (localFraction_set_bddAbove hq) ⟨hHpos.le, _, hL, ?_⟩
  exact Fin.forall_fin_two.mpr ⟨fun y a b => le_trans (hgen 0 y a b) (hsum0 y a b),
    fun y c b => le_trans (hgen 1 y c b) (hsum1 y c b)⟩

/-- **Theorem F.3 (local-component bound), vector form.** If a behaviour `q` arises from vectors
`u^y_{ab}`, `v^y_{cb}` with the Gram structure listed in the module docstring, then
`LF(q) ≥ (m_A - √(m_A² - 4))/2` with `m_A = 2|α|` (each of Alice's two measurements has `|α|`
outcomes). -/
theorem lowRoot_le_localFraction {u v : Fin 2 → α → β → E} {k : α → α → ℂ} {pA pC : α → ℝ}
    {q : Table α β} (hq : IsNoSignalling q)
    (hq0 : ∀ y a b, q 0 y a b = ‖u y a b‖ ^ 2) (hq1 : ∀ y c b, q 1 y c b = ‖v y c b‖ ^ 2)
    (hu : ∀ y b a a', a ≠ a' → inner ℂ (u y a b) (u y a' b) = 0)
    (hv : ∀ y b c c', c ≠ c' → inner ℂ (v y c b) (v y c' b) = 0)
    (hk : ∀ y a c, ∑ b, inner ℂ (u y a b) (v y c b) = k a c)
    (hpA : ∀ y a, ∑ b, ‖u y a b‖ ^ 2 = pA a) (hpC : ∀ y c, ∑ b, ‖v y c b‖ ^ 2 = pC c)
    (hkCS : ∀ a c, ‖k a c‖ ^ 2 ≤ pA a * pC c) (hk1 : ∑ a, ∑ c, k a c = 1) :
    lowRoot (2 * Fintype.card α) 1 ≤ localFraction q := by
  obtain ⟨-, -, hpA1, hpC1, hkA⟩ := gram_facts hq hq0 hq1 hpA hpC hkCS
  exact (lowRoot_le_sum_lowRoot hkA hpA1 hpC1 hk1).trans
    (sum_lowRoot_le_localFraction hq hq0 hq1 hu hv hk hpA hpC hkA)

theorem lowRoot_zero_right {w : ℝ} (hw : 0 ≤ w) : lowRoot w 0 = 0 := by
  unfold lowRoot
  rw [show w ^ 2 - 4 * (0 : ℝ) ^ 2 = w ^ 2 by ring, Real.sqrt_sq hw, sub_self, zero_div]

/-- The Jensen step when Alice's measurements have outcome supports `S₀` and `S₁`
(`q_A(a|0) = 0` off `S₀`, `q_A(c|1) = 0` off `S₁`): `Σ_{a,c} h_{ac} ≥ (m_A - √(m_A² - 4))/2` with
`m_A = |S₀| + |S₁|`. -/
theorem lowRoot_le_sum_lowRoot_support {k : α → α → ℂ} {pA pC : α → ℝ} (S₀ S₁ : Finset α)
    (hpA0 : ∀ a, 0 ≤ pA a) (hpC0 : ∀ c, 0 ≤ pC c)
    (hS₀ : ∀ a ∉ S₀, pA a = 0) (hS₁ : ∀ c ∉ S₁, pC c = 0)
    (hkCS : ∀ a c, ‖k a c‖ ^ 2 ≤ pA a * pC c) (hkA : ∀ a c, 2 * ‖k a c‖ ≤ pA a + pC c)
    (hpA1 : ∑ a, pA a = 1) (hpC1 : ∑ c, pC c = 1) (hk1 : ∑ a, ∑ c, k a c = 1) :
    lowRoot (S₀.card + S₁.card) 1 ≤ ∑ l : α × α, lowRoot (pA l.1 + pC l.2) ‖k l.1 l.2‖ := by
  have hk0 : ∀ l : α × α, l ∉ S₀ ×ˢ S₁ → k l.1 l.2 = 0 := by
    intro l hl
    rw [Finset.mem_product, not_and_or] at hl
    have hprod : pA l.1 * pC l.2 = 0 := by
      rcases hl with h | h
      · rw [hS₀ l.1 h, zero_mul]
      · rw [hS₁ l.2 h, mul_zero]
    have h2 : ‖k l.1 l.2‖ ^ 2 ≤ 0 := by
      have h3 := hkCS l.1 l.2
      rwa [hprod] at h3
    exact norm_eq_zero.mp ((pow_eq_zero_iff two_ne_zero).mp (le_antisymm h2 (sq_nonneg _)))
  have hh0 : ∀ l : α × α, l ∉ S₀ ×ˢ S₁ → lowRoot (pA l.1 + pC l.2) ‖k l.1 l.2‖ = 0 := by
    intro l hl
    rw [hk0 l hl, norm_zero]
    exact lowRoot_zero_right (add_nonneg (hpA0 l.1) (hpC0 l.2))
  rw [← Finset.sum_subset (Finset.subset_univ (S₀ ×ˢ S₁)) (fun l _ hl => hh0 l hl)]
  have hA1 : ∑ a ∈ S₀, pA a = 1 := by
    rw [← hpA1]
    exact Finset.sum_subset (Finset.subset_univ _) (fun a _ ha => hS₀ a ha)
  have hC1 : ∑ c ∈ S₁, pC c = 1 := by
    rw [← hpC1]
    exact Finset.sum_subset (Finset.subset_univ _) (fun c _ hc => hS₁ c hc)
  have hW : ∑ l ∈ S₀ ×ˢ S₁, (pA l.1 + pC l.2) = S₀.card + S₁.card := by
    rw [Finset.sum_product]
    simp only [Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul, ← Finset.mul_sum, hA1, hC1]
    ring
  have hK : 1 ≤ ∑ l ∈ S₀ ×ˢ S₁, ‖k l.1 l.2‖ := by
    have h1 : ‖∑ l ∈ S₀ ×ˢ S₁, k l.1 l.2‖ ≤ ∑ l ∈ S₀ ×ˢ S₁, ‖k l.1 l.2‖ := norm_sum_le _ _
    have h2 : ∑ l ∈ S₀ ×ˢ S₁, k l.1 l.2 = 1 := by
      rw [Finset.sum_subset (Finset.subset_univ (S₀ ×ˢ S₁)) (fun l _ hl => hk0 l hl),
        Fintype.sum_prod_type' k, hk1]
    rw [h2, norm_one] at h1
    exact h1
  have hM : ∑ l ∈ S₀ ×ˢ S₁, Real.sqrt ((pA l.1 + pC l.2) ^ 2 - 4 * ‖k l.1 l.2‖ ^ 2)
      ≤ Real.sqrt ((∑ l ∈ S₀ ×ˢ S₁, (pA l.1 + pC l.2)) ^ 2
        - 4 * (∑ l ∈ S₀ ×ˢ S₁, ‖k l.1 l.2‖) ^ 2) :=
    revMinkowski_sum (fun l : α × α => pA l.1 + pC l.2) (fun l => ‖k l.1 l.2‖)
      (S₀ ×ˢ S₁) (fun l _ => norm_nonneg _) (fun l _ => hkA l.1 l.2)
  rw [hW] at hM
  have hmono : Real.sqrt (((S₀.card : ℝ) + S₁.card) ^ 2
        - 4 * (∑ l ∈ S₀ ×ˢ S₁, ‖k l.1 l.2‖) ^ 2)
      ≤ Real.sqrt (((S₀.card : ℝ) + S₁.card) ^ 2 - 4 * 1 ^ 2) :=
    Real.sqrt_le_sqrt (by nlinarith [hK])
  have hsum : ∑ l ∈ S₀ ×ˢ S₁, lowRoot (pA l.1 + pC l.2) ‖k l.1 l.2‖
      = ((∑ l ∈ S₀ ×ˢ S₁, (pA l.1 + pC l.2))
        - ∑ l ∈ S₀ ×ˢ S₁, Real.sqrt ((pA l.1 + pC l.2) ^ 2 - 4 * ‖k l.1 l.2‖ ^ 2)) / 2 := by
    unfold lowRoot
    rw [← Finset.sum_sub_distrib, Finset.sum_div]
  rw [hsum, hW]
  unfold lowRoot
  exact div_le_div_of_nonneg_right (sub_le_sub_left (hM.trans hmono) _) (by norm_num)

/-- **Theorem F.3, general form, vector version.** If Alice's measurement `0` has outcome support
`S₀` and measurement `1` has outcome support `S₁`, then `LF(q) ≥ (m_A - √(m_A² - 4))/2` with
`m_A = |S₀| + |S₁|`. -/
theorem lowRoot_le_localFraction_support {u v : Fin 2 → α → β → E} {k : α → α → ℂ}
    {pA pC : α → ℝ} {q : Table α β} (hq : IsNoSignalling q)
    (hq0 : ∀ y a b, q 0 y a b = ‖u y a b‖ ^ 2) (hq1 : ∀ y c b, q 1 y c b = ‖v y c b‖ ^ 2)
    (hu : ∀ y b a a', a ≠ a' → inner ℂ (u y a b) (u y a' b) = 0)
    (hv : ∀ y b c c', c ≠ c' → inner ℂ (v y c b) (v y c' b) = 0)
    (hk : ∀ y a c, ∑ b, inner ℂ (u y a b) (v y c b) = k a c)
    (hpA : ∀ y a, ∑ b, ‖u y a b‖ ^ 2 = pA a) (hpC : ∀ y c, ∑ b, ‖v y c b‖ ^ 2 = pC c)
    (hkCS : ∀ a c, ‖k a c‖ ^ 2 ≤ pA a * pC c) (hk1 : ∑ a, ∑ c, k a c = 1)
    (S₀ S₁ : Finset α) (hS₀ : ∀ a ∉ S₀, pA a = 0) (hS₁ : ∀ c ∉ S₁, pC c = 0) :
    lowRoot (S₀.card + S₁.card) 1 ≤ localFraction q := by
  obtain ⟨hpA0, hpC0, hpA1, hpC1, hkA⟩ := gram_facts hq hq0 hq1 hpA hpC hkCS
  exact (lowRoot_le_sum_lowRoot_support S₀ S₁ hpA0 hpC0 hS₀ hS₁ hkCS hkA hpA1 hpC1 hk1).trans
    (sum_lowRoot_le_localFraction hq hq0 hq1 hu hv hk hpA hpC hkA)

end

end CGLMPBounds
