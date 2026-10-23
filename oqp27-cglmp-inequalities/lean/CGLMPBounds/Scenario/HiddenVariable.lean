module

public import CGLMPBounds.Scenario.Local

@[expose] public section


/-!
# Local hidden-variable models with stochastic responses

A table of the form `∑_λ p(λ) A_λ(a|x) B_λ(b|y)`, with `p` a probability weight on a finite set
and `A_λ(·|x)`, `B_λ(·|y)` probability vectors, lies in the Bell-local set (the convex hull of the
deterministic tables). This is the standard equivalence between hidden-variable models with
stochastic and with deterministic responses, in the direction needed to exhibit local models.

* `prodTable_mem_localSet` : product tables `A(a|x) B(b|y)` are local;
* `lhv_mem_localSet`       : finite mixtures of product tables are local.
-/

namespace CGLMPBounds

noncomputable section

/-- A sum over functions on `Fin 2` is a double sum over the two values. -/
theorem sum_fin_two_arrow {γ : Type*} [Fintype γ] (F : γ → γ → ℝ) :
    ∑ u : Fin 2 → γ, F (u 0) (u 1) = ∑ c₀, ∑ c₁, F c₀ c₁ :=
  (Fintype.sum_equiv (finTwoArrowEquiv γ) (fun u => F (u 0) (u 1)) (fun p => F p.1 p.2)
    (fun _ => rfl)).trans (Fintype.sum_prod_type' F)

theorem sum_fin_two_weight {γ : Type*} [Fintype γ] (A : Fin 2 → γ → ℝ)
    (hA : ∀ x, ∑ c, A x c = 1) : ∑ u : Fin 2 → γ, A 0 (u 0) * A 1 (u 1) = 1 := by
  refine (sum_fin_two_arrow (fun c₀ c₁ => A 0 c₀ * A 1 c₁)).trans ?_
  simp only [← Finset.mul_sum, hA, mul_one]

theorem sum_fin_two_weight_indicator {γ : Type*} [Fintype γ] [DecidableEq γ]
    (A : Fin 2 → γ → ℝ) (hA : ∀ x, ∑ c, A x c = 1) (a : γ) :
    ∀ x : Fin 2,
      ∑ u : Fin 2 → γ, (A 0 (u 0) * A 1 (u 1)) * (if a = u x then 1 else 0) = A x a := by
  refine Fin.forall_fin_two.mpr ⟨?_, ?_⟩
  · refine (sum_fin_two_arrow
      (fun c₀ c₁ => (A 0 c₀ * A 1 c₁) * (if a = c₀ then 1 else 0))).trans ?_
    have inner : ∀ c₀ : γ, ∑ c₁, (A 0 c₀ * A 1 c₁) * (if a = c₀ then (1 : ℝ) else 0)
        = A 0 c₀ * (if a = c₀ then 1 else 0) := by
      intro c₀
      rw [← Finset.sum_mul, ← Finset.mul_sum, hA 1, mul_one]
    simp only [inner]
    rw [Finset.sum_eq_single_of_mem a (Finset.mem_univ a)]
    · rw [if_pos rfl, mul_one]
    · intro c _ hc
      rw [if_neg (fun e => hc e.symm), mul_zero]
  · refine (sum_fin_two_arrow
      (fun c₀ c₁ => (A 0 c₀ * A 1 c₁) * (if a = c₁ then 1 else 0))).trans ?_
    have inner : ∀ c₀ : γ, ∑ c₁, (A 0 c₀ * A 1 c₁) * (if a = c₁ then (1 : ℝ) else 0)
        = A 0 c₀ * A 1 a := by
      intro c₀
      rw [Finset.sum_eq_single_of_mem a (Finset.mem_univ a)]
      · rw [if_pos rfl, mul_one]
      · intro c _ hc
        rw [if_neg (fun e => hc e.symm), mul_zero]
    simp only [inner]
    rw [← Finset.sum_mul, hA 0, one_mul]

theorem sum_prod_mul {U V : Type*} [Fintype U] [Fintype V] (f : U → ℝ) (g : V → ℝ) :
    ∑ s : U × V, f s.1 * g s.2 = (∑ u, f u) * ∑ v, g v :=
  (Fintype.sum_prod_type' (fun u v => f u * g v)).trans (Finset.sum_mul_sum _ _ _ _).symm

variable {α β : Type*} [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β]

/-- A product of stochastic response functions is Bell-local. -/
theorem prodTable_mem_localSet (A : Fin 2 → α → ℝ) (B : Fin 2 → β → ℝ)
    (hA0 : ∀ x a, 0 ≤ A x a) (hA1 : ∀ x, ∑ a, A x a = 1)
    (hB0 : ∀ y b, 0 ≤ B y b) (hB1 : ∀ y, ∑ b, B y b = 1) :
    (fun x y a b => A x a * B y b : Table α β) ∈ localSet α β := by
  rw [mem_localSet_iff]
  refine ⟨fun s => (A 0 (s.1 0) * A 1 (s.1 1)) * (B 0 (s.2 0) * B 1 (s.2 1)),
    fun s => ?_, ?_, ?_⟩
  · exact mul_nonneg (mul_nonneg (hA0 _ _) (hA0 _ _)) (mul_nonneg (hB0 _ _) (hB0 _ _))
  · refine (sum_prod_mul (fun u : Fin 2 → α => A 0 (u 0) * A 1 (u 1))
      (fun v : Fin 2 → β => B 0 (v 0) * B 1 (v 1))).trans ?_
    rw [sum_fin_two_weight A hA1, sum_fin_two_weight B hB1, one_mul]
  · funext x y a b
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, detTable]
    have key : ∀ s : Strategy α β,
        (A 0 (s.1 0) * A 1 (s.1 1)) * (B 0 (s.2 0) * B 1 (s.2 1))
            * (if a = s.1 x ∧ b = s.2 y then (1 : ℝ) else 0)
          = ((A 0 (s.1 0) * A 1 (s.1 1)) * (if a = s.1 x then 1 else 0))
            * ((B 0 (s.2 0) * B 1 (s.2 1)) * (if b = s.2 y then 1 else 0)) := by
      intro s
      by_cases h1 : a = s.1 x <;> by_cases h2 : b = s.2 y <;> simp [h1, h2]
    simp only [key]
    refine ((sum_prod_mul
      (fun u : Fin 2 → α => (A 0 (u 0) * A 1 (u 1)) * (if a = u x then 1 else 0))
      (fun v : Fin 2 → β => (B 0 (v 0) * B 1 (v 1)) * (if b = v y then 1 else 0))).trans ?_).symm
    rw [sum_fin_two_weight_indicator A hA1 a x, sum_fin_two_weight_indicator B hB1 b y]

/-- A finite local hidden-variable model with stochastic responses is Bell-local. -/
theorem lhv_mem_localSet {Λ : Type*} [Fintype Λ] (p : Λ → ℝ) (hp0 : ∀ l, 0 ≤ p l)
    (hp1 : ∑ l, p l = 1) (A : Λ → Fin 2 → α → ℝ) (B : Λ → Fin 2 → β → ℝ)
    (hA0 : ∀ l x a, 0 ≤ A l x a) (hA1 : ∀ l x, ∑ a, A l x a = 1)
    (hB0 : ∀ l y b, 0 ≤ B l y b) (hB1 : ∀ l y, ∑ b, B l y b = 1) :
    (fun x y a b => ∑ l, p l * (A l x a * B l y b) : Table α β) ∈ localSet α β := by
  have hEq : (fun x y a b => ∑ l, p l * (A l x a * B l y b) : Table α β)
      = ∑ l, p l • (fun x y a b => A l x a * B l y b : Table α β) := by
    funext x y a b
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  rw [hEq]
  exact (convex_convexHull ℝ _).sum_mem (fun l _ => hp0 l) hp1
    (fun l _ => prodTable_mem_localSet (A l) (B l) (hA0 l) (hA1 l) (hB0 l) (hB1 l))

end

end CGLMPBounds
