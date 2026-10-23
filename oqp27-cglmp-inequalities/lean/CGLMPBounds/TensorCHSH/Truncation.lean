module

public import CGLMPBounds.TensorCHSH.Binomial
public import CGLMPBounds.Scenario.CoarseGrain

@[expose] public section


/-!
# Discarding output bits of the tensor CHSH table

Supplement, text before (F.7): "Discarding all but the first `M` output bits maps `T_m` to `T_M` and
`u_{2^m}` to `u_{2^M}`, for every `m ≥ M`. Local behaviours remain local under this map. Data
processing and preservation of the noise mixture therefore give `v_crit(T_m) ≤ v_crit(T_M)`."

Here bits are discarded one at a time from the end (`Fin.init`), for the closed-formula table
`tensorTable m ρ` of (F.5).

* `coarseGrain_init_tensorTable` : dropping the last bit maps `T_{M+1}` to `T_M`;
* `critVisibility_tensorTable_le` : `v_crit(T_m) ≤ v_crit(T_M)` for `M ≤ m` (visibility half of (F.7)).
-/

namespace CGLMPBounds.TensorCHSH

noncomputable section

open Finset

theorem errCount_snoc {M : ℕ} (x y : Fin 2) (s t : Fin M → Bool) (u v : Bool) :
    errCount x y (Fin.snoc (α := fun _ => Bool) s u) (Fin.snoc (α := fun _ => Bool) t v)
      = errCount x y s t + errBit x y u v := by
  rw [errCount_eq_sum, errCount_eq_sum, Fin.sum_univ_castSucc]
  simp only [Fin.snoc_castSucc, Fin.snoc_last]

theorem errBit_le_one (x y : Fin 2) (u v : Bool) : errBit x y u v ≤ 1 := by
  unfold errBit
  split_ifs <;> omega

/-- The closed formula factorises over the last coordinate. -/
theorem tensorTable_snoc {M : ℕ} (ρ : ℝ) (x y : Fin 2) (s t : Fin M → Bool) (u v : Bool) :
    tensorTable (M + 1) ρ x y (Fin.snoc (α := fun _ => Bool) s u)
        (Fin.snoc (α := fun _ => Bool) t v)
      = tensorTable M ρ x y s t
        * (1 / 2 * ((1 - ρ) ^ (1 - errBit x y u v) * ρ ^ errBit x y u v)) := by
  have hK : errCount x y s t ≤ M := errCount_le x y s t
  have he := errBit_le_one x y u v
  simp only [tensorTable, errCount_snoc]
  rw [show M + 1 - (errCount x y s t + errBit x y u v)
      = (M - errCount x y s t) + (1 - errBit x y u v) by omega]
  simp only [pow_add, pow_one]
  ring

/-- The last pair of output bits of the single-pair factor is normalised. -/
theorem sum_last_bit (ρ : ℝ) (x y : Fin 2) :
    1 / 2 * ∑ u : Bool, ∑ v : Bool, (1 - ρ) ^ (1 - errBit x y u v) * ρ ^ errBit x y u v = 1 := by
  unfold errBit
  cases h : (decide (x = 1) && decide (y = 1)) <;> simp [Fintype.sum_bool] <;> ring

/-- Sums over `M+1`-bit strings split off the last bit. -/
theorem sum_snoc {M : ℕ} (F : (Fin (M + 1) → Bool) → ℝ) :
    ∑ a, F a = ∑ u : Bool, ∑ a0 : Fin M → Bool, F (Fin.snoc (α := fun _ => Bool) a0 u) :=
  (Fintype.sum_equiv (Fin.snocEquiv (fun _ => Bool)) _ F (fun _ => rfl)).symm.trans
    (Fintype.sum_prod_type _)

theorem sum_ite_and_left {γ : Type*} [Fintype γ] (P : Prop) [Decidable P] (Q : γ → Prop)
    [DecidablePred Q] (F : γ → ℝ) :
    ∑ b, (if P ∧ Q b then F b else 0) = if P then ∑ b, (if Q b then F b else 0) else 0 := by
  by_cases h : P <;> simp [h]

/-- Entries of a coarse-grained table as sums over fibres. -/
theorem coarseGrain_apply {α β α' β' : Type*} [Fintype α] [Fintype β] [DecidableEq α']
    [DecidableEq β'] (f : α → α') (g : β → β') (q : Table α β) (x y : Fin 2) (a' : α') (b' : β') :
    coarseGrain f g q x y a' b' = ∑ a, ∑ b, if a' = f a ∧ b' = g b then q x y a b else 0 := by
  show bell (fibreTable f g x y a' b') q = _
  rw [bell_apply, Finset.sum_eq_single_of_mem x (Finset.mem_univ x)]
  · rw [Finset.sum_eq_single_of_mem y (Finset.mem_univ y)]
    · refine Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl (fun b _ => ?_))
      show (if (x = x ∧ y = y) ∧ (a' = f a ∧ b' = g b) then (1 : ℝ) else 0) * q x y a b = _
      by_cases h : a' = f a ∧ b' = g b
      · rw [if_pos ⟨⟨rfl, rfl⟩, h⟩, if_pos h, one_mul]
      · rw [if_neg (fun h' => h h'.2), if_neg h, zero_mul]
    · intro y₁ _ hy
      refine Finset.sum_eq_zero (fun a _ => Finset.sum_eq_zero (fun b _ => ?_))
      show (if (x = x ∧ y₁ = y) ∧ (a' = f a ∧ b' = g b) then (1 : ℝ) else 0) * q x y₁ a b = 0
      rw [if_neg (fun h' => hy h'.1.2), zero_mul]
  · intro x₁ _ hx
    refine Finset.sum_eq_zero (fun y₁ _ => Finset.sum_eq_zero (fun a _ =>
      Finset.sum_eq_zero (fun b _ => ?_)))
    show (if (x₁ = x ∧ y₁ = y) ∧ (a' = f a ∧ b' = g b) then (1 : ℝ) else 0) * q x₁ y₁ a b = 0
    rw [if_neg (fun h' => hx h'.1.1), zero_mul]

/-- Dropping the last output bit of both parties maps `T_{M+1}` to `T_M`. -/
theorem coarseGrain_init_tensorTable (M : ℕ) (ρ : ℝ) :
    coarseGrain (Fin.init (α := fun _ => Bool)) (Fin.init (α := fun _ => Bool))
      (tensorTable (M + 1) ρ) = tensorTable M ρ := by
  funext x y s t
  rw [coarseGrain_apply, sum_snoc]
  simp only [Fin.init_snoc, sum_ite_and_left]
  simp only [Finset.sum_ite_eq, Finset.mem_univ, ite_true]
  have key : ∀ u : Bool, ∑ b : Fin (M + 1) → Bool,
      (if t = Fin.init b then tensorTable (M + 1) ρ x y (Fin.snoc (α := fun _ => Bool) s u) b
        else 0)
      = ∑ v : Bool, tensorTable (M + 1) ρ x y (Fin.snoc (α := fun _ => Bool) s u)
          (Fin.snoc (α := fun _ => Bool) t v) := by
    intro u
    rw [sum_snoc]
    simp only [Fin.init_snoc, Finset.sum_ite_eq, Finset.mem_univ, ite_true]
  simp only [key, tensorTable_snoc, ← Finset.mul_sum]
  rw [sum_last_bit, mul_one]

theorem coarseGrain_init_uniformTable (M : ℕ) :
    coarseGrain (Fin.init (α := fun _ => Bool)) (Fin.init (α := fun _ => Bool))
      (uniformTable (Fin (M + 1) → Bool) (Fin (M + 1) → Bool))
      = uniformTable (Fin M → Bool) (Fin M → Bool) := by
  rw [← tensorTable_half, ← tensorTable_half, coarseGrain_init_tensorTable]

/-- Dropping one output bit cannot decrease the critical visibility. -/
theorem critVisibility_tensorTable_succ_le (M : ℕ) (ρ : ℝ) :
    critVisibility (tensorTable (M + 1) ρ) ≤ critVisibility (tensorTable M ρ) := by
  have h := critVisibility_le_coarseGrain (Fin.init (α := fun _ => Bool))
    (Fin.init (α := fun _ => Bool)) (coarseGrain_init_uniformTable M) (tensorTable (M + 1) ρ)
  rwa [coarseGrain_init_tensorTable] at h

/-- Visibility half of (F.7): `v_crit(T_m) ≤ v_crit(T_M)` for `M ≤ m`. -/
theorem critVisibility_tensorTable_le {M m : ℕ} (h : M ≤ m) (ρ : ℝ) :
    critVisibility (tensorTable m ρ) ≤ critVisibility (tensorTable M ρ) := by
  induction h with
  | refl => exact le_rfl
  | step _ ih => exact (critVisibility_tensorTable_succ_le _ ρ).trans ih

end

end CGLMPBounds.TensorCHSH
