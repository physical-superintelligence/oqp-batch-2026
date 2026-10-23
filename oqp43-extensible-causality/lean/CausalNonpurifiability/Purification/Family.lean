module

public import CausalNonpurifiability.Definitions.ProcessFamily
public import CausalNonpurifiability.Purification.Heisenberg

@[expose] public section


/-!
# `CausalNonpurifiability.Purification.Family`

Steps 2 and 3 of the proof of Theorem 6.1 (manuscript Appendix A, `app:purcs`).

Let `S = |𝒰⟩⟩⟨⟨𝒰|` be a pure process (`Pure.exists_unitary`). For vectors `u`, `v` on the global
past, `procV U u v` is the operator `W_τ` of Step 2 for `τ = |u⟩⟨v|`, and
`reducePastFuture_eq_procV` says `W = W_{|0⟩⟨0|}`.

* Step 2: `procV U v v` is positive (`procV_posSemidef`), and `procV_normalization` evaluates
  `procV U u v` on pairs of channels; here the first clause of `Pure` (`Deterministic`) is used
  with one-dimensional additional systems. With the converse of Lemma 2.3
  (`lvEquations_of_channel_normalization`) this gives `procV_lvEquations`: every `W_τ`
  satisfies `eq:LV`.
* Step 3: through `procV_entry` the equations `eq:LV` become statements about `Φ†` (`heis`):
  `heis_lv_c` (from `eq:LV-c`), and `eq:no-self`, that is `heis_no_self_A` (from `eq:LV-a` and
  `eq:LV-c`) and `heis_no_self_B` (from `eq:LV-b` and `eq:LV-c`).

Helper lemmas on finite sums and the contractions `contr`, `trBO`, `trAO` are in the namespace
`CausalNonpurifiability.Family`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open Matrix
open scoped ComplexOrder Kronecker

namespace CausalNonpurifiability

noncomputable section

namespace Family

/-! ### Finite sums -/

theorem sum_mul_piSingle_one {X : Type} [Fintype X] [DecidableEq X] (g : X → ℂ) (x₀ : X) :
    ∑ x, g x * (Pi.single x₀ (1 : ℂ) : X → ℂ) x = g x₀ := by
  rw [Finset.sum_eq_single x₀]
  · simp
  · intro x _ hx
    simp [Pi.single_apply, hx]
  · intro h
    exact absurd (Finset.mem_univ _) h

theorem sum_sandwich {X Z : Type} [Fintype X] [Fintype Z] (α β : Z → X → ℂ) (u v : X → ℂ) :
    ∑ x, ∑ x', star (v x') * (∑ z, star (β z x') * α z x) * u x =
      ∑ z, (∑ x, α z x * u x) * star (∑ x', β z x' * v x') := by
  calc ∑ x, ∑ x', star (v x') * (∑ z, star (β z x') * α z x) * u x
      = ∑ x, ∑ x', ∑ z, α z x * u x * star (β z x' * v x') := by
        refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun x' _ => ?_
        rw [Finset.mul_sum, Finset.sum_mul]
        refine Finset.sum_congr rfl fun z _ => ?_
        rw [star_mul']
        ring
    _ = ∑ x, ∑ z, ∑ x', α z x * u x * star (β z x' * v x') :=
        Finset.sum_congr rfl fun x _ => Finset.sum_comm
    _ = ∑ z, ∑ x, ∑ x', α z x * u x * star (β z x' * v x') := Finset.sum_comm
    _ = ∑ z, (∑ x, α z x * u x) * star (∑ x', β z x' * v x') := by
        refine Finset.sum_congr rfl fun z _ => ?_
        rw [star_sum, Finset.sum_mul]
        refine Finset.sum_congr rfl fun x _ => ?_
        rw [Finset.mul_sum]

theorem sum_mul_const_mul_sum {Q Z : Type} [Fintype Q] [Fintype Z] (a : Q → ℂ) (c : ℂ)
    (b : Q → Z → ℂ) : ∑ q, a q * (c * ∑ z, b q z) = c * ∑ z, ∑ q, a q * b q z := by
  calc ∑ q, a q * (c * ∑ z, b q z) = ∑ q, ∑ z, c * (a q * b q z) := by
        refine Finset.sum_congr rfl fun q _ => ?_
        rw [Finset.mul_sum, Finset.mul_sum]
        exact Finset.sum_congr rfl fun z _ => by ring
    _ = ∑ z, ∑ q, c * (a q * b q z) := Finset.sum_comm
    _ = c * ∑ z, ∑ q, a q * b q z := by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun z _ => by rw [Finset.mul_sum]

theorem sum_sum_mul_const_mul_sum {A B Z : Type} [Fintype A] [Fintype B] [Fintype Z]
    (g : A → B → ℂ) (c : ℂ) (F : A → B → Z → ℂ) :
    ∑ a, ∑ b, g a b * (c * ∑ z, F a b z) = c * ∑ z, ∑ a, ∑ b, g a b * F a b z := by
  calc ∑ a, ∑ b, g a b * (c * ∑ z, F a b z) = ∑ a, c * ∑ z, ∑ b, g a b * F a b z :=
        Finset.sum_congr rfl fun a _ => sum_mul_const_mul_sum (g a) c (F a)
    _ = c * ∑ a, ∑ z, ∑ b, g a b * F a b z := by rw [Finset.mul_sum]
    _ = c * ∑ z, ∑ a, ∑ b, g a b * F a b z := by rw [Finset.sum_comm]

theorem sum_sum_sum_mul_comm {L Z : Type} [Fintype L] [Fintype Z] (s : Z → L → L → ℂ)
    (m : L → L → ℂ) :
    ∑ l, ∑ l', (∑ z, s z l l') * m l l' = ∑ z, ∑ l, ∑ l', s z l l' * m l l' := by
  calc ∑ l, ∑ l', (∑ z, s z l l') * m l l' = ∑ l, ∑ l', ∑ z, s z l l' * m l l' := by
        refine Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun l' _ => ?_
        rw [Finset.sum_mul]
    _ = ∑ l, ∑ z, ∑ l', s z l l' * m l l' := Finset.sum_congr rfl fun l _ => Finset.sum_comm
    _ = ∑ z, ∑ l, ∑ l', s z l l' * m l l' := Finset.sum_comm

theorem sum3_rotate {A O Z : Type} [Fintype A] [Fintype O] [Fintype Z] (F : A → O → Z → ℂ) :
    ∑ a, ∑ o, ∑ z, F a o z = ∑ z, ∑ a, ∑ o, F a o z := by
  calc ∑ a, ∑ o, ∑ z, F a o z = ∑ a, ∑ z, ∑ o, F a o z :=
        Finset.sum_congr rfl fun a _ => Finset.sum_comm
    _ = ∑ z, ∑ a, ∑ o, F a o z := Finset.sum_comm

/-! ### `Φ†` of matrix units -/

section HeisFacts

variable {F K N : Type} [Fintype F] [Fintype K] [Fintype N] [DecidableEq F] [DecidableEq K]
  [DecidableEq N]

theorem heis_unitMat_apply (U : Matrix (F × K) N ℂ) (k₀' k₀ : K) (a b : N) :
    heis U (unitMat k₀' k₀) a b = ∑ z, star (U (z, k₀') a) * U (z, k₀) b := by
  rw [heis_apply]
  refine Finset.sum_congr rfl fun z _ => ?_
  rw [Finset.sum_eq_single k₀]
  · rw [Finset.sum_eq_single k₀']
    · simp [unitMat_apply]
    · intro k' _ hk'
      simp [unitMat_apply, hk']
    · intro h
      exact absurd (Finset.mem_univ _) h
  · intro k _ hk
    have h0 : ∀ k', star (U (z, k') a) * unitMat k₀' k₀ k' k = 0 := by
      intro k'
      simp [unitMat_apply, hk]
    simp only [h0, Finset.sum_const_zero, zero_mul]
  · intro h
    exact absurd (Finset.mem_univ _) h

/-- Expansion of `Φ†(Q)` in matrix units. -/
theorem heis_eq_sum_unitMat (U : Matrix (F × K) N ℂ) (Q : Matrix K K ℂ) (a b : N) :
    heis U Q a b = ∑ q : K × K, Q q.2 q.1 * heis U (unitMat q.2 q.1) a b := by
  rw [Fintype.sum_prod_type]
  simp only [heis_unitMat_apply]
  rw [heis_apply]
  calc ∑ z, ∑ k, (∑ k', star (U (z, k') a) * Q k' k) * U (z, k) b
      = ∑ z, ∑ k, ∑ k', Q k' k * (star (U (z, k') a) * U (z, k) b) := by
        refine Finset.sum_congr rfl fun z _ => Finset.sum_congr rfl fun k _ => ?_
        rw [Finset.sum_mul]
        exact Finset.sum_congr rfl fun k' _ => by ring
    _ = ∑ k, ∑ z, ∑ k', Q k' k * (star (U (z, k') a) * U (z, k) b) := Finset.sum_comm
    _ = ∑ k, ∑ k', ∑ z, Q k' k * (star (U (z, k') a) * U (z, k) b) :=
        Finset.sum_congr rfl fun k _ => Finset.sum_comm
    _ = ∑ k, ∑ k', Q k' k * ∑ z, star (U (z, k') a) * U (z, k) b := by
        refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun k' _ => ?_
        rw [Finset.mul_sum]

end HeisFacts

/-! ### Channels with one-dimensional additional systems -/

theorem sum_linkOut {f : ℕ} {β : Type} [AddCommMonoid β] (g : LinkOut f 0 0 → β) :
    ∑ w, g w = ∑ z, g (z, (0, 0)) := by
  rw [Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun z _ => ?_
  rw [Fintype.sum_prod_type, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero, Fin.sum_univ_succ,
    Fin.sum_univ_zero, add_zero]

theorem one_apply_linkIn {p : ℕ} (x x' : Fin (p + 1)) :
    (1 : Op (LinkIn p 0 0)) (x, (0, 0)) (x', (0, 0)) = if x = x' then 1 else 0 := by
  by_cases h : x = x'
  · subst h
    simp
  · have hne : ((x, (0, 0)) : LinkIn p 0 0) ≠ (x', (0, 0)) := fun hh => h (congrArg Prod.fst hh)
    rw [Matrix.one_apply_ne hne, if_neg h]

theorem one_apply_prod_fin_one {I : Type} [DecidableEq I] (i j : I) (e e' : Fin (0 + 1)) :
    (1 : Op (I × Fin (0 + 1))) (i, e) (j, e') = (1 : Op I) i j := by
  have he : e = e' := Fin.ext (by have := e.isLt; have := e'.isLt; omega)
  rw [he]
  by_cases h : i = j
  · rw [h, Matrix.one_apply_eq, Matrix.one_apply_eq]
  · have hne : ((i, e') : I × Fin (0 + 1)) ≠ (j, e') := fun hh => h (congrArg Prod.fst hh)
    rw [Matrix.one_apply_ne hne, Matrix.one_apply_ne h]

theorem channelChoi_trivialExtA {D : Ports} {J : Op (Fin D.m × Fin D.d)} (hJ : J.PosSemidef)
    (h1 : ptraceOut J = 1) : ChannelChoi (trivialExtA D Jᵀ) := by
  refine ⟨?_, ?_⟩
  · have h : trivialExtA D Jᵀ = Jᵀ.submatrix
        (fun x : (Fin D.m × Fin (0 + 1)) × (Fin D.d × Fin (0 + 1)) => (x.1.1, x.2.1))
        (fun x : (Fin D.m × Fin (0 + 1)) × (Fin D.d × Fin (0 + 1)) => (x.1.1, x.2.1)) := by
      ext x y
      rfl
    rw [h]
    exact posSemidef_submatrix hJ.transpose _
  · ext ⟨i, e⟩ ⟨j, e'⟩
    have hJ1 := congrFun (congrFun h1 j) i
    rw [ptraceOut_apply] at hJ1
    show ∑ w : Fin D.d × Fin (0 + 1), J (j, w.1) (i, w.1) = _
    rw [Fintype.sum_prod_type, one_apply_prod_fin_one]
    simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
    rw [hJ1]
    by_cases hij : i = j
    · rw [hij]
    · rw [Matrix.one_apply_ne (Ne.symm hij), Matrix.one_apply_ne hij]

theorem channelChoi_trivialExtB {D : Ports} {J : Op (Fin D.n × Fin D.e)} (hJ : J.PosSemidef)
    (h1 : ptraceOut J = 1) : ChannelChoi (trivialExtB D Jᵀ) := by
  refine ⟨?_, ?_⟩
  · have h : trivialExtB D Jᵀ = Jᵀ.submatrix
        (fun x : (Fin D.n × Fin (0 + 1)) × (Fin D.e × Fin (0 + 1)) => (x.1.1, x.2.1))
        (fun x : (Fin D.n × Fin (0 + 1)) × (Fin D.e × Fin (0 + 1)) => (x.1.1, x.2.1)) := by
      ext x y
      rfl
    rw [h]
    exact posSemidef_submatrix hJ.transpose _
  · ext ⟨i, e⟩ ⟨j, e'⟩
    have hJ1 := congrFun (congrFun h1 j) i
    rw [ptraceOut_apply] at hJ1
    show ∑ w : Fin D.e × Fin (0 + 1), J (j, w.1) (i, w.1) = _
    rw [Fintype.sum_prod_type, one_apply_prod_fin_one]
    simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
    rw [hJ1]
    by_cases hij : i = j
    · rw [hij]
    · rw [Matrix.one_apply_ne (Ne.symm hij), Matrix.one_apply_ne hij]

/-- The first clause of `Pure` (`Deterministic`) for a pair of channels without additional
systems, read at the entry `|x⟩⟨x'|` of the global past after the trace over the future. -/
theorem link_trivial_sum {D : Ports} {p f : ℕ} {S : HigherOp D p f} (hdet : Deterministic D S)
    {Mt : Op (Fin D.m × Fin D.d)} {Nt : Op (Fin D.n × Fin D.e)} (hM : Mt.PosSemidef)
    (hM1 : ptraceOut Mt = 1) (hN : Nt.PosSemidef) (hN1 : ptraceOut Nt = 1) (x x' : Fin (p + 1)) :
    ∑ z, ∑ l, ∑ l', S ((x, l), z) ((x', l'), z) * (Mt l'.1 l.1 * Nt l'.2 l.2) =
      if x = x' then 1 else 0 := by
  have hL := (hdet.2 0 0 0 0 (trivialExtA D Mtᵀ) (trivialExtB D Ntᵀ)
    (channelChoi_trivialExtA hM hM1) (channelChoi_trivialExtB hN hN1)).2
  have h := congrFun (congrFun hL (x, (0, 0))) (x', (0, 0))
  rw [ptraceOut_apply, sum_linkOut, one_apply_linkIn] at h
  rw [← h]
  refine Finset.sum_congr rfl fun z _ => ?_
  rw [link_apply]
  refine Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun l' _ => ?_
  show _ = S ((x, l), z) ((x', l'), z) * Mt l'.1 l.1 * Nt l'.2 l.2
  ring

/-- The block `∑_z S_{(x,l,z),(x',l',z)}` of a process with global past and future. -/
def blockS {D : Ports} {p f : ℕ} (S : HigherOp D p f) (x x' : Fin (p + 1)) : PMat D :=
  fun l l' => ∑ z, S ((x, l), z) ((x', l'), z)

theorem blockS_apply {D : Ports} {p f : ℕ} (S : HigherOp D p f) (x x' : Fin (p + 1))
    (l l' : LabIndex D) : blockS S x x' l l' = ∑ z, S ((x, l), z) ((x', l'), z) :=
  rfl

theorem trace_blockS {D : Ports} {p f : ℕ} {S : HigherOp D p f} (hdet : Deterministic D S)
    {Mt : Op (Fin D.m × Fin D.d)} {Nt : Op (Fin D.n × Fin D.e)} (hM : Mt.PosSemidef)
    (hM1 : ptraceOut Mt = 1) (hN : Nt.PosSemidef) (hN1 : ptraceOut Nt = 1) (x x' : Fin (p + 1)) :
    (blockS S x x' * (Mt ⊗ₖ Nt)).trace = if x = x' then 1 else 0 := by
  rw [← link_trivial_sum hdet hM hM1 hN hN1 x x']
  show ∑ l, ∑ l', (∑ z, S ((x, l), z) ((x', l'), z)) * (Mt l'.1 l.1 * Nt l'.2 l.2) = _
  exact sum_sum_sum_mul_comm _ _

/-! ### Contractions of the input factors -/

section Contraction

variable {D : Ports}

/-- Contraction of the input factors `A_I B_I` of an operator with `Q`; the output indices
`y = (o, t)` (row) and `y'` (column) are kept. -/
def contr (Q : Op (Fin D.m × Fin D.n)) (T : PMat D) (y' y : Fin D.d × Fin D.e) : ℂ :=
  ∑ q : (Fin D.m × Fin D.n) × (Fin D.m × Fin D.n),
    Q q.2 q.1 * T ((q.1.1, y.1), (q.1.2, y.2)) ((q.2.1, y'.1), (q.2.2, y'.2))

theorem contr_add (Q : Op (Fin D.m × Fin D.n)) (T₁ T₂ : PMat D) (y' y : Fin D.d × Fin D.e) :
    contr Q (T₁ + T₂) y' y = contr Q T₁ y' y + contr Q T₂ y' y := by
  simp only [contr, Matrix.add_apply, mul_add, Finset.sum_add_distrib]

theorem contr_sub (Q : Op (Fin D.m × Fin D.n)) (T₁ T₂ : PMat D) (y' y : Fin D.d × Fin D.e) :
    contr Q (T₁ - T₂) y' y = contr Q T₁ y' y - contr Q T₂ y' y := by
  simp only [contr, Matrix.sub_apply, mul_sub, Finset.sum_sub_distrib]

theorem contr_zero (Q : Op (Fin D.m × Fin D.n)) (y' y : Fin D.d × Fin D.e) :
    contr Q (0 : PMat D) y' y = 0 := by
  simp only [contr, Matrix.zero_apply, mul_zero, Finset.sum_const_zero]

theorem contr_R_AO (Q : Op (Fin D.m × Fin D.n)) (T : PMat D) (o o' : Fin D.d) (t t' : Fin D.e) :
    contr Q (R_AO T) (o', t') (o, t) =
      if o = o' then invCard (Fin D.d) * ∑ z, contr Q T (z, t') (z, t) else 0 := by
  unfold contr
  simp only [R_AO_apply]
  by_cases h : o = o'
  · simp only [if_pos h]
    exact sum_mul_const_mul_sum _ _ _
  · simp only [if_neg h, mul_zero, Finset.sum_const_zero]

theorem contr_R_BO (Q : Op (Fin D.m × Fin D.n)) (T : PMat D) (o o' : Fin D.d) (t t' : Fin D.e) :
    contr Q (R_BO T) (o', t') (o, t) =
      if t = t' then invCard (Fin D.e) * ∑ z, contr Q T (o', z) (o, z) else 0 := by
  unfold contr
  simp only [R_BO_apply]
  by_cases h : t = t'
  · simp only [if_pos h]
    exact sum_mul_const_mul_sum _ _ _
  · simp only [if_neg h, mul_zero, Finset.sum_const_zero]

theorem contr_kron_one (X : Op (Fin D.m)) (T : PMat D) (y' y : Fin D.d × Fin D.e) :
    contr (X ⊗ₖ (1 : Op (Fin D.n))) T y' y =
      ∑ a, ∑ a', X a' a * ∑ b, T ((a, y.1), (b, y.2)) ((a', y'.1), (b, y'.2)) := by
  have hq : ∀ k k' : Fin D.m × Fin D.n,
      (X ⊗ₖ (1 : Op (Fin D.n))) k' k * T ((k.1, y.1), (k.2, y.2)) ((k'.1, y'.1), (k'.2, y'.2)) =
        if k'.2 = k.2 then X k'.1 k.1 * T ((k.1, y.1), (k.2, y.2)) ((k'.1, y'.1), (k.2, y'.2))
        else 0 := by
    intro k k'
    rw [Matrix.kroneckerMap_apply, Matrix.one_apply]
    split_ifs with h
    · rw [h, mul_one]
    · rw [mul_zero, zero_mul]
  calc contr (X ⊗ₖ (1 : Op (Fin D.n))) T y' y
      = ∑ k : Fin D.m × Fin D.n, ∑ k' : Fin D.m × Fin D.n, (X ⊗ₖ (1 : Op (Fin D.n))) k' k *
          T ((k.1, y.1), (k.2, y.2)) ((k'.1, y'.1), (k'.2, y'.2)) := by
        unfold contr
        simp only [Fintype.sum_prod_type]
    _ = ∑ k : Fin D.m × Fin D.n, ∑ k' : Fin D.m × Fin D.n, (if k'.2 = k.2 then
          X k'.1 k.1 * T ((k.1, y.1), (k.2, y.2)) ((k'.1, y'.1), (k.2, y'.2)) else 0) := by
        simp only [hq]
    _ = ∑ k : Fin D.m × Fin D.n,
          ∑ a', X a' k.1 * T ((k.1, y.1), (k.2, y.2)) ((a', y'.1), (k.2, y'.2)) := by
        refine Finset.sum_congr rfl fun k _ => ?_
        rw [Fintype.sum_prod_type]
        refine Finset.sum_congr rfl fun a' _ => ?_
        rw [Finset.sum_eq_single k.2]
        · simp
        · intro b' _ hb'
          simp [hb']
        · intro h
          exact absurd (Finset.mem_univ _) h
    _ = ∑ a, ∑ b, ∑ a', X a' a * T ((a, y.1), (b, y.2)) ((a', y'.1), (b, y'.2)) := by
        simp only [Fintype.sum_prod_type]
    _ = ∑ a, ∑ a', ∑ b, X a' a * T ((a, y.1), (b, y.2)) ((a', y'.1), (b, y'.2)) :=
        Finset.sum_congr rfl fun a _ => Finset.sum_comm
    _ = ∑ a, ∑ a', X a' a * ∑ b, T ((a, y.1), (b, y.2)) ((a', y'.1), (b, y'.2)) := by
        refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun a' _ => ?_
        rw [Finset.mul_sum]

theorem contr_one_kron (Y : Op (Fin D.n)) (T : PMat D) (y' y : Fin D.d × Fin D.e) :
    contr ((1 : Op (Fin D.m)) ⊗ₖ Y) T y' y =
      ∑ b, ∑ b', Y b' b * ∑ a, T ((a, y.1), (b, y.2)) ((a, y'.1), (b', y'.2)) := by
  have hq : ∀ k k' : Fin D.m × Fin D.n,
      ((1 : Op (Fin D.m)) ⊗ₖ Y) k' k * T ((k.1, y.1), (k.2, y.2)) ((k'.1, y'.1), (k'.2, y'.2)) =
        if k'.1 = k.1 then Y k'.2 k.2 * T ((k.1, y.1), (k.2, y.2)) ((k.1, y'.1), (k'.2, y'.2))
        else 0 := by
    intro k k'
    rw [Matrix.kroneckerMap_apply, Matrix.one_apply]
    split_ifs with h
    · rw [h, one_mul]
    · rw [zero_mul, zero_mul]
  calc contr ((1 : Op (Fin D.m)) ⊗ₖ Y) T y' y
      = ∑ k : Fin D.m × Fin D.n, ∑ k' : Fin D.m × Fin D.n, ((1 : Op (Fin D.m)) ⊗ₖ Y) k' k *
          T ((k.1, y.1), (k.2, y.2)) ((k'.1, y'.1), (k'.2, y'.2)) := by
        unfold contr
        simp only [Fintype.sum_prod_type]
    _ = ∑ k : Fin D.m × Fin D.n, ∑ k' : Fin D.m × Fin D.n, (if k'.1 = k.1 then
          Y k'.2 k.2 * T ((k.1, y.1), (k.2, y.2)) ((k.1, y'.1), (k'.2, y'.2)) else 0) := by
        simp only [hq]
    _ = ∑ k : Fin D.m × Fin D.n,
          ∑ b', Y b' k.2 * T ((k.1, y.1), (k.2, y.2)) ((k.1, y'.1), (b', y'.2)) := by
        refine Finset.sum_congr rfl fun k _ => ?_
        rw [Fintype.sum_prod_type, Finset.sum_eq_single k.1]
        · simp
        · intro a' _ ha'
          simp [ha']
        · intro h
          exact absurd (Finset.mem_univ _) h
    _ = ∑ a, ∑ b, ∑ b', Y b' b * T ((a, y.1), (b, y.2)) ((a, y'.1), (b', y'.2)) := by
        simp only [Fintype.sum_prod_type]
    _ = ∑ b, ∑ a, ∑ b', Y b' b * T ((a, y.1), (b, y.2)) ((a, y'.1), (b', y'.2)) :=
        Finset.sum_comm
    _ = ∑ b, ∑ b', ∑ a, Y b' b * T ((a, y.1), (b, y.2)) ((a, y'.1), (b', y'.2)) :=
        Finset.sum_congr rfl fun b _ => Finset.sum_comm
    _ = ∑ b, ∑ b', Y b' b * ∑ a, T ((a, y.1), (b, y.2)) ((a, y'.1), (b', y'.2)) := by
        refine Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun b' _ => ?_
        rw [Finset.mul_sum]

/-- `Tr_{B_I B_O}` of an operator, contracted with `X` on `A_I`. -/
def trBO (X : Op (Fin D.m)) (T : PMat D) (o' o : Fin D.d) : ℂ :=
  ∑ a : Fin D.m, ∑ a' : Fin D.m, X a' a *
    ∑ b : Fin D.n, ∑ t : Fin D.e, T ((a, o), (b, t)) ((a', o'), (b, t))

theorem sum_contr_kron_one (X : Op (Fin D.m)) (T : PMat D) (o' o : Fin D.d) :
    ∑ t'', contr (X ⊗ₖ (1 : Op (Fin D.n))) T (o', t'') (o, t'') = trBO X T o' o := by
  simp only [contr_kron_one]
  unfold trBO
  calc ∑ t'', ∑ a, ∑ a', X a' a * ∑ b, T ((a, o), (b, t'')) ((a', o'), (b, t''))
      = ∑ a, ∑ t'', ∑ a', X a' a * ∑ b, T ((a, o), (b, t'')) ((a', o'), (b, t'')) :=
        Finset.sum_comm
    _ = ∑ a, ∑ a', ∑ t'', X a' a * ∑ b, T ((a, o), (b, t'')) ((a', o'), (b, t'')) :=
        Finset.sum_congr rfl fun a _ => Finset.sum_comm
    _ = ∑ a, ∑ a', X a' a * ∑ t'', ∑ b, T ((a, o), (b, t'')) ((a', o'), (b, t'')) := by
        refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun a' _ => ?_
        rw [Finset.mul_sum]
    _ = ∑ a, ∑ a', X a' a * ∑ b, ∑ t'', T ((a, o), (b, t'')) ((a', o'), (b, t'')) := by
        refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun a' _ => ?_
        rw [Finset.sum_comm]

/-- `eq:LV-a` for the contraction `trBO`. -/
theorem trBO_lv_a {T : PMat D} (hLVa : R_BIBO T - R_AO (R_BIBO T) = 0) (X : Op (Fin D.m))
    (o o' : Fin D.d) :
    trBO X T o' o = if o = o' then invCard (Fin D.d) * ∑ z, trBO X T z z else 0 := by
  have h1 : trBO X T o' o = ∑ a, ∑ a', X a' a *
      (if o = o' then ((D.d : ℂ))⁻¹ * ∑ u, ∑ b, ∑ t, T ((a, u), (b, t)) ((a', u), (b, t))
        else 0) := by
    unfold trBO
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun a' _ => ?_
    rw [LVa_entry D hLVa a a' o o']
  have hc : invCard (Fin D.d) = ((D.d : ℂ))⁻¹ := by rw [invCard, Fintype.card_fin]
  rw [h1, hc]
  by_cases h : o = o'
  · simp only [if_pos h]
    exact sum_sum_mul_const_mul_sum _ _ _
  · simp only [if_neg h, mul_zero, Finset.sum_const_zero]

/-- `Tr_{A_I A_O}` of an operator, contracted with `Y` on `B_I`. -/
def trAO (Y : Op (Fin D.n)) (T : PMat D) (t' t : Fin D.e) : ℂ :=
  ∑ b : Fin D.n, ∑ b' : Fin D.n, Y b' b *
    ∑ a : Fin D.m, ∑ o : Fin D.d, T ((a, o), (b, t)) ((a, o), (b', t'))

theorem sum_contr_one_kron (Y : Op (Fin D.n)) (T : PMat D) (t' t : Fin D.e) :
    ∑ o'', contr ((1 : Op (Fin D.m)) ⊗ₖ Y) T (o'', t') (o'', t) = trAO Y T t' t := by
  simp only [contr_one_kron]
  unfold trAO
  calc ∑ o'', ∑ b, ∑ b', Y b' b * ∑ a, T ((a, o''), (b, t)) ((a, o''), (b', t'))
      = ∑ b, ∑ o'', ∑ b', Y b' b * ∑ a, T ((a, o''), (b, t)) ((a, o''), (b', t')) :=
        Finset.sum_comm
    _ = ∑ b, ∑ b', ∑ o'', Y b' b * ∑ a, T ((a, o''), (b, t)) ((a, o''), (b', t')) :=
        Finset.sum_congr rfl fun b _ => Finset.sum_comm
    _ = ∑ b, ∑ b', Y b' b * ∑ o'', ∑ a, T ((a, o''), (b, t)) ((a, o''), (b', t')) := by
        refine Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun b' _ => ?_
        rw [Finset.mul_sum]
    _ = ∑ b, ∑ b', Y b' b * ∑ a, ∑ o, T ((a, o), (b, t)) ((a, o), (b', t')) := by
        refine Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun b' _ => ?_
        rw [Finset.sum_comm]

/-- `eq:LV-b` for the contraction `trAO`. -/
theorem trAO_lv_b {T : PMat D} (hLVb : R_AIAO T - R_BO (R_AIAO T) = 0) (Y : Op (Fin D.n))
    (t t' : Fin D.e) :
    trAO Y T t' t = if t = t' then invCard (Fin D.e) * ∑ z, trAO Y T z z else 0 := by
  have h1 : trAO Y T t' t = ∑ b, ∑ b', Y b' b *
      (if t = t' then ((D.e : ℂ))⁻¹ * ∑ z, ∑ a, ∑ o, T ((a, o), (b, z)) ((a, o), (b', z))
        else 0) := by
    unfold trAO
    refine Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun b' _ => ?_
    rw [LVb_entry D hLVb b b' t t', sum3_rotate]
  have hc : invCard (Fin D.e) = ((D.e : ℂ))⁻¹ := by rw [invCard, Fintype.card_fin]
  rw [h1, hc]
  by_cases h : t = t'
  · simp only [if_pos h]
    exact sum_sum_mul_const_mul_sum _ _ _
  · simp only [if_neg h, mul_zero, Finset.sum_const_zero]

end Contraction

end Family

open Family

/-! ### The family `W_τ` (Step 2) -/

section Process

variable {D : Ports} {p f : ℕ}
  (U : Matrix (Fin (f + 1) × (Fin D.m × Fin D.n)) (Fin (p + 1) × (Fin D.d × Fin D.e)) ℂ)

theorem procV_apply (u v : Fin (p + 1) → ℂ) (l l' : LabIndex D) :
    procV U u v l l' = ∑ z, (∑ x, U (z, (l.1.1, l.2.1)) (x, (l.1.2, l.2.2)) * u x) *
      star (∑ x', U (z, (l'.1.1, l'.2.1)) (x', (l'.1.2, l'.2.2)) * v x') :=
  rfl

/-- The Gram factor of `procV U v v`. -/
def psiV (v : Fin (p + 1) → ℂ) : Matrix (LabIndex D) (Fin (f + 1)) ℂ :=
  Matrix.of fun l z => ∑ x, U (z, (l.1.1, l.2.1)) (x, (l.1.2, l.2.2)) * v x

theorem procV_posSemidef (v : Fin (p + 1) → ℂ) : (procV U v v).PosSemidef := by
  have h : procV U v v = psiV U v * (psiV U v)ᴴ := by
    ext l l'
    simp only [procV_apply, psiV, Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.of_apply]
  rw [h]
  exact Matrix.posSemidef_self_mul_conjTranspose _

theorem procV_add_add (u₁ u₂ v₁ v₂ : Fin (p + 1) → ℂ) :
    procV U (u₁ + u₂) (v₁ + v₂) =
      procV U u₁ v₁ + procV U u₁ v₂ + procV U u₂ v₁ + procV U u₂ v₂ := by
  ext l l'
  simp only [procV_apply, Matrix.add_apply, Pi.add_apply, mul_add, Finset.sum_add_distrib,
    star_add, add_mul]
  ring

theorem procV_entry (u v : Fin (p + 1) → ℂ) (i i' : Fin D.m) (o o' : Fin D.d) (j j' : Fin D.n)
    (t t' : Fin D.e) :
    procV U u v ((i, o), (j, t)) ((i', o'), (j', t')) =
      ∑ x, ∑ x', star (v x') *
        heis U (unitMat i' i ⊗ₖ unitMat j' j) (x', (o', t')) (x, (o, t)) * u x := by
  rw [unitMat_kronecker]
  simp only [heis_unitMat_apply]
  rw [procV_apply]
  exact (sum_sandwich (fun z x => U (z, (i, j)) (x, (o, t)))
    (fun z x' => U (z, (i', j')) (x', (o', t'))) u v).symm

theorem reducePastFuture_eq_procV {S : HigherOp D p f}
    (hS : ∀ (x x' : Fin (p + 1)) (z z' : Fin (f + 1)) (l l' : LabIndex D),
      S ((x, l), z) ((x', l'), z') =
        U (z, (l.1.1, l.2.1)) (x, (l.1.2, l.2.2)) *
          star (U (z', (l'.1.1, l'.2.1)) (x', (l'.1.2, l'.2.2)))) :
    reducePastFuture D S = procV U (Pi.single 0 1) (Pi.single 0 1) := by
  ext l l'
  rw [reducePastFuture_apply, procV_apply]
  refine Finset.sum_congr rfl fun z _ => ?_
  rw [hS, sum_mul_piSingle_one, sum_mul_piSingle_one]

theorem procV_eq_sum_smul {S : HigherOp D p f}
    (hS : ∀ (x x' : Fin (p + 1)) (z z' : Fin (f + 1)) (l l' : LabIndex D),
      S ((x, l), z) ((x', l'), z') =
        U (z, (l.1.1, l.2.1)) (x, (l.1.2, l.2.2)) *
          star (U (z', (l'.1.1, l'.2.1)) (x', (l'.1.2, l'.2.2))))
    (u v : Fin (p + 1) → ℂ) :
    procV U u v = ∑ x, ∑ x', (u x * star (v x')) • blockS S x x' := by
  ext l l'
  rw [procV_apply, ← sum_sandwich]
  simp only [Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul, blockS_apply]
  refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun x' _ => ?_
  have hz : ∑ z, S ((x, l), z) ((x', l'), z) =
      ∑ z, star (U (z, (l'.1.1, l'.2.1)) (x', (l'.1.2, l'.2.2))) *
        U (z, (l.1.1, l.2.1)) (x, (l.1.2, l.2.2)) := by
    refine Finset.sum_congr rfl fun z _ => ?_
    rw [hS, mul_comm]
  rw [hz]
  ring

/-- Step 2: `W_τ` maps every pair of channels to `Tr τ`. -/
theorem procV_normalization {S : HigherOp D p f}
    (hS : ∀ (x x' : Fin (p + 1)) (z z' : Fin (f + 1)) (l l' : LabIndex D),
      S ((x, l), z) ((x', l'), z') =
        U (z, (l.1.1, l.2.1)) (x, (l.1.2, l.2.2)) *
          star (U (z', (l'.1.1, l'.2.1)) (x', (l'.1.2, l'.2.2))))
    (hdet : Deterministic D S) (u v : Fin (p + 1) → ℂ) (Mt : Op (Fin D.m × Fin D.d))
    (Nt : Op (Fin D.n × Fin D.e)) (hM : Mt.PosSemidef) (hM1 : ptraceOut Mt = 1)
    (hN : Nt.PosSemidef) (hN1 : ptraceOut Nt = 1) :
    (procV U u v * (Mt ⊗ₖ Nt)).trace = ∑ x, u x * star (v x) := by
  rw [procV_eq_sum_smul U hS]
  simp only [Finset.sum_mul, Matrix.trace_sum, Matrix.smul_mul, Matrix.trace_smul, smul_eq_mul]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [Finset.sum_eq_single x]
  · rw [trace_blockS hdet hM hM1 hN hN1, if_pos rfl, mul_one]
  · intro x' _ hx'
    rw [trace_blockS hdet hM hM1 hN hN1, if_neg (Ne.symm hx'), mul_zero]
  · intro h
    exact absurd (Finset.mem_univ _) h

/-- Step 2: every `W_τ` satisfies `eq:LV` (converse of Lemma 2.3). -/
theorem procV_lvEquations {S : HigherOp D p f}
    (hS : ∀ (x x' : Fin (p + 1)) (z z' : Fin (f + 1)) (l l' : LabIndex D),
      S ((x, l), z) ((x', l'), z') =
        U (z, (l.1.1, l.2.1)) (x, (l.1.2, l.2.2)) *
          star (U (z', (l'.1.1, l'.2.1)) (x', (l'.1.2, l'.2.2))))
    (hdet : Deterministic D S) (u v : Fin (p + 1) → ℂ) : LVEquations (procV U u v) :=
  (lvEquations_of_channel_normalization (procV U u v) (∑ x, u x * star (v x))
    fun Mt Nt hM hM1 hN hN1 => procV_normalization U hS hdet u v Mt Nt hM hM1 hN hN1).1

/-! ### What `eq:LV` says about `Φ†` (Step 3) -/

theorem procV_single_apply (x x' : Fin (p + 1)) (k k' : Fin D.m × Fin D.n)
    (y y' : Fin D.d × Fin D.e) :
    procV U (Pi.single x 1) (Pi.single x' 1) ((k.1, y.1), (k.2, y.2))
        ((k'.1, y'.1), (k'.2, y'.2)) =
      heis U (unitMat k' k) (x', y') (x, y) := by
  rw [heis_unitMat_apply]
  show (∑ z, (∑ x₁, U (z, k) (x₁, y) * (Pi.single x (1 : ℂ) : Fin (p + 1) → ℂ) x₁) *
      star (∑ x₁, U (z, k') (x₁, y') * (Pi.single x' (1 : ℂ) : Fin (p + 1) → ℂ) x₁)) = _
  refine Finset.sum_congr rfl fun z _ => ?_
  rw [sum_mul_piSingle_one, sum_mul_piSingle_one, mul_comm]

theorem heis_eq_contr (Q : Op (Fin D.m × Fin D.n)) (x x' : Fin (p + 1))
    (y y' : Fin D.d × Fin D.e) :
    heis U Q (x', y') (x, y) = contr Q (procV U (Pi.single x 1) (Pi.single x' 1)) y' y := by
  rw [heis_eq_sum_unitMat]
  unfold contr
  refine Finset.sum_congr rfl fun q _ => ?_
  rw [procV_single_apply]

/-- `eq:LV-c` for `Φ†(Q)`. -/
theorem heis_lv_c {S : HigherOp D p f}
    (hS : ∀ (x x' : Fin (p + 1)) (z z' : Fin (f + 1)) (l l' : LabIndex D),
      S ((x, l), z) ((x', l'), z') =
        U (z, (l.1.1, l.2.1)) (x, (l.1.2, l.2.2)) *
          star (U (z', (l'.1.1, l'.2.1)) (x', (l'.1.2, l'.2.2))))
    (hdet : Deterministic D S)
    (Q : Op (Fin D.m × Fin D.n)) (x' x : Fin (p + 1)) (o' o : Fin D.d) (t' t : Fin D.e) :
    heis U Q (x', (o', t')) (x, (o, t))
      - (if o = o' then invCard (Fin D.d) * ∑ o'', heis U Q (x', (o'', t')) (x, (o'', t)) else 0)
      - (if t = t' then invCard (Fin D.e) * ∑ t'', heis U Q (x', (o', t'')) (x, (o, t'')) else 0)
      + (if o = o' then invCard (Fin D.d) * ∑ o'', (if t = t' then invCard (Fin D.e) *
            ∑ t'', heis U Q (x', (o'', t'')) (x, (o'', t'')) else 0) else 0) = 0 := by
  have hc := (procV_lvEquations U hS hdet (Pi.single x 1) (Pi.single x' 1)).2.2
  have h0 := congrArg (fun T => contr Q T (o', t') (o, t)) hc
  simp only [contr_add, contr_sub, contr_zero, contr_R_AO, contr_R_BO] at h0
  simp only [heis_eq_contr U Q x x']
  exact h0

theorem heis_trace_A {S : HigherOp D p f}
    (hS : ∀ (x x' : Fin (p + 1)) (z z' : Fin (f + 1)) (l l' : LabIndex D),
      S ((x, l), z) ((x', l'), z') =
        U (z, (l.1.1, l.2.1)) (x, (l.1.2, l.2.2)) *
          star (U (z', (l'.1.1, l'.2.1)) (x', (l'.1.2, l'.2.2))))
    (hdet : Deterministic D S) (X : Op (Fin D.m)) (x' x : Fin (p + 1)) (o' o : Fin D.d) :
    ∑ t'', heis U (X ⊗ₖ (1 : Op (Fin D.n))) (x', (o', t'')) (x, (o, t'')) =
      if o = o' then invCard (Fin D.d) *
        ∑ o'', ∑ t'', heis U (X ⊗ₖ (1 : Op (Fin D.n))) (x', (o'', t'')) (x, (o'', t''))
      else 0 := by
  have hLVa := (procV_lvEquations U hS hdet (Pi.single x 1) (Pi.single x' 1)).1
  simp only [heis_eq_contr U _ x x', sum_contr_kron_one]
  exact trBO_lv_a hLVa X o o'

theorem heis_trace_B {S : HigherOp D p f}
    (hS : ∀ (x x' : Fin (p + 1)) (z z' : Fin (f + 1)) (l l' : LabIndex D),
      S ((x, l), z) ((x', l'), z') =
        U (z, (l.1.1, l.2.1)) (x, (l.1.2, l.2.2)) *
          star (U (z', (l'.1.1, l'.2.1)) (x', (l'.1.2, l'.2.2))))
    (hdet : Deterministic D S) (Y : Op (Fin D.n)) (x' x : Fin (p + 1)) (t' t : Fin D.e) :
    ∑ o'', heis U ((1 : Op (Fin D.m)) ⊗ₖ Y) (x', (o'', t')) (x, (o'', t)) =
      if t = t' then invCard (Fin D.e) *
        ∑ t'', ∑ o'', heis U ((1 : Op (Fin D.m)) ⊗ₖ Y) (x', (o'', t'')) (x, (o'', t''))
      else 0 := by
  have hLVb := (procV_lvEquations U hS hdet (Pi.single x 1) (Pi.single x' 1)).2.1
  simp only [heis_eq_contr U _ x x', sum_contr_one_kron]
  exact trAO_lv_b hLVb Y t t'

/-- `eq:no-self`, Alice: `Φ†(X ⊗ 1)` acts as the identity on `A_O`. -/
theorem heis_no_self_A {S : HigherOp D p f}
    (hS : ∀ (x x' : Fin (p + 1)) (z z' : Fin (f + 1)) (l l' : LabIndex D),
      S ((x, l), z) ((x', l'), z') =
        U (z, (l.1.1, l.2.1)) (x, (l.1.2, l.2.2)) *
          star (U (z', (l'.1.1, l'.2.1)) (x', (l'.1.2, l'.2.2))))
    (hdet : Deterministic D S)
    (X : Op (Fin D.m)) (x' x : Fin (p + 1)) (o' o : Fin D.d) (t' t : Fin D.e) :
    heis U (X ⊗ₖ (1 : Op (Fin D.n))) (x', (o', t')) (x, (o, t)) =
      if o = o' then invCard (Fin D.d) *
        ∑ o'', heis U (X ⊗ₖ (1 : Op (Fin D.n))) (x', (o'', t')) (x, (o'', t)) else 0 := by
  have hc := heis_lv_c U hS hdet (X ⊗ₖ (1 : Op (Fin D.n))) x' x o' o t' t
  have ha := heis_trace_A U hS hdet X x' x o' o
  have hsum : ∑ o'', invCard (Fin D.e) *
        ∑ t'', heis U (X ⊗ₖ (1 : Op (Fin D.n))) (x', (o'', t'')) (x, (o'', t'')) =
      invCard (Fin D.e) *
        ∑ o'', ∑ t'', heis U (X ⊗ₖ (1 : Op (Fin D.n))) (x', (o'', t'')) (x, (o'', t'')) := by
    rw [Finset.mul_sum]
  by_cases ho : o = o' <;> by_cases ht : t = t'
  · simp only [if_pos ho, if_pos ht] at hc ha ⊢
    linear_combination hc + invCard (Fin D.e) * ha - invCard (Fin D.d) * hsum
  · simp only [if_pos ho, if_neg ht, Finset.sum_const_zero, mul_zero] at hc ⊢
    linear_combination hc
  · simp only [if_neg ho, if_pos ht] at hc ha ⊢
    linear_combination hc + invCard (Fin D.e) * ha
  · simp only [if_neg ho, if_neg ht] at hc ⊢
    linear_combination hc

/-- `eq:no-self`, Bob: `Φ†(1 ⊗ Y)` acts as the identity on `B_O`. -/
theorem heis_no_self_B {S : HigherOp D p f}
    (hS : ∀ (x x' : Fin (p + 1)) (z z' : Fin (f + 1)) (l l' : LabIndex D),
      S ((x, l), z) ((x', l'), z') =
        U (z, (l.1.1, l.2.1)) (x, (l.1.2, l.2.2)) *
          star (U (z', (l'.1.1, l'.2.1)) (x', (l'.1.2, l'.2.2))))
    (hdet : Deterministic D S)
    (Y : Op (Fin D.n)) (x' x : Fin (p + 1)) (o' o : Fin D.d) (t' t : Fin D.e) :
    heis U ((1 : Op (Fin D.m)) ⊗ₖ Y) (x', (o', t')) (x, (o, t)) =
      if t = t' then invCard (Fin D.e) *
        ∑ t'', heis U ((1 : Op (Fin D.m)) ⊗ₖ Y) (x', (o', t'')) (x, (o, t'')) else 0 := by
  have hc := heis_lv_c U hS hdet ((1 : Op (Fin D.m)) ⊗ₖ Y) x' x o' o t' t
  have hb := heis_trace_B U hS hdet Y x' x t' t
  have hsum : ∑ o'', invCard (Fin D.e) *
        ∑ t'', heis U ((1 : Op (Fin D.m)) ⊗ₖ Y) (x', (o'', t'')) (x, (o'', t'')) =
      invCard (Fin D.e) *
        ∑ t'', ∑ o'', heis U ((1 : Op (Fin D.m)) ⊗ₖ Y) (x', (o'', t'')) (x, (o'', t'')) := by
    rw [← Finset.mul_sum, Finset.sum_comm]
  by_cases ho : o = o' <;> by_cases ht : t = t'
  · simp only [if_pos ho, if_pos ht] at hc hb ⊢
    linear_combination hc + invCard (Fin D.d) * hb - invCard (Fin D.d) * hsum
  · simp only [if_pos ho, if_neg ht, Finset.sum_const_zero, mul_zero] at hc hb ⊢
    linear_combination hc + invCard (Fin D.d) * hb
  · simp only [if_neg ho, if_pos ht] at hc ⊢
    linear_combination hc
  · simp only [if_neg ho, if_neg ht] at hc ⊢
    linear_combination hc

end Process

end

end CausalNonpurifiability
