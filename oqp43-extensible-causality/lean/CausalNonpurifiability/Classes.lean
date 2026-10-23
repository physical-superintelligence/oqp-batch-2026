module

public import CausalNonpurifiability.Definitions.Separability
public import CausalNonpurifiability.Definitions.CausalProcess
public import CausalNonpurifiability.Definitions.ExtensibleGeneral

@[expose] public section


/-!
# `CausalNonpurifiability.Classes`

Causally separable processes are extensibly causal ("a single
decomposition of `W` into an operator in `O_{A≺B}` and an operator in `O_{B≺A}` gives the
decomposition `eq:causal-definition` in all experiments").

For `W = q W_A + (1 - q) W_B` (Definition 2.4, `causallySeparable_iff_convex`) and any
experiment, the distribution of `W` is `q p_A + (1 - q) p_B` with the distributions `p_A`, `p_B`
of `W_A`, `W_B` (`bornExtended_convex`); `p_A` does not let Bob signal to Alice because
`W_A ∈ O_{A≺B}` (`bornExtended_NS_AB`, from `ordered_completed_pairing`), and symmetrically for
`p_B` (`bornExtended_NS_BA`).

Extensibly causal processes are causal (`causalProcess_of_extensiblyCausal`): an
experiment without additional systems is the experiment with one-dimensional additional systems
(`Instrument.unitExt`, `bornExtended_unitExt`).
-/

set_option autoImplicit false

open Matrix
open scoped ComplexOrder Kronecker

namespace CausalNonpurifiability

noncomputable section

variable {D : Ports} {RA RB X Y A B : Type} [Fintype RA] [DecidableEq RA] [Fintype RB]
  [DecidableEq RB] [Fintype A] [Fintype B]

theorem kronecker_sum_right {I J κ : Type} [Fintype κ] (M : Op I) (N : κ → Op J) :
    M ⊗ₖ (∑ b, N b) = ∑ b, M ⊗ₖ N b := by
  ext u v
  simp only [Matrix.kroneckerMap_apply, Matrix.sum_apply, Finset.mul_sum]

theorem kronecker_sum_left {I J ι : Type} [Fintype ι] (M : ι → Op I) (N : Op J) :
    (∑ a, M a) ⊗ₖ N = ∑ a, M a ⊗ₖ N := by
  ext u v
  simp only [Matrix.kroneckerMap_apply, Matrix.sum_apply, Finset.sum_mul]

theorem bornExtended_sum_b (W : PMat D) (σ : Op (RA × RB))
    (M : Instrument (Fin D.m × RA) (Fin D.d) X A) (N : Instrument (Fin D.n × RB) (Fin D.e) Y B)
    (x : X) (y : Y) (a : A) :
    ∑ b, bornExtended D W σ M N x y a b =
      ((extendInput D W σ * (M.elem x a ⊗ₖ ∑ b, N.elem y b)).trace).re := by
  simp only [bornExtended]
  rw [kronecker_sum_right, Matrix.mul_sum, Matrix.trace_sum, Complex.re_sum]

theorem bornExtended_sum_a (W : PMat D) (σ : Op (RA × RB))
    (M : Instrument (Fin D.m × RA) (Fin D.d) X A) (N : Instrument (Fin D.n × RB) (Fin D.e) Y B)
    (x : X) (y : Y) (b : B) :
    ∑ a, bornExtended D W σ M N x y a b =
      ((extendInput D W σ * ((∑ a, M.elem x a) ⊗ₖ N.elem y b)).trace).re := by
  simp only [bornExtended]
  rw [kronecker_sum_left, Matrix.mul_sum, Matrix.trace_sum, Complex.re_sum]

/-- In every experiment, a process of order `A ≺ B` lets no signal pass from Bob to Alice. -/
theorem bornExtended_NS_AB {WA : PMat D} (hA : OrderedAB D WA) (σ : Op (RA × RB))
    (M : Instrument (Fin D.m × RA) (Fin D.d) X A) (N : Instrument (Fin D.n × RB) (Fin D.e) Y B) :
    NS_AB (bornExtended D WA σ M N) := by
  intro x y y' a
  rw [bornExtended_sum_b, bornExtended_sum_b, extendInput_eq_extended,
    ordered_completed_pairing D hA σ _ _ (N.normalized y),
    ordered_completed_pairing D hA σ _ _ (N.normalized y')]

/-- In every experiment, a process of order `B ≺ A` lets no signal pass from Alice to Bob. -/
theorem bornExtended_NS_BA {WB : PMat D} (hB : OrderedBA D WB) (σ : Op (RA × RB))
    (M : Instrument (Fin D.m × RA) (Fin D.d) X A) (N : Instrument (Fin D.n × RB) (Fin D.e) Y B) :
    NS_BA (bornExtended D WB σ M N) := by
  intro x x' y b
  rw [bornExtended_sum_a, bornExtended_sum_a, extendInput_eq_extended,
    ordered_completed_pairing_B D hB σ _ _ (M.normalized x),
    ordered_completed_pairing_B D hB σ _ _ (M.normalized x')]

/-- The distribution of a convex combination of processes is the convex combination of their
distributions. -/
theorem bornExtended_convex (q : ℝ) (WA WB : PMat D) (σ : Op (RA × RB))
    (M : Instrument (Fin D.m × RA) (Fin D.d) X A) (N : Instrument (Fin D.n × RB) (Fin D.e) Y B)
    (x : X) (y : Y) (a : A) (b : B) :
    bornExtended D ((q : ℂ) • WA + ((1 - q : ℝ) : ℂ) • WB) σ M N x y a b =
      q * bornExtended D WA σ M N x y a b + (1 - q) * bornExtended D WB σ M N x y a b := by
  have hlin : extendInput D ((q : ℂ) • WA + ((1 - q : ℝ) : ℂ) • WB) σ =
      (q : ℂ) • extendInput D WA σ + ((1 - q : ℝ) : ℂ) • extendInput D WB σ := by
    ext u v
    simp only [extendInput_eq_extended, extended_apply, Matrix.add_apply, Matrix.smul_apply,
      smul_eq_mul]
    ring
  simp only [bornExtended, hlin, Matrix.add_mul, Matrix.smul_mul, Matrix.trace_add,
    Matrix.trace_smul, smul_eq_mul, Complex.add_re, Complex.re_ofReal_mul]

theorem causal_of_convex {q : ℝ} (hq0 : 0 ≤ q) (hq1 : q ≤ 1) {WA WB : PMat D}
    (hA : Valid D WA) (hAo : OrderedAB D WA) (hB : Valid D WB) (hBo : OrderedBA D WB)
    {σ : Op (RA × RB)} (hσ : Density σ)
    (M : Instrument (Fin D.m × RA) (Fin D.d) X A) (N : Instrument (Fin D.n × RB) (Fin D.e) Y B) :
    Causal (bornExtended D ((q : ℂ) • WA + ((1 - q : ℝ) : ℂ) • WB) σ M N) :=
  ⟨q, bornExtended D WA σ M N, bornExtended D WB σ M N, hq0, hq1,
    valid_born_extended D hA hσ M N, valid_born_extended D hB hσ M N,
    bornExtended_NS_AB hAo σ M N, bornExtended_NS_BA hBo σ M N,
    fun x y a b => bornExtended_convex q WA WB σ M N x y a b⟩

/-- **Causally separable processes are extensibly causal** ([OG, Section 3.5]). -/
theorem extensiblyCausal_of_causallySeparable {W : PMat D} (h : CausallySeparable D W) :
    ExtensiblyCausal D W := by
  have hW : Valid D W := h.1
  obtain ⟨q, WA, WB, hq0, hq1, hA, hAo, hB, hBo, hWq⟩ := (causallySeparable_iff_convex D hW).mp h
  refine ⟨hW, fun r s nx ny na nb σ hσ M N => ?_⟩
  rw [hWq]
  exact causal_of_convex hq0 hq1 hA hAo hB hBo hσ M N

/-- The instrument on `I ⊗ Unit` that ignores a one-dimensional additional system. -/
def Instrument.unitExt {I O X' A' : Type} [Fintype I] [Fintype O] [Fintype A'] [DecidableEq I]
    (M : Instrument I O X' A') : Instrument (I × Unit) O X' A' where
  elem x a := (M.elem x a).submatrix (fun u => (u.1.1, u.2)) (fun u => (u.1.1, u.2))
  positive x a := (M.positive x a).submatrix _
  normalized x := by
    ext ⟨i, ⟨⟩⟩ ⟨j, ⟨⟩⟩
    have h := congrFun (congrFun (M.normalized x) i) j
    simp only [ptraceOut_apply, Matrix.sum_apply, Matrix.submatrix_apply] at h ⊢
    rw [h]
    by_cases hij : i = j
    · subst hij
      simp
    · have hne : ((i, ()) : I × Unit) ≠ (j, ()) := fun hh => hij (congrArg Prod.fst hh)
      rw [Matrix.one_apply_ne hij, Matrix.one_apply_ne hne]

/-- Dropping one-dimensional additional systems from the index of an extended operator. -/
def unitDrop (D : Ports) :
    LabIdx (Fin D.m × Unit) (Fin D.d) (Fin D.n × Unit) (Fin D.e) ≃ LabIndex D where
  toFun u := ((u.1.1.1, u.1.2), (u.2.1.1, u.2.2))
  invFun v := (((v.1.1, ()), v.1.2), ((v.2.1, ()), v.2.2))
  left_inv := fun ⟨⟨⟨_, ⟨⟩⟩, _⟩, ⟨⟨_, ⟨⟩⟩, _⟩⟩ => rfl
  right_inv := fun ⟨⟨_, _⟩, ⟨_, _⟩⟩ => rfl

@[simp] theorem unitDrop_apply (D : Ports)
    (u : LabIdx (Fin D.m × Unit) (Fin D.d) (Fin D.n × Unit) (Fin D.e)) :
    unitDrop D u = ((u.1.1.1, u.1.2), (u.2.1.1, u.2.2)) :=
  rfl

/-- With one-dimensional additional systems, the extended Born rule is the Born rule. -/
theorem bornExtended_unitExt {X' Y' A' B' : Type} [Fintype A'] [Fintype B'] (W : PMat D)
    (M : Instrument (Fin D.m) (Fin D.d) X' A') (N : Instrument (Fin D.n) (Fin D.e) Y' B')
    (x : X') (y : Y') (a : A') (b : B') :
    bornExtended D W (1 : Op (Unit × Unit)) M.unitExt N.unitExt x y a b = born D W M N x y a b := by
  have h1 : extendInput D W (1 : Op (Unit × Unit)) = W.submatrix (unitDrop D) (unitDrop D) := by
    ext ⟨⟨⟨ai, ⟨⟩⟩, ao⟩, ⟨⟨bi, ⟨⟩⟩, bo⟩⟩ ⟨⟨⟨ai', ⟨⟩⟩, ao'⟩, ⟨⟨bi', ⟨⟩⟩, bo'⟩⟩
    simp [extendInput_apply]
  have h2 : M.unitExt.elem x a ⊗ₖ N.unitExt.elem y b =
      (M.elem x a ⊗ₖ N.elem y b).submatrix (unitDrop D) (unitDrop D) := by
    ext ⟨⟨⟨ai, ⟨⟩⟩, ao⟩, ⟨⟨bi, ⟨⟩⟩, bo⟩⟩ ⟨⟨⟨ai', ⟨⟩⟩, ao'⟩, ⟨⟨bi', ⟨⟩⟩, bo'⟩⟩
    simp [Instrument.unitExt, Matrix.kroneckerMap_apply]
  simp only [bornExtended, born, h1, h2]
  rw [Matrix.submatrix_mul_equiv, trace_submatrix_equiv']

/-- **Extensibly causal processes are causal**. -/
theorem causalProcess_of_extensiblyCausal {W : PMat D} (h : ExtensiblyCausal D W) :
    CausalProcess D W := by
  obtain ⟨hW, hgen⟩ := (extensiblyCausal_iff_gen D W).mp h
  refine ⟨hW, fun nx ny na nb M N => ?_⟩
  have hσ : Density (1 : Op (Unit × Unit)) := ⟨Matrix.PosSemidef.one, by simp⟩
  have hc := hgen Unit Unit (Fin (nx + 1)) (Fin (ny + 1)) (Fin (na + 1)) (Fin (nb + 1)) 1 hσ
    M.unitExt N.unitExt
  have heq : bornExtended D W (1 : Op (Unit × Unit)) M.unitExt N.unitExt = born D W M N := by
    funext x y a b
    exact bornExtended_unitExt W M N x y a b
  rwa [heq] at hc

/-- **Causal distributions form a convex set**: a convex combination of two
causal distributions is causal, with the weight `λ = t λ₁ + (1 - t) λ₂` for the order `A ≺ B`. -/
theorem Causal.convex {p₁ p₂ : Prob X Y A B} (h₁ : Causal p₁) (h₂ : Causal p₂) {t : ℝ}
    (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    Causal (fun x y a b => t * p₁ x y a b + (1 - t) * p₂ x y a b) := by
  obtain ⟨l₁, A₁, B₁, hl₁0, hl₁1, hA₁, hB₁, hnA₁, hnB₁, hd₁⟩ := h₁
  obtain ⟨l₂, A₂, B₂, hl₂0, hl₂1, hA₂, hB₂, hnA₂, hnB₂, hd₂⟩ := h₂
  have ht1' : 0 ≤ 1 - t := by linarith
  have hc1 : 0 ≤ t * l₁ := mul_nonneg ht0 hl₁0
  have hc2 : 0 ≤ (1 - t) * l₂ := mul_nonneg ht1' hl₂0
  have hc3 : 0 ≤ t * (1 - l₁) := mul_nonneg ht0 (by linarith)
  have hc4 : 0 ≤ (1 - t) * (1 - l₂) := mul_nonneg ht1' (by linarith)
  set l := t * l₁ + (1 - t) * l₂ with hl
  have hl0 : 0 ≤ l := add_nonneg hc1 hc2
  have hl1' : 1 - l = t * (1 - l₁) + (1 - t) * (1 - l₂) := by rw [hl]; ring
  have hl1 : l ≤ 1 := by linarith [add_nonneg hc3 hc4]
  refine ⟨l, fun x y a b => if l = 0 then A₁ x y a b
      else (t * l₁ * A₁ x y a b + (1 - t) * l₂ * A₂ x y a b) / l,
    fun x y a b => if l = 1 then B₁ x y a b
      else (t * (1 - l₁) * B₁ x y a b + (1 - t) * (1 - l₂) * B₂ x y a b) / (1 - l),
    hl0, hl1, ⟨fun x y a b => ?_, fun x y => ?_⟩, ⟨fun x y a b => ?_, fun x y => ?_⟩,
    fun x y y' a => ?_, fun x x' y b => ?_, fun x y a b => ?_⟩
  · by_cases h : l = 0
    · simp only [if_pos h]
      exact hA₁.1 x y a b
    · simp only [if_neg h]
      exact div_nonneg (add_nonneg (mul_nonneg hc1 (hA₁.1 x y a b))
        (mul_nonneg hc2 (hA₂.1 x y a b))) hl0
  · by_cases h : l = 0
    · simp only [if_pos h]
      exact hA₁.2 x y
    · simp only [if_neg h, ← Finset.sum_div, Finset.sum_add_distrib, ← Finset.mul_sum,
        hA₁.2 x y, hA₂.2 x y, mul_one]
      exact (div_eq_one_iff_eq h).2 (by linarith [hl])
  · by_cases h : l = 1
    · simp only [if_pos h]
      exact hB₁.1 x y a b
    · simp only [if_neg h]
      exact div_nonneg (add_nonneg (mul_nonneg hc3 (hB₁.1 x y a b))
        (mul_nonneg hc4 (hB₂.1 x y a b))) (by linarith)
  · by_cases h : l = 1
    · simp only [if_pos h]
      exact hB₁.2 x y
    · have h' : 1 - l ≠ 0 := sub_ne_zero.mpr (Ne.symm h)
      simp only [if_neg h, ← Finset.sum_div, Finset.sum_add_distrib, ← Finset.mul_sum,
        hB₁.2 x y, hB₂.2 x y, mul_one]
      exact (div_eq_one_iff_eq h').2 (by linarith [hl1'])
  · by_cases h : l = 0
    · simp only [if_pos h]
      exact hnA₁ x y y' a
    · simp only [if_neg h, ← Finset.sum_div, Finset.sum_add_distrib, ← Finset.mul_sum,
        hnA₁ x y y' a, hnA₂ x y y' a]
  · by_cases h : l = 1
    · simp only [if_pos h]
      exact hnB₁ x x' y b
    · simp only [if_neg h, ← Finset.sum_div, Finset.sum_add_distrib, ← Finset.mul_sum,
        hnB₁ x x' y b, hnB₂ x x' y b]
  · simp only [hd₁ x y a b, hd₂ x y a b]
    by_cases h0 : l = 0
    · have h1 : ¬ l = 1 := by rw [h0]; norm_num
      have h0' : t * l₁ + (1 - t) * l₂ = 0 := by rw [← hl]; exact h0
      obtain ⟨e1, e2⟩ := (add_eq_zero_iff_of_nonneg hc1 hc2).1 h0'
      simp only [if_pos h0, if_neg h1]
      rw [h0]
      linear_combination A₁ x y a b * e1 + A₂ x y a b * e2
    · by_cases h1 : l = 1
      · have h1' : t * (1 - l₁) + (1 - t) * (1 - l₂) = 0 := by rw [← hl1', h1]; ring
        obtain ⟨e3, e4⟩ := (add_eq_zero_iff_of_nonneg hc3 hc4).1 h1'
        simp only [if_neg h0, if_pos h1]
        rw [h1]
        linear_combination B₁ x y a b * e3 + B₂ x y a b * e4
      · have h1' : 1 - l ≠ 0 := sub_ne_zero.mpr (Ne.symm h1)
        simp only [if_neg h0, if_neg h1]
        rw [mul_div_assoc', mul_div_assoc', mul_div_cancel_left₀ _ h0,
          mul_div_cancel_left₀ _ h1']
        ring

/-- A convex combination of processes is a process. -/
theorem Valid.convex {W₁ W₂ : PMat D} (h₁ : Valid D W₁) (h₂ : Valid D W₂) {t : ℝ} (ht0 : 0 ≤ t)
    (ht1 : t ≤ 1) : Valid D ((t : ℂ) • W₁ + ((1 - t : ℝ) : ℂ) • W₂) := by
  refine ⟨genLV_add (genLV_smul (isSelfAdjoint_ofReal t) h₁.1)
      (genLV_smul (isSelfAdjoint_ofReal (1 - t)) h₂.1),
    (posSemidef_complex_smul h₁.2.1 (Complex.zero_le_real.mpr ht0)).add
      (posSemidef_complex_smul h₂.2.1 (Complex.zero_le_real.mpr (by linarith))), ?_⟩
  rw [Matrix.trace_add, Matrix.trace_smul, Matrix.trace_smul, h₁.2.2, h₂.2.2, smul_eq_mul,
    smul_eq_mul]
  push_cast
  ring

/-- **Extensibly causal processes form a convex set** (for given local
dimensions): in every experiment the distribution of a convex combination is the convex
combination of the distributions (`bornExtended_convex`), and causal distributions form a convex
set (`Causal.convex`). -/
theorem ExtensiblyCausal.convex {W₁ W₂ : PMat D} (h₁ : ExtensiblyCausal D W₁)
    (h₂ : ExtensiblyCausal D W₂) {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    ExtensiblyCausal D ((t : ℂ) • W₁ + ((1 - t : ℝ) : ℂ) • W₂) := by
  refine ⟨Valid.convex h₁.1 h₂.1 ht0 ht1, fun r s nx ny na nb σ hσ M N => ?_⟩
  have hc := Causal.convex (h₁.2 r s nx ny na nb σ hσ M N) (h₂.2 r s nx ny na nb σ hσ M N)
    ht0 ht1
  have e : bornExtended D ((t : ℂ) • W₁ + ((1 - t : ℝ) : ℂ) • W₂) σ M N =
      fun x y a b => t * bornExtended D W₁ σ M N x y a b +
        (1 - t) * bornExtended D W₂ σ M N x y a b := by
    funext x y a b
    exact bornExtended_convex t W₁ W₂ σ M N x y a b
  rw [e]
  exact hc

end

end CausalNonpurifiability
