module

public import Mathlib
public import CausalNonpurifiability.Definitions.Process
public import CausalNonpurifiability.Definitions.Purity
public import CausalNonpurifiability.Definitions.Instruments
public import CausalNonpurifiability.Certificates.Qubit

@[expose] public section


/-!
# `CausalNonpurifiability.Boundary.Transpose`

The transpose-convention theorem (manuscript §2.3, last paragraph). The primary definition is
`eq:purification`; the OQP-page formula is a separate compatibility theorem.

"Full transposition preserves positivity and `eq:LV`, commutes with replacements, and preserves
complete purity by complex conjugation of the unitary maps.  Transposing the instruments and
ancillary state likewise preserves the set of obtainable distributions.  Hence validity, causal
separability, extensible causality, and purifiability are invariant under this convention
change."  Each sentence is a section below:

* replacements commute with `ᵀ` (`R_AO_transpose`, …), hence `GenLV.transpose`,
  `InLV.transpose`, `Valid.transpose`, `OrderedAB/OrderedBA.transpose`,
  `CausallySeparable.transpose` (and `↔` forms, since `Wᵀᵀ = W`);
* purity: `UnitaryChoi.transpose` (witness `U ↦ U.map star`, complex conjugation),
  `ChannelChoi.transpose`, `link_transpose : link D Sᵀ JAᵀ JBᵀ = (link D S JA JB)ᵀ`,
  `Deterministic.transpose`, `Pure.transpose`, `Purifiable.transpose`;
* extensible causality: `Instrument.transpose`, `extendInput_transpose`,
  `bornExtended_transpose`, `ExtensiblyCausal.transpose`;
* the OQP-page formula: `purifiable_iff_transpose_convention` (recovering `W` as the transpose
  of `eq:purification` is equivalent), and `Wq_transpose : (toC (W0 2 2 2 2))ᵀ = toC (W0 2 2 2 2)`.

Manuscript anchors: §2.3 last paragraph, `eq:purification`, `eq:link`, `eq:LV`, `eq:valid`,
`eq:ordered-cones`, `eq:born`.
-/

set_option autoImplicit false

open Matrix
open scoped ComplexOrder Kronecker

namespace CausalNonpurifiability

/-! ### Generic transpose facts -/

section Generic

/-- Partial trace commutes with the full transpose. -/
theorem ptraceOut_transpose {I O : Type} [Fintype O] (T : Op (I × O)) :
    ptraceOut Tᵀ = (ptraceOut T)ᵀ := by
  ext i j
  simp only [ptraceOut_apply, Matrix.transpose_apply]

/-- `(A ⊗ B)ᵀ = Aᵀ ⊗ Bᵀ` (entrywise). -/
theorem kronecker_transpose_eq {ι κ : Type} (A : Op ι) (B : Op κ) : (A ⊗ₖ B)ᵀ = Aᵀ ⊗ₖ Bᵀ := by
  ext ⟨i, k⟩ ⟨j, l⟩
  rfl

end Generic

/-! ### Replacements commute with the transpose (`eq:replacement`) -/

section Replacement

variable {AI AO BI BO : Type} [Fintype AI] [Fintype AO] [Fintype BI] [Fintype BO] [DecidableEq AI]
  [DecidableEq AO] [DecidableEq BI] [DecidableEq BO]

theorem R_AO_transpose (W : Op (LabIdx AI AO BI BO)) : R_AO Wᵀ = (R_AO W)ᵀ := by
  ext x y
  rw [Matrix.transpose_apply, R_AO_apply, R_AO_apply]
  simp only [Matrix.transpose_apply]
  by_cases h : x.1.2 = y.1.2
  · rw [if_pos h, if_pos h.symm]
  · rw [if_neg h, if_neg (Ne.symm h)]

theorem R_BO_transpose (W : Op (LabIdx AI AO BI BO)) : R_BO Wᵀ = (R_BO W)ᵀ := by
  ext x y
  rw [Matrix.transpose_apply, R_BO_apply, R_BO_apply]
  simp only [Matrix.transpose_apply]
  by_cases h : x.2.2 = y.2.2
  · rw [if_pos h, if_pos h.symm]
  · rw [if_neg h, if_neg (Ne.symm h)]

theorem R_BIBO_transpose (W : Op (LabIdx AI AO BI BO)) : R_BIBO Wᵀ = (R_BIBO W)ᵀ := by
  ext x y
  rw [Matrix.transpose_apply, R_BIBO_apply, R_BIBO_apply]
  simp only [Matrix.transpose_apply]
  by_cases h : x.2 = y.2
  · rw [if_pos h, if_pos h.symm]
  · rw [if_neg h, if_neg (Ne.symm h)]

theorem R_AIAO_transpose (W : Op (LabIdx AI AO BI BO)) : R_AIAO Wᵀ = (R_AIAO W)ᵀ := by
  ext x y
  rw [Matrix.transpose_apply, R_AIAO_apply, R_AIAO_apply]
  simp only [Matrix.transpose_apply]
  by_cases h : x.1 = y.1
  · rw [if_pos h, if_pos h.symm]
  · rw [if_neg h, if_neg (Ne.symm h)]

/-- `eq:LV` is invariant under the full transpose. -/
theorem GenLV.transpose {W : Op (LabIdx AI AO BI BO)} (h : GenLV W) : GenLV Wᵀ := by
  obtain ⟨hH, ha, hb, hc⟩ := h
  refine ⟨hH.transpose, ?_, ?_, ?_⟩
  · rw [R_BIBO_transpose, R_AO_transpose, ← Matrix.transpose_sub, ha, Matrix.transpose_zero]
  · rw [R_AIAO_transpose, R_BO_transpose, ← Matrix.transpose_sub, hb, Matrix.transpose_zero]
  · rw [R_AO_transpose, R_BO_transpose, R_AO_transpose, ← Matrix.transpose_sub,
      ← Matrix.transpose_sub, ← Matrix.transpose_add, hc, Matrix.transpose_zero]

end Replacement

/-! ### Validity, ordered cones, causal separability -/

section Process

variable {D : Ports}

theorem InLV.transpose {W : PMat D} (h : InLV D W) : InLV D Wᵀ := GenLV.transpose h

theorem inLV_transpose_iff (W : PMat D) : InLV D Wᵀ ↔ InLV D W :=
  ⟨fun h => by simpa using InLV.transpose h, InLV.transpose⟩

/-- Validity (`eq:valid`) is invariant under the full transpose. -/
theorem Valid.transpose {W : PMat D} (h : Valid D W) : Valid D Wᵀ :=
  ⟨InLV.transpose h.1, h.2.1.transpose, by rw [Matrix.trace_transpose]; exact h.2.2⟩

theorem valid_transpose_iff (W : PMat D) : Valid D Wᵀ ↔ Valid D W :=
  ⟨fun h => by simpa using Valid.transpose h, Valid.transpose⟩

/-- `O_{A≺B}` (`eq:ordered-cones`) is invariant under the full transpose. -/
theorem OrderedAB.transpose {T : PMat D} (h : OrderedAB D T) : OrderedAB D Tᵀ :=
  ⟨InLV.transpose h.1, h.2.1.transpose, by rw [R_BO_transpose, h.2.2]⟩

/-- `O_{B≺A}` (`eq:ordered-cones`) is invariant under the full transpose. -/
theorem OrderedBA.transpose {T : PMat D} (h : OrderedBA D T) : OrderedBA D Tᵀ :=
  ⟨InLV.transpose h.1, h.2.1.transpose, by rw [R_AO_transpose, h.2.2]⟩

theorem orderedAB_transpose_iff (T : PMat D) : OrderedAB D Tᵀ ↔ OrderedAB D T :=
  ⟨fun h => by simpa using OrderedAB.transpose h, OrderedAB.transpose⟩

theorem orderedBA_transpose_iff (T : PMat D) : OrderedBA D Tᵀ ↔ OrderedBA D T :=
  ⟨fun h => by simpa using OrderedBA.transpose h, OrderedBA.transpose⟩

/-- Causal separability is invariant under the full transpose. -/
theorem CausallySeparable.transpose {W : PMat D} (h : CausallySeparable D W) :
    CausallySeparable D Wᵀ := by
  obtain ⟨hW, U, V, hU, hV, hUV⟩ := h
  exact ⟨Valid.transpose hW, Uᵀ, Vᵀ, OrderedAB.transpose hU, OrderedBA.transpose hV,
    by rw [hUV, Matrix.transpose_add]⟩

theorem causallySeparable_transpose_iff (W : PMat D) :
    CausallySeparable D Wᵀ ↔ CausallySeparable D W :=
  ⟨fun h => by simpa using CausallySeparable.transpose h, CausallySeparable.transpose⟩

end Process

/-! ### Complete purity: complex conjugation of the unitary maps -/

section Purity

/-- A unitary Choi matrix stays unitary under the full transpose: the witness is the complex
conjugate `U.map star` (§2.3, "preserves complete purity by complex conjugation of the unitary
maps"). -/
theorem UnitaryChoi.transpose {I O : Type} [Fintype I] [Fintype O] [DecidableEq I] [DecidableEq O]
    {J : Op (I × O)} (h : UnitaryChoi J) : UnitaryChoi Jᵀ := by
  obtain ⟨U, h1, h2, hJ⟩ := h
  refine ⟨U.map star, ?_, ?_, fun i o j o' => ?_⟩
  · ext a b
    have hab := congrArg star (congrFun (congrFun h1 a) b)
    rw [Matrix.mul_apply, star_sum] at hab
    simp only [Matrix.conjTranspose_apply, star_mul', star_star] at hab
    rw [Matrix.mul_apply]
    simp only [Matrix.conjTranspose_apply, Matrix.map_apply, star_star]
    rw [hab, Matrix.one_apply]
    split_ifs <;> simp
  · ext o o'
    have hoo := congrArg star (congrFun (congrFun h2 o) o')
    rw [Matrix.mul_apply, star_sum] at hoo
    simp only [Matrix.conjTranspose_apply, star_mul', star_star] at hoo
    rw [Matrix.mul_apply]
    simp only [Matrix.conjTranspose_apply, Matrix.map_apply, star_star]
    rw [hoo, Matrix.one_apply]
    split_ifs <;> simp
  · rw [Matrix.transpose_apply, hJ]
    simp only [Matrix.map_apply, star_star]
    ring

/-- A channel Choi matrix stays a channel Choi matrix under the full transpose. -/
theorem ChannelChoi.transpose {I O : Type} [Fintype I] [Fintype O] [DecidableEq I]
    {J : Op (I × O)} (h : ChannelChoi J) : ChannelChoi Jᵀ :=
  ⟨h.1.transpose, by rw [ptraceOut_transpose, h.2, Matrix.transpose_one]⟩

variable (D : Ports)

/-- `eq:link` commutes with the full transpose of all three factors. -/
theorem link_transpose {p f a a' b b' : ℕ} (S : HigherOp D p f) (JA : ExtChoiA D a a')
    (JB : ExtChoiB D b b') : link D Sᵀ JAᵀ JBᵀ = (link D S JA JB)ᵀ := by
  ext u v
  simp only [link_apply, Matrix.transpose_apply]
  exact Finset.sum_comm

theorem Deterministic.transpose {p f : ℕ} {S : HigherOp D p f} (h : Deterministic D S) :
    Deterministic D Sᵀ := by
  refine ⟨h.1.transpose, fun a a' b b' JA JB hA hB => ?_⟩
  have e : link D Sᵀ JA JB = (link D S JAᵀ JBᵀ)ᵀ := by
    rw [← link_transpose, Matrix.transpose_transpose, Matrix.transpose_transpose]
  rw [e]
  exact ChannelChoi.transpose (h.2 a a' b b' JAᵀ JBᵀ (ChannelChoi.transpose hA)
    (ChannelChoi.transpose hB))

/-- Complete purity (AFNB Definition 3) is invariant under the full transpose. -/
theorem Pure.transpose {p f : ℕ} {S : HigherOp D p f} (h : Pure D S) : Pure D Sᵀ := by
  refine ⟨Deterministic.transpose D h.1, fun a a' b b' JA JB hA hB => ?_⟩
  have e : link D Sᵀ JA JB = (link D S JAᵀ JBᵀ)ᵀ := by
    rw [← link_transpose, Matrix.transpose_transpose, Matrix.transpose_transpose]
  rw [e]
  exact UnitaryChoi.transpose (h.2 a a' b b' JAᵀ JBᵀ (UnitaryChoi.transpose hA)
    (UnitaryChoi.transpose hB))

/-- Purifiability (`eq:purification`) is invariant under the full transpose. -/
theorem Purifiable.transpose {W : PMat D} (h : Purifiable D W) : Purifiable D Wᵀ := by
  obtain ⟨p, f, S, hS, hW⟩ := h
  exact ⟨p, f, Sᵀ, Pure.transpose D hS, by rw [reducePastFuture_transpose, hW]⟩

theorem purifiable_transpose_iff (W : PMat D) : Purifiable D Wᵀ ↔ Purifiable D W :=
  ⟨fun h => by simpa using Purifiable.transpose D h, Purifiable.transpose D⟩

/-- **The OQP-page convention is immaterial** (§2.3): `W` is purifiable in the sense of
`eq:purification` iff it is the *full transpose* of the recovery of some completely pure
higher-order process (the Problem 43 page's `Sᵀ` formula). -/
theorem purifiable_iff_transpose_convention (W : PMat D) :
    Purifiable D W ↔
      ∃ (p f : ℕ) (S : HigherOp D p f), Pure D S ∧ (reducePastFuture D S)ᵀ = W := by
  constructor
  · rintro ⟨p, f, S, hS, hW⟩
    exact ⟨p, f, Sᵀ, Pure.transpose D hS,
      by rw [reducePastFuture_transpose, Matrix.transpose_transpose, hW]⟩
  · rintro ⟨p, f, S, hS, hW⟩
    exact ⟨p, f, Sᵀ, Pure.transpose D hS, by rw [reducePastFuture_transpose, hW]⟩

end Purity

/-! ### Extensible causality: transposing instruments and the ancilla state -/

section Extensible

variable (D : Ports)

/-- Elementwise transpose of an instrument (positivity and normalization are preserved). -/
def Instrument.transpose {I O X A : Type} [Fintype I] [Fintype O] [Fintype A] [DecidableEq I]
    (M : Instrument I O X A) : Instrument I O X A where
  elem x a := (M.elem x a)ᵀ
  positive x a := (M.positive x a).transpose
  normalized x := by
    rw [← Matrix.transpose_sum, ptraceOut_transpose, M.normalized x, Matrix.transpose_one]

@[simp] theorem Instrument.transpose_elem {I O X A : Type} [Fintype I] [Fintype O] [Fintype A]
    [DecidableEq I] (M : Instrument I O X A) (x : X) (a : A) :
    M.transpose.elem x a = (M.elem x a)ᵀ := rfl

variable {RA RB : Type}

theorem extendInput_transpose (W : PMat D) (σ : Op (RA × RB)) :
    extendInput D Wᵀ σᵀ = (extendInput D W σ)ᵀ := by
  ext x y
  rfl

variable {X Y A B : Type} [Fintype RA] [DecidableEq RA] [Fintype RB] [DecidableEq RB] [Fintype A]
  [Fintype B]

/-- Transposing the process, the ancilla state and both instruments leaves the Born
distribution unchanged (`Tr[Xᵀ Yᵀ] = Tr[X Y]`). -/
theorem bornExtended_transpose (W : PMat D) (σ : Op (RA × RB))
    (M : Instrument (Fin D.m × RA) (Fin D.d) X A) (N : Instrument (Fin D.n × RB) (Fin D.e) Y B)
    (x : X) (y : Y) (a : A) (b : B) :
    bornExtended D Wᵀ σᵀ M.transpose N.transpose x y a b = bornExtended D W σ M N x y a b := by
  simp only [bornExtended, Instrument.transpose_elem, extendInput_transpose]
  rw [← kronecker_transpose_eq, ← Matrix.transpose_mul, Matrix.trace_transpose,
    Matrix.trace_mul_comm]

/-- Variant with the transposes moved to the other side. -/
theorem bornExtended_transpose' (W : PMat D) (σ : Op (RA × RB))
    (M : Instrument (Fin D.m × RA) (Fin D.d) X A) (N : Instrument (Fin D.n × RB) (Fin D.e) Y B)
    (x : X) (y : Y) (a : A) (b : B) :
    bornExtended D Wᵀ σ M N x y a b = bornExtended D W σᵀ M.transpose N.transpose x y a b := by
  simp only [bornExtended, Instrument.transpose_elem]
  have e : extendInput D Wᵀ σ = (extendInput D W σᵀ)ᵀ := by
    rw [← extendInput_transpose, Matrix.transpose_transpose]
  rw [e, ← Matrix.transpose_transpose (M.elem x a ⊗ₖ N.elem y b), kronecker_transpose_eq,
    ← Matrix.transpose_mul, Matrix.trace_transpose, Matrix.trace_mul_comm]

theorem Density.transpose {I : Type} [Fintype I] {σ : Op I} (h : Density σ) : Density σᵀ :=
  ⟨h.1.transpose, by rw [Matrix.trace_transpose]; exact h.2⟩

/-- Extensible causality is invariant under the full transpose (§2.3: "transposing the
instruments and ancillary state likewise preserves the set of obtainable distributions"). -/
theorem ExtensiblyCausal.transpose {W : PMat D} (h : ExtensiblyCausal D W) :
    ExtensiblyCausal D Wᵀ := by
  refine ⟨Valid.transpose h.1, fun r s nx ny na nb σ hσ M N => ?_⟩
  have key : bornExtended D Wᵀ σ M N = bornExtended D W σᵀ M.transpose N.transpose := by
    funext x y a b
    exact bornExtended_transpose' D W σ M N x y a b
  rw [key]
  exact h.2 r s nx ny na nb σᵀ (Density.transpose hσ) M.transpose N.transpose

theorem extensiblyCausal_transpose_iff (W : PMat D) :
    ExtensiblyCausal D Wᵀ ↔ ExtensiblyCausal D W :=
  ⟨fun h => by simpa using ExtensiblyCausal.transpose D h, ExtensiblyCausal.transpose D⟩

end Extensible

/-! ### The qubit example is transpose-symmetric -/

/-- `Wqᵀ = Wq` for the kernel example `Wq = toC (W0 2 2 2 2)` (`W0_transpose`), so the
convention question does not even arise there. -/
theorem Wq_transpose : (toC (W0 2 2 2 2))ᵀ = toC (W0 2 2 2 2) := by
  rw [← Matrix.transpose_map, W0_transpose]

end CausalNonpurifiability
