module

public import CausalNonpurifiability.Linear.PartialTrace

@[expose] public section


/-!
# `CausalNonpurifiability.Linear.Replacement`

Replacement maps `R_Y T = (I_Y / |Y|) ⊗ Tr_Y T` (`eq:replacement`) as `ℂ`-linear maps
on operators over generic laboratory indices `LabIdx AI AO BI BO`, with the manuscript's
structural facts: idempotence, commutation on disjoint factors, trace preservation,
unitality, positivity, Hermiticity, and Hilbert–Schmidt self-adjointness
`Tr((R_Y A) B) = Tr(A (R_Y B))`; and the ancilla extension `extended W σ` (`W ⊗ σ` with
the ancilla factors attached to the inputs) together with the way the
four replacement maps act through it (output replacements act on `W` alone, input
partial traces factor through `σ`).

## Architecture

* `replaceLast` is the last-factor form on `Op (I × Y)`:
  `R(T)_{(i,y),(j,y')} = δ_{y,y'} (Tr_Y T)_{i,j} / |Y|`, written as
  `invCard Y • (ptraceOut T ⊗ₖ 1)`.
* `replaceVia e` transports it along a coordinate equivalence `e : ι ≃ I × Y`
  (`Matrix.reindex`), so every lemma is proved once and specialised.
* `R_AO`, `R_BO`, `R_BIBO`, `R_AIAO` are `replaceVia` along the named equivalences of
  `CausalNonpurifiability.Linear.Indices`, generic in the four finite factor types; the factor
  `1/|Y|` is present throughout.

Manuscript anchors: `eq:replacement` and Lemma 2.1 (`lem:replacement`: the maps are positive, unital, trace preserving and self-adjoint for the
Hilbert–Schmidt inner product, and `R_Y R_Z = R_{Y∪Z}`); the second statement of Lemma 2.3 and
its proof (`W ⊗ σ` satisfies `eq:LV` for the enlarged input spaces).
-/

set_option autoImplicit false
-- Generic-index lemmas deliberately carry the uniform `[Fintype _] [DecidableEq _]` assumptions of
-- their sections (a few are not needed by individual statements); the corresponding linter is off.
set_option linter.unusedSectionVars false

open scoped Kronecker ComplexOrder

namespace CausalNonpurifiability

noncomputable section

/-! ### The scalar `1/|Y|` -/

/-- `1/|Y|` as a complex scalar (`eq:replacement`). -/
def invCard (Y : Type) [Fintype Y] : ℂ := ((Fintype.card Y : ℂ))⁻¹

section InvCard

variable (Y : Type) [Fintype Y]

theorem invCard_mul_card [Nonempty Y] : invCard Y * (Fintype.card Y : ℂ) = 1 :=
  inv_mul_cancel₀ (Nat.cast_ne_zero.2 Fintype.card_ne_zero)

theorem card_mul_invCard [Nonempty Y] : (Fintype.card Y : ℂ) * invCard Y = 1 :=
  mul_inv_cancel₀ (Nat.cast_ne_zero.2 Fintype.card_ne_zero)

theorem invCard_ne_zero [Nonempty Y] : invCard Y ≠ 0 :=
  inv_ne_zero (Nat.cast_ne_zero.2 Fintype.card_ne_zero)

theorem star_invCard : star (invCard Y) = invCard Y := by
  simp [invCard]

theorem invCard_nonneg : 0 ≤ invCard Y := by
  have h : (0 : ℝ) ≤ (Fintype.card Y : ℝ)⁻¹ := by positivity
  simp [invCard]

/-- `1/|(X × R) × Y| = (1/|X × Y|) · (1/|R|)`: the scalar bookkeeping of the extension. -/
theorem invCard_prod_prod (X R : Type) [Fintype X] [Fintype R] :
    invCard ((X × R) × Y) = invCard (X × Y) * invCard R := by
  simp only [invCard, Fintype.card_prod, Nat.cast_mul]
  rw [mul_inv, mul_inv, mul_inv]
  ring

end InvCard

/-! ### Last-factor replacement -/

section Generic

variable {I Y : Type} [Fintype I] [Fintype Y] [DecidableEq I] [DecidableEq Y]

/-- Replacement of the final factor: `R T = (1/|Y|) • (Tr_Y T ⊗ I_Y)` on `Op (I × Y)`
(`eq:replacement` in the last-factor form
`R_Y(T)_{(i,y),(j,y')} = δ_{y,y'} (Tr_Y T)_{i,j} / |Y|`). -/
def replaceLast (T : Op (I × Y)) : Op (I × Y) := invCard Y • (ptraceOut T ⊗ₖ (1 : Op Y))

omit [Fintype I] [DecidableEq I] in
theorem replaceLast_apply (T : Op (I × Y)) (x y : I × Y) :
    replaceLast T x y = if x.2 = y.2 then invCard Y * ptraceOut T x.1 y.1 else 0 := by
  simp only [replaceLast, Matrix.smul_apply, Matrix.kroneckerMap_apply, Matrix.one_apply,
    smul_eq_mul, mul_ite, mul_one, mul_zero]

omit [Fintype I] [DecidableEq I] in
theorem replaceLast_add (S T : Op (I × Y)) :
    replaceLast (S + T) = replaceLast S + replaceLast T := by
  unfold replaceLast
  rw [ptraceOut_add, Matrix.add_kronecker, smul_add]

omit [Fintype I] [DecidableEq I] in
theorem replaceLast_smul (c : ℂ) (T : Op (I × Y)) : replaceLast (c • T) = c • replaceLast T := by
  unfold replaceLast
  rw [ptraceOut_smul, Matrix.smul_kronecker, smul_comm]

/-- `replaceLast` as a `ℂ`-linear map. -/
def replaceLastₗ : Op (I × Y) →ₗ[ℂ] Op (I × Y) where
  toFun := replaceLast
  map_add' := replaceLast_add
  map_smul' := replaceLast_smul

omit [Fintype I] in
@[simp] theorem replaceLastₗ_apply (T : Op (I × Y)) : replaceLastₗ T = replaceLast T := rfl

omit [DecidableEq I] in
theorem ptraceOut_replaceLast [Nonempty Y] (T : Op (I × Y)) :
    ptraceOut (replaceLast T) = ptraceOut T := by
  unfold replaceLast
  rw [ptraceOut_smul, ptraceOut_kronecker, Matrix.trace_one, smul_smul, invCard_mul_card,
    one_smul]

omit [DecidableEq I] in
theorem replaceLast_idem [Nonempty Y] (T : Op (I × Y)) :
    replaceLast (replaceLast T) = replaceLast T := by
  show invCard Y • (ptraceOut (replaceLast T) ⊗ₖ (1 : Op Y)) = replaceLast T
  rw [ptraceOut_replaceLast]
  rfl

omit [DecidableEq I] in
theorem trace_replaceLast [Nonempty Y] (T : Op (I × Y)) : (replaceLast T).trace = T.trace := by
  unfold replaceLast
  rw [Matrix.trace_smul, Matrix.trace_kronecker, Matrix.trace_one, trace_ptraceOut, smul_eq_mul,
    mul_comm T.trace, ← mul_assoc, invCard_mul_card, one_mul]

theorem replaceLast_one [Nonempty Y] : replaceLast (1 : Op (I × Y)) = 1 := by
  unfold replaceLast
  rw [ptraceOut_one, Matrix.smul_kronecker, Matrix.one_kronecker_one, smul_smul, invCard_mul_card,
    one_smul]

omit [DecidableEq I] in
theorem replaceLast_posSemidef {T : Op (I × Y)} (h : T.PosSemidef) :
    (replaceLast T).PosSemidef :=
  ((ptraceOut_posSemidef h).kronecker Matrix.PosSemidef.one).smul (invCard_nonneg Y)

omit [Fintype I] in
theorem replaceLast_isHermitian {T : Op (I × Y)} (h : T.IsHermitian) :
    (replaceLast T).IsHermitian := by
  have hP := ptraceOut_isHermitian h
  refine Matrix.IsHermitian.ext fun x y => ?_
  rw [replaceLast_apply, replaceLast_apply]
  by_cases hxy : x.2 = y.2
  · rw [if_pos hxy, if_pos hxy.symm, star_mul', star_invCard, hP.apply]
  · rw [if_neg hxy, if_neg (Ne.symm hxy), star_zero]

omit [DecidableEq I] in
/-- `Tr((M ⊗ I) B) = Tr(M · Tr_Y B)`: the contraction identity behind self-adjointness. -/
theorem trace_kronecker_one_mul (M : Op I) (B : Op (I × Y)) :
    ((M ⊗ₖ (1 : Op Y)) * B).trace = (M * ptraceOut B).trace := by
  simp only [Matrix.trace, Matrix.diag_apply, Matrix.mul_apply, Matrix.kroneckerMap_apply,
    Matrix.one_apply, ptraceOut_apply, Fintype.sum_prod_type, mul_ite, mul_one, mul_zero,
    ite_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, if_true,
    Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_comm

omit [DecidableEq I] in
theorem trace_replaceLast_mul (A B : Op (I × Y)) :
    (replaceLast A * B).trace = invCard Y * (ptraceOut A * ptraceOut B).trace := by
  unfold replaceLast
  rw [Matrix.smul_mul, Matrix.trace_smul, smul_eq_mul, trace_kronecker_one_mul]

/-- Hilbert–Schmidt self-adjointness of the last-factor replacement. -/
theorem replaceLast_pairing (A B : Op (I × Y)) :
    (replaceLast A * B).trace = (A * replaceLast B).trace := by
  rw [trace_replaceLast_mul, Matrix.trace_mul_comm A (replaceLast B), trace_replaceLast_mul,
    Matrix.trace_mul_comm (ptraceOut B) (ptraceOut A)]

end Generic

/-! ### Replacement along a coordinate equivalence -/

section Via

variable {ι I Y : Type} [Fintype ι] [DecidableEq ι] [Fintype I] [Fintype Y] [DecidableEq I]
  [DecidableEq Y]

/-- Replacement of the factor `Y` singled out by the coordinate equivalence `e : ι ≃ I × Y`:
`R_Y = reindex e⁻¹ ∘ replaceLast ∘ reindex e` (`eq:replacement`). -/
def replaceVia (e : ι ≃ I × Y) : Op ι →ₗ[ℂ] Op ι :=
  (Matrix.reindexLinearEquiv ℂ ℂ e.symm e.symm).toLinearMap ∘ₗ replaceLastₗ ∘ₗ
    (Matrix.reindexLinearEquiv ℂ ℂ e e).toLinearMap

omit [DecidableEq ι] in
/-- Trace is invariant under reindexing by an equivalence. -/
theorem trace_submatrix_equiv' {κ : Type} [Fintype κ] (f : ι ≃ κ) (M : Op κ) :
    (M.submatrix f f).trace = M.trace := by
  simp only [Matrix.trace, Matrix.diag_apply, Matrix.submatrix_apply]
  exact Equiv.sum_comp f (fun j => M j j)

variable (e : ι ≃ I × Y)

omit [Fintype ι] [DecidableEq ι] in
theorem replaceVia_apply (T : Op ι) :
    replaceVia e T = Matrix.reindex e.symm e.symm (replaceLast (Matrix.reindex e e T)) := rfl

omit [Fintype ι] in
/-- Entry formula: `(R_Y T)_{x,y} = δ_{y-part} (1/|Y|) ∑_z T_{(x_I,z),(y_I,z)}`. -/
theorem replaceVia_apply_entry (T : Op ι) (x y : ι) :
    replaceVia e T x y =
      if (e x).2 = (e y).2 then
        invCard Y * ∑ z, T (e.symm ((e x).1, z)) (e.symm ((e y).1, z))
      else 0 := by
  rw [replaceVia_apply]
  simp only [Matrix.reindex_apply, Matrix.submatrix_apply, Equiv.symm_symm, replaceLast_apply,
    ptraceOut_apply]

omit [Fintype ι] [DecidableEq ι] in
theorem replacement_idempotent [Nonempty Y] (T : Op ι) :
    replaceVia e (replaceVia e T) = replaceVia e T := by
  simp only [replaceVia_apply]
  rw [reindex_reindex_symm, replaceLast_idem]

theorem replacement_trace [Nonempty Y] (T : Op ι) : (replaceVia e T).trace = T.trace := by
  rw [replaceVia_apply, Matrix.reindex_apply, trace_submatrix_equiv', trace_replaceLast,
    Matrix.reindex_apply, trace_submatrix_equiv']

omit [Fintype ι] in
theorem replacement_unital [Nonempty Y] : replaceVia e (1 : Op ι) = 1 := by
  simp only [replaceVia_apply, Matrix.reindex_apply, Matrix.submatrix_one_equiv, replaceLast_one]

omit [Fintype ι] in
theorem replacement_psd {T : Op ι} (h : T.PosSemidef) : (replaceVia e T).PosSemidef := by
  rw [replaceVia_apply, Matrix.reindex_apply]
  refine Matrix.PosSemidef.submatrix ?_ _
  rw [Matrix.reindex_apply]
  exact replaceLast_posSemidef (h.submatrix _)

omit [Fintype ι] in
theorem replacement_hermitian {T : Op ι} (h : T.IsHermitian) : (replaceVia e T).IsHermitian := by
  rw [replaceVia_apply, Matrix.reindex_apply]
  refine Matrix.IsHermitian.submatrix ?_ _
  rw [Matrix.reindex_apply]
  exact replaceLast_isHermitian (h.submatrix _)

omit [DecidableEq I] [DecidableEq ι] in
theorem trace_reindex_mul (X X' : Op (I × Y)) :
    (Matrix.reindex e.symm e.symm X * Matrix.reindex e.symm e.symm X').trace = (X * X').trace := by
  rw [Matrix.reindex_apply, Matrix.reindex_apply, Matrix.submatrix_mul_equiv,
    trace_submatrix_equiv']

/-- Hilbert–Schmidt self-adjointness `Tr((R_Y A) B) = Tr(A (R_Y B))`. -/
theorem replacement_trace_pairing (A B : Op ι) :
    (replaceVia e A * B).trace = (A * replaceVia e B).trace := by
  conv_lhs => rw [← reindex_symm_reindex e B]
  conv_rhs => rw [← reindex_symm_reindex e A]
  rw [replaceVia_apply, replaceVia_apply, trace_reindex_mul, trace_reindex_mul,
    replaceLast_pairing]

end Via

/-! ### Replacement of the first factor of a bipartite ancilla -/

section First

variable {RA RB : Type} [Fintype RA] [Fintype RB] [DecidableEq RA] [DecidableEq RB]

/-- Replacement of the *first* factor of `Op (RA × RB)` (`R_{R_A}` on the ancilla). -/
def replaceFst : Op (RA × RB) →ₗ[ℂ] Op (RA × RB) := replaceVia (Equiv.prodComm RA RB)

theorem replaceFst_apply (σ : Op (RA × RB)) (x y : RA × RB) :
    replaceFst σ x y = if x.1 = y.1 then invCard RA * ∑ z, σ (z, x.2) (z, y.2) else 0 := by
  obtain ⟨ra, rb⟩ := x
  obtain ⟨ra', rb'⟩ := y
  simp only [replaceFst, replaceVia_apply_entry, Equiv.prodComm_apply, Equiv.prodComm_symm,
    Prod.swap_prod_mk]
  exact ite_congr rfl (fun _ => rfl) (fun _ => rfl)

end First

/-! ### The four named replacement maps on generic laboratory indices -/

section Named

variable {AI AO BI BO : Type} [Fintype AI] [Fintype AO] [Fintype BI] [Fintype BO]
  [DecidableEq AI] [DecidableEq AO] [DecidableEq BI] [DecidableEq BO]

/-- `R_{A_O}` (`eq:replacement`): `(I_{A_O}/|A_O|) ⊗ Tr_{A_O}`, factors kept in physical order. -/
def R_AO : Op (LabIdx AI AO BI BO) →ₗ[ℂ] Op (LabIdx AI AO BI BO) := replaceVia (eqAO AI AO BI BO)

/-- `R_{B_O}` (`eq:replacement`): `(I_{B_O}/|B_O|) ⊗ Tr_{B_O}`. -/
def R_BO : Op (LabIdx AI AO BI BO) →ₗ[ℂ] Op (LabIdx AI AO BI BO) := replaceVia (eqBO AI AO BI BO)

/-- `R_{B_I B_O}` (`eq:replacement`): `(I_{B_I B_O}/|B_I B_O|) ⊗ Tr_{B_I B_O}`. -/
def R_BIBO : Op (LabIdx AI AO BI BO) →ₗ[ℂ] Op (LabIdx AI AO BI BO) :=
  replaceVia (eqBIBO AI AO BI BO)

/-- `R_{A_I A_O}` (`eq:replacement`): `(I_{A_I A_O}/|A_I A_O|) ⊗ Tr_{A_I A_O}`. -/
def R_AIAO : Op (LabIdx AI AO BI BO) →ₗ[ℂ] Op (LabIdx AI AO BI BO) :=
  replaceVia (eqAIAO AI AO BI BO)

variable (T : Op (LabIdx AI AO BI BO)) (x y : LabIdx AI AO BI BO)

theorem R_AO_apply :
    R_AO T x y =
      if x.1.2 = y.1.2 then invCard AO * ∑ z, T ((x.1.1, z), x.2) ((y.1.1, z), y.2) else 0 := by
  obtain ⟨⟨a, o⟩, ⟨b, t⟩⟩ := x
  obtain ⟨⟨a', o'⟩, ⟨b', t'⟩⟩ := y
  simp only [R_AO, replaceVia_apply_entry, eqAO_apply, eqAO_symm_apply]
  exact ite_congr rfl (fun _ => rfl) (fun _ => rfl)

theorem R_BO_apply :
    R_BO T x y =
      if x.2.2 = y.2.2 then invCard BO * ∑ z, T (x.1, (x.2.1, z)) (y.1, (y.2.1, z)) else 0 := by
  obtain ⟨⟨a, o⟩, ⟨b, t⟩⟩ := x
  obtain ⟨⟨a', o'⟩, ⟨b', t'⟩⟩ := y
  simp only [R_BO, replaceVia_apply_entry, eqBO_apply, eqBO_symm_apply]
  exact ite_congr rfl (fun _ => rfl) (fun _ => rfl)

theorem R_BIBO_apply :
    R_BIBO T x y =
      if x.2 = y.2 then invCard (BI × BO) * ∑ z, T (x.1, z) (y.1, z) else 0 := by
  obtain ⟨⟨a, o⟩, ⟨b, t⟩⟩ := x
  obtain ⟨⟨a', o'⟩, ⟨b', t'⟩⟩ := y
  simp only [R_BIBO, replaceVia_apply_entry, eqBIBO_apply, eqBIBO_symm_apply]
  exact ite_congr rfl (fun _ => rfl) (fun _ => rfl)

theorem R_AIAO_apply :
    R_AIAO T x y =
      if x.1 = y.1 then invCard (AI × AO) * ∑ z, T (z, x.2) (z, y.2) else 0 := by
  obtain ⟨⟨a, o⟩, ⟨b, t⟩⟩ := x
  obtain ⟨⟨a', o'⟩, ⟨b', t'⟩⟩ := y
  simp only [R_AIAO, replaceVia_apply_entry, eqAIAO_apply, eqAIAO_symm_apply]
  exact ite_congr rfl (fun _ => rfl) (fun _ => rfl)

/-! Structural facts, specialised (manuscript sentence after `eq:replacement`). -/

theorem R_AO_idem [Nonempty AO] : R_AO (R_AO T) = R_AO T := replacement_idempotent _ T
theorem R_BO_idem [Nonempty BO] : R_BO (R_BO T) = R_BO T := replacement_idempotent _ T
theorem R_BIBO_idem [Nonempty BI] [Nonempty BO] : R_BIBO (R_BIBO T) = R_BIBO T :=
  replacement_idempotent _ T
theorem R_AIAO_idem [Nonempty AI] [Nonempty AO] : R_AIAO (R_AIAO T) = R_AIAO T :=
  replacement_idempotent _ T

theorem R_AO_trace [Nonempty AO] : (R_AO T).trace = T.trace := replacement_trace _ T
theorem R_BO_trace [Nonempty BO] : (R_BO T).trace = T.trace := replacement_trace _ T
theorem R_BIBO_trace [Nonempty BI] [Nonempty BO] : (R_BIBO T).trace = T.trace :=
  replacement_trace _ T
theorem R_AIAO_trace [Nonempty AI] [Nonempty AO] : (R_AIAO T).trace = T.trace :=
  replacement_trace _ T

theorem R_AO_one [Nonempty AO] : R_AO (1 : Op (LabIdx AI AO BI BO)) = 1 := replacement_unital _
theorem R_BO_one [Nonempty BO] : R_BO (1 : Op (LabIdx AI AO BI BO)) = 1 := replacement_unital _
theorem R_BIBO_one [Nonempty BI] [Nonempty BO] : R_BIBO (1 : Op (LabIdx AI AO BI BO)) = 1 :=
  replacement_unital _
theorem R_AIAO_one [Nonempty AI] [Nonempty AO] : R_AIAO (1 : Op (LabIdx AI AO BI BO)) = 1 :=
  replacement_unital _

variable {T}

theorem R_AO_posSemidef (h : T.PosSemidef) : (R_AO T).PosSemidef := replacement_psd _ h
theorem R_BO_posSemidef (h : T.PosSemidef) : (R_BO T).PosSemidef := replacement_psd _ h
theorem R_BIBO_posSemidef (h : T.PosSemidef) : (R_BIBO T).PosSemidef := replacement_psd _ h
theorem R_AIAO_posSemidef (h : T.PosSemidef) : (R_AIAO T).PosSemidef := replacement_psd _ h

theorem R_AO_isHermitian (h : T.IsHermitian) : (R_AO T).IsHermitian := replacement_hermitian _ h
theorem R_BO_isHermitian (h : T.IsHermitian) : (R_BO T).IsHermitian := replacement_hermitian _ h
theorem R_BIBO_isHermitian (h : T.IsHermitian) : (R_BIBO T).IsHermitian :=
  replacement_hermitian _ h
theorem R_AIAO_isHermitian (h : T.IsHermitian) : (R_AIAO T).IsHermitian :=
  replacement_hermitian _ h

variable (A B : Op (LabIdx AI AO BI BO))

theorem R_AO_pairing : (R_AO A * B).trace = (A * R_AO B).trace := replacement_trace_pairing _ A B
theorem R_BO_pairing : (R_BO A * B).trace = (A * R_BO B).trace := replacement_trace_pairing _ A B
theorem R_BIBO_pairing : (R_BIBO A * B).trace = (A * R_BIBO B).trace :=
  replacement_trace_pairing _ A B
theorem R_AIAO_pairing : (R_AIAO A * B).trace = (A * R_AIAO B).trace :=
  replacement_trace_pairing _ A B

/-! Commutation on disjoint factors (`replacement_commute`). -/

variable (T)

theorem R_AO_R_BO_comm : R_AO (R_BO T) = R_BO (R_AO T) := by
  ext ⟨⟨a, o⟩, ⟨b, t⟩⟩ ⟨⟨a', o'⟩, ⟨b', t'⟩⟩
  simp only [R_AO_apply, R_BO_apply]
  by_cases ho : o = o'
  · subst ho
    by_cases ht : t = t'
    · subst ht
      simp only [if_true, Finset.mul_sum]
      rw [Finset.sum_comm]
      exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring
    · simp [ht]
  · simp [ho]

theorem R_AO_R_BIBO_comm : R_AO (R_BIBO T) = R_BIBO (R_AO T) := by
  ext ⟨⟨a, o⟩, ⟨b, t⟩⟩ ⟨⟨a', o'⟩, ⟨b', t'⟩⟩
  simp only [R_AO_apply, R_BIBO_apply]
  by_cases ho : o = o'
  · subst ho
    by_cases hbt : (b, t) = (b', t')
    · simp only [hbt, if_true, Finset.mul_sum]
      rw [Finset.sum_comm]
      exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring
    · simp [hbt]
  · simp [ho]

theorem R_BO_R_AIAO_comm : R_BO (R_AIAO T) = R_AIAO (R_BO T) := by
  ext ⟨⟨a, o⟩, ⟨b, t⟩⟩ ⟨⟨a', o'⟩, ⟨b', t'⟩⟩
  simp only [R_BO_apply, R_AIAO_apply]
  by_cases ht : t = t'
  · subst ht
    by_cases hao : (a, o) = (a', o')
    · simp only [hao, if_true, Finset.mul_sum]
      rw [Finset.sum_comm]
      exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring
    · simp [hao]
  · simp [ht]

/-- Commutation statement for the three disjoint-factor pairs used by `eq:LV`. -/
theorem replacement_commute :
    (∀ T : Op (LabIdx AI AO BI BO), R_AO (R_BO T) = R_BO (R_AO T)) ∧
    (∀ T : Op (LabIdx AI AO BI BO), R_AO (R_BIBO T) = R_BIBO (R_AO T)) ∧
    (∀ T : Op (LabIdx AI AO BI BO), R_BO (R_AIAO T) = R_AIAO (R_BO T)) :=
  ⟨R_AO_R_BO_comm, R_AO_R_BIBO_comm, R_BO_R_AIAO_comm⟩

end Named

/-! ### Ancilla extension `W ⊗ σ` and how the replacement maps act through it -/

section Extended

variable {AI AO BI BO RA RB : Type}

/-- Ancilla extension `W ⊗ σ` with the ancilla factors attached to the inputs, in the
enlarged-input party-grouped order `((A_I × R_A) × A_O) × ((B_I × R_B) × B_O)`
(entry formula):
`(extended W σ) (((ai,ra),ao),((bi,rb),bo)) (((ai',ra'),ao'),((bi',rb'),bo'))
  = W ((ai,ao),(bi,bo)) ((ai',ao'),(bi',bo')) * σ (ra,rb) (ra',rb')`. -/
def extended (W : Op (LabIdx AI AO BI BO)) (σ : Op (RA × RB)) :
    Op (LabIdx (AI × RA) AO (BI × RB) BO) :=
  fun x y =>
    W ((x.1.1.1, x.1.2), (x.2.1.1, x.2.2)) ((y.1.1.1, y.1.2), (y.2.1.1, y.2.2)) *
      σ (x.1.1.2, x.2.1.2) (y.1.1.2, y.2.1.2)

variable (W : Op (LabIdx AI AO BI BO)) (σ : Op (RA × RB))

theorem extended_apply (x y : LabIdx (AI × RA) AO (BI × RB) BO) :
    extended W σ x y =
      W ((x.1.1.1, x.1.2), (x.2.1.1, x.2.2)) ((y.1.1.1, y.1.2), (y.2.1.1, y.2.2)) *
        σ (x.1.1.2, x.2.1.2) (y.1.1.2, y.2.1.2) := rfl

theorem extended_apply' (ai ai' : AI) (ra ra' : RA) (ao ao' : AO) (bi bi' : BI) (rb rb' : RB)
    (bo bo' : BO) :
    extended W σ (((ai, ra), ao), ((bi, rb), bo)) (((ai', ra'), ao'), ((bi', rb'), bo')) =
      W ((ai, ao), (bi, bo)) ((ai', ao'), (bi', bo')) * σ (ra, rb) (ra', rb') := rfl

theorem extended_add (W' : Op (LabIdx AI AO BI BO)) :
    extended (W + W') σ = extended W σ + extended W' σ := by
  ext x y
  simp only [extended_apply, Matrix.add_apply, add_mul]

theorem extended_sub (W' : Op (LabIdx AI AO BI BO)) :
    extended (W - W') σ = extended W σ - extended W' σ := by
  ext x y
  simp only [extended_apply, Matrix.sub_apply, sub_mul]

theorem extended_zero : extended (0 : Op (LabIdx AI AO BI BO)) σ = 0 := by
  ext x y
  simp only [extended_apply, Matrix.zero_apply, zero_mul]

theorem extended_isHermitian {W : Op (LabIdx AI AO BI BO)} {σ : Op (RA × RB)}
    (hW : W.IsHermitian) (hσ : σ.IsHermitian) : (extended W σ).IsHermitian := by
  refine Matrix.IsHermitian.ext fun x y => ?_
  rw [extended_apply, extended_apply, star_mul', hW.apply, hσ.apply]

variable [Fintype AI] [Fintype AO] [Fintype BI] [Fintype BO] [Fintype RA] [Fintype RB]
  [DecidableEq AI] [DecidableEq AO] [DecidableEq BI] [DecidableEq BO] [DecidableEq RA]
  [DecidableEq RB]

/-- The output replacement `R_{A_O}` acts on `W` alone. -/
theorem R_AO_extended : R_AO (extended W σ) = extended (R_AO W) σ := by
  ext ⟨⟨⟨ai, ra⟩, ao⟩, ⟨⟨bi, rb⟩, bo⟩⟩ ⟨⟨⟨ai', ra'⟩, ao'⟩, ⟨⟨bi', rb'⟩, bo'⟩⟩
  simp only [R_AO_apply, extended_apply, ite_mul, zero_mul, Finset.sum_mul, mul_assoc]

/-- The output replacement `R_{B_O}` acts on `W` alone. -/
theorem R_BO_extended : R_BO (extended W σ) = extended (R_BO W) σ := by
  ext ⟨⟨⟨ai, ra⟩, ao⟩, ⟨⟨bi, rb⟩, bo⟩⟩ ⟨⟨⟨ai', ra'⟩, ao'⟩, ⟨⟨bi', rb'⟩, bo'⟩⟩
  simp only [R_BO_apply, extended_apply, ite_mul, zero_mul, Finset.sum_mul, mul_assoc]

/-- The input partial trace factors through `σ`: `R_{B_I R_B B_O}(W ⊗ σ) = R_{B_I B_O} W ⊗ R_{R_B} σ`. -/
theorem R_BIBO_extended : R_BIBO (extended W σ) = extended (R_BIBO W) (replaceLast σ) := by
  ext ⟨⟨⟨ai, ra⟩, ao⟩, ⟨⟨bi, rb⟩, bo⟩⟩ ⟨⟨⟨ai', ra'⟩, ao'⟩, ⟨⟨bi', rb'⟩, bo'⟩⟩
  simp only [R_BIBO_apply, extended_apply, replaceLast_apply, ptraceOut_apply,
    Fintype.sum_prod_type, Prod.mk.injEq]
  by_cases hb : bi = bi'
  · by_cases hr : rb = rb'
    · by_cases ho : bo = bo'
      · subst hb hr ho
        simp only [and_self, if_true]
        rw [invCard_prod_prod, mul_mul_mul_comm, Finset.sum_mul_sum]
        simp only [Finset.sum_mul]
      · simp [ho]
    · simp [hr]
  · simp [hb]

/-- The input partial trace factors through `σ`: `R_{A_I R_A A_O}(W ⊗ σ) = R_{A_I A_O} W ⊗ R_{R_A} σ`. -/
theorem R_AIAO_extended : R_AIAO (extended W σ) = extended (R_AIAO W) (replaceFst σ) := by
  ext ⟨⟨⟨ai, ra⟩, ao⟩, ⟨⟨bi, rb⟩, bo⟩⟩ ⟨⟨⟨ai', ra'⟩, ao'⟩, ⟨⟨bi', rb'⟩, bo'⟩⟩
  simp only [R_AIAO_apply, extended_apply, replaceFst_apply, Fintype.sum_prod_type,
    Prod.mk.injEq]
  by_cases ha : ai = ai'
  · by_cases hr : ra = ra'
    · by_cases ho : ao = ao'
      · subst ha hr ho
        simp only [and_self, if_true]
        rw [invCard_prod_prod, mul_mul_mul_comm, Finset.sum_mul_sum]
        simp only [Finset.sum_mul]
      · simp [ho]
    · simp [hr]
  · simp [ha]

end Extended

end

end CausalNonpurifiability
