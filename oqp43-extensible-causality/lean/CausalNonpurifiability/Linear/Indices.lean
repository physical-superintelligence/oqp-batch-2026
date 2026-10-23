module

public import Mathlib

@[expose] public section


/-!
# `CausalNonpurifiability.Linear.Indices`

Port dimensions, party-grouped laboratory indices in the physical order
`A_I, A_O, B_I, B_O` (generic finite factors `LabIdx AI AO BI BO`, and the
`Fin`-coordinate instance `LabIndex D`), named coordinate equivalences that single out
one factor (or one group of factors) for partial traces and replacement maps, the
ancilla-extension regrouping `eqExt`, and the flat equivalence
`labFlat : LabIndex qubits ≃ Fin 16` with `((α,o),(β,t)) ↦ 8α+4o+2β+t`
(the four-qubit flat index `8i+4o+2j+t` of Appendix C), used only for
certificate comparison.

Manuscript anchors: §2.1 tensor order `A_I, A_O, B_I, B_O`; `eq:QC` (factors brought to this
order); the flat index of Appendix C. Partial traces are the usual entrywise
ones, summing `T_{(u,w),(v,w)}` over the common index `w` with the remaining indices in their
original order; the manuscript does not number this convention.

Conventions: foundational lemmas are generic in the finite index types;
`Valid D` etc. are their `Fin`-coordinate interface.  Indices are never flattened inside
the development; `Fin 16` appears only through `labFlat`.
-/

set_option autoImplicit false

namespace CausalNonpurifiability

/-- Port dimensions `(m, d, n, e) = (dim A_I, dim A_O, dim B_I, dim B_O)`, all positive
(§2.1). -/
structure Ports where
  m : ℕ
  d : ℕ
  n : ℕ
  e : ℕ
  positive : 0 < m ∧ 0 < d ∧ 0 < n ∧ 0 < e

/-- Operators on a finite-dimensional space with a fixed basis indexed by `ι`. -/
abbrev Op (ι : Type) := Matrix ι ι ℂ

/-- Generic laboratory index in the physical tensor order `A_I, A_O, B_I, B_O`,
party-grouped: `((a, o), (b, t))`. -/
abbrev LabIdx (AI AO BI BO : Type) := (AI × AO) × (BI × BO)

/-- Laboratory index of the port configuration `D`: `LabIdx (Fin m) (Fin d) (Fin n) (Fin e)`. -/
abbrev LabIndex (D : Ports) := (Fin D.m × Fin D.d) × (Fin D.n × Fin D.e)

/-- Process-matrix carrier: operators on `A_I ⊗ A_O ⊗ B_I ⊗ B_O`. -/
abbrev PMat (D : Ports) := Op (LabIndex D)

/-- All four ports at least two-dimensional (the regime of the uniform construction). -/
def AllPortsGE2 (D : Ports) : Prop := 2 ≤ D.m ∧ 2 ≤ D.d ∧ 2 ≤ D.n ∧ 2 ≤ D.e

/-- The four-qubit port configuration `(2, 2, 2, 2)` of the kernel example. -/
def qubits : Ports := ⟨2, 2, 2, 2, by decide⟩

@[simp] theorem qubits_m : qubits.m = 2 := rfl
@[simp] theorem qubits_d : qubits.d = 2 := rfl
@[simp] theorem qubits_n : qubits.n = 2 := rfl
@[simp] theorem qubits_e : qubits.e = 2 := rfl

namespace Ports

variable (D : Ports)

theorem m_pos : 0 < D.m := D.positive.1
theorem d_pos : 0 < D.d := D.positive.2.1
theorem n_pos : 0 < D.n := D.positive.2.2.1
theorem e_pos : 0 < D.e := D.positive.2.2.2

theorem m_ne_zero : D.m ≠ 0 := D.m_pos.ne'
theorem d_ne_zero : D.d ≠ 0 := D.d_pos.ne'
theorem n_ne_zero : D.n ≠ 0 := D.n_pos.ne'
theorem e_ne_zero : D.e ≠ 0 := D.e_pos.ne'

instance nonempty_m : Nonempty (Fin D.m) := ⟨⟨0, D.m_pos⟩⟩
instance nonempty_d : Nonempty (Fin D.d) := ⟨⟨0, D.d_pos⟩⟩
instance nonempty_n : Nonempty (Fin D.n) := ⟨⟨0, D.n_pos⟩⟩
instance nonempty_e : Nonempty (Fin D.e) := ⟨⟨0, D.e_pos⟩⟩

end Ports

/-! ### Coordinate equivalences singling out a factor

Each `eqY : LabIdx AI AO BI BO ≃ I × Y` moves the factor(s) `Y` to the last position and
keeps the remaining indices in their original order (the entrywise convention above); `ptraceOut` on the
reindexed operator is then `Tr_Y`, and `replaceVia eqY` is `R_Y` (`eq:replacement`). -/

section Coordinates

variable (AI AO BI BO : Type)

/-- Single out `A_O`: `((a,o),(b,t)) ↦ ((a,(b,t)), o)`. -/
def eqAO : LabIdx AI AO BI BO ≃ (AI × (BI × BO)) × AO where
  toFun x := ((x.1.1, x.2), x.1.2)
  invFun y := ((y.1.1, y.2), y.1.2)
  left_inv := fun ⟨⟨_, _⟩, ⟨_, _⟩⟩ => rfl
  right_inv := fun ⟨⟨_, ⟨_, _⟩⟩, _⟩ => rfl

/-- Single out `B_O`: `((a,o),(b,t)) ↦ (((a,o),b), t)`. -/
def eqBO : LabIdx AI AO BI BO ≃ ((AI × AO) × BI) × BO where
  toFun x := ((x.1, x.2.1), x.2.2)
  invFun y := (y.1.1, (y.1.2, y.2))
  left_inv := fun ⟨⟨_, _⟩, ⟨_, _⟩⟩ => rfl
  right_inv := fun ⟨⟨⟨_, _⟩, _⟩, _⟩ => rfl

/-- Single out `B_I B_O` (already last): the identity regrouping. -/
def eqBIBO : LabIdx AI AO BI BO ≃ (AI × AO) × (BI × BO) where
  toFun x := x
  invFun y := y
  left_inv := fun _ => rfl
  right_inv := fun _ => rfl

/-- Single out `A_I A_O`: `((a,o),(b,t)) ↦ ((b,t),(a,o))`. -/
def eqAIAO : LabIdx AI AO BI BO ≃ (BI × BO) × (AI × AO) where
  toFun x := (x.2, x.1)
  invFun y := (y.2, y.1)
  left_inv := fun ⟨⟨_, _⟩, ⟨_, _⟩⟩ => rfl
  right_inv := fun ⟨⟨_, _⟩, ⟨_, _⟩⟩ => rfl

/-- Keep `A_I` first, everything else last: `((a,o),(b,t)) ↦ (a, (o,(b,t)))`
(for `Tr_{A_O B_I B_O}`, `eq:ordered-marginal`). -/
def eqAI : LabIdx AI AO BI BO ≃ AI × (AO × (BI × BO)) where
  toFun x := (x.1.1, (x.1.2, x.2))
  invFun y := ((y.1, y.2.1), y.2.2)
  left_inv := fun ⟨⟨_, _⟩, ⟨_, _⟩⟩ => rfl
  right_inv := fun ⟨_, ⟨_, ⟨_, _⟩⟩⟩ => rfl

/-- Keep `B_I` first, everything else last: `((a,o),(b,t)) ↦ (b, ((a,o),t))`
(for `Tr_{A_I A_O B_O}`, `omega_B`). -/
def eqBI : LabIdx AI AO BI BO ≃ BI × ((AI × AO) × BO) where
  toFun x := (x.2.1, (x.1, x.2.2))
  invFun y := (y.2.1, (y.1, y.2.2))
  left_inv := fun ⟨⟨_, _⟩, ⟨_, _⟩⟩ => rfl
  right_inv := fun ⟨_, ⟨⟨_, _⟩, _⟩⟩ => rfl

/-- Input/output regrouping of `eq:QC`:
`((a,b),(o,t)) ↦ ((a,o),(b,t))`, so that `Q_C = reindex eqQC (C ⊗ I_{A_O B_O})`. -/
def eqQC : (AI × BI) × (AO × BO) ≃ LabIdx AI AO BI BO where
  toFun x := ((x.1.1, x.2.1), (x.1.2, x.2.2))
  invFun y := ((y.1.1, y.2.1), (y.1.2, y.2.2))
  left_inv := fun ⟨⟨_, _⟩, ⟨_, _⟩⟩ => rfl
  right_inv := fun ⟨⟨_, _⟩, ⟨_, _⟩⟩ => rfl

/-- Ancilla extension: `(((a,o),(b,t)),(r,s)) ↦ (((a,r),o),((b,s),t))`
(`W ⊗ σ` in the enlarged-input party-grouped order). -/
def eqExt (RA RB : Type) : LabIdx AI AO BI BO × (RA × RB) ≃ LabIdx (AI × RA) AO (BI × RB) BO where
  toFun x := (((x.1.1.1, x.2.1), x.1.1.2), ((x.1.2.1, x.2.2), x.1.2.2))
  invFun y := (((y.1.1.1, y.1.2), (y.2.1.1, y.2.2)), (y.1.1.2, y.2.1.2))
  left_inv := fun ⟨⟨⟨_, _⟩, ⟨_, _⟩⟩, ⟨_, _⟩⟩ => rfl
  right_inv := fun ⟨⟨⟨_, _⟩, _⟩, ⟨⟨_, _⟩, _⟩⟩ => rfl

variable {AI AO BI BO}

@[simp] theorem eqAO_apply (x : LabIdx AI AO BI BO) :
    eqAO AI AO BI BO x = ((x.1.1, x.2), x.1.2) := rfl
@[simp] theorem eqAO_symm_apply (y : (AI × (BI × BO)) × AO) :
    (eqAO AI AO BI BO).symm y = ((y.1.1, y.2), y.1.2) := rfl
@[simp] theorem eqBO_apply (x : LabIdx AI AO BI BO) :
    eqBO AI AO BI BO x = ((x.1, x.2.1), x.2.2) := rfl
@[simp] theorem eqBO_symm_apply (y : ((AI × AO) × BI) × BO) :
    (eqBO AI AO BI BO).symm y = (y.1.1, (y.1.2, y.2)) := rfl
@[simp] theorem eqBIBO_apply (x : LabIdx AI AO BI BO) : eqBIBO AI AO BI BO x = x := rfl
@[simp] theorem eqBIBO_symm_apply (y : (AI × AO) × (BI × BO)) :
    (eqBIBO AI AO BI BO).symm y = y := rfl
@[simp] theorem eqAIAO_apply (x : LabIdx AI AO BI BO) : eqAIAO AI AO BI BO x = (x.2, x.1) := rfl
@[simp] theorem eqAIAO_symm_apply (y : (BI × BO) × (AI × AO)) :
    (eqAIAO AI AO BI BO).symm y = (y.2, y.1) := rfl
@[simp] theorem eqAI_apply (x : LabIdx AI AO BI BO) :
    eqAI AI AO BI BO x = (x.1.1, (x.1.2, x.2)) := rfl
@[simp] theorem eqAI_symm_apply (y : AI × (AO × (BI × BO))) :
    (eqAI AI AO BI BO).symm y = ((y.1, y.2.1), y.2.2) := rfl
@[simp] theorem eqBI_apply (x : LabIdx AI AO BI BO) :
    eqBI AI AO BI BO x = (x.2.1, (x.1, x.2.2)) := rfl
@[simp] theorem eqBI_symm_apply (y : BI × ((AI × AO) × BO)) :
    (eqBI AI AO BI BO).symm y = (y.2.1, (y.1, y.2.2)) := rfl
@[simp] theorem eqQC_apply (x : (AI × BI) × (AO × BO)) :
    eqQC AI AO BI BO x = ((x.1.1, x.2.1), (x.1.2, x.2.2)) := rfl
@[simp] theorem eqQC_symm_apply (y : LabIdx AI AO BI BO) :
    (eqQC AI AO BI BO).symm y = ((y.1.1, y.2.1), (y.1.2, y.2.2)) := rfl
@[simp] theorem eqExt_apply (RA RB : Type) (x : LabIdx AI AO BI BO × (RA × RB)) :
    eqExt AI AO BI BO RA RB x = (((x.1.1.1, x.2.1), x.1.1.2), ((x.1.2.1, x.2.2), x.1.2.2)) := rfl
@[simp] theorem eqExt_symm_apply (RA RB : Type) (y : LabIdx (AI × RA) AO (BI × RB) BO) :
    (eqExt AI AO BI BO RA RB).symm y =
      (((y.1.1.1, y.1.2), (y.2.1.1, y.2.2)), (y.1.1.2, y.2.1.2)) := rfl

end Coordinates

/-- Flat index of the four-qubit laboratory: `((α,o),(β,t)) ↦ 8α + 4o + 2β + t`
(Appendix C: `8i+4o+2j+t` for four qubits). -/
def labFlat : LabIndex qubits ≃ Fin 16 :=
  ((finProdFinEquiv : Fin 2 × Fin 2 ≃ Fin 4).prodCongr
      (finProdFinEquiv : Fin 2 × Fin 2 ≃ Fin 4)).trans
    (finProdFinEquiv : Fin 4 × Fin 4 ≃ Fin 16)

theorem labFlat_apply (α o β t : Fin 2) :
    (labFlat ((α, o), (β, t)) : ℕ) = 8 * α + 4 * o + 2 * β + t := by
  revert α o β t
  decide

/-- Alias of `labFlat` (an earlier name). -/
abbrev flatQubit : LabIndex qubits ≃ Fin 16 := labFlat

end CausalNonpurifiability
