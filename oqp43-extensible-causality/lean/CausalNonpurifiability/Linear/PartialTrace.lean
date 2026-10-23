module

public import CausalNonpurifiability.Linear.Indices

@[expose] public section


/-!
# `CausalNonpurifiability.Linear.PartialTrace`

Entrywise partial traces on product index types and their contraction identities.

`ptraceOut T i j = ∑ o, T (i, o) (j, o)` traces out the *second* factor, keeping the
remaining index in its original position — the usual entrywise convention, summing
`T_{(u,w),(v,w)}` over the common index `w` (the manuscript does not number it).  Partial traces over other factors are
obtained by first reindexing with the coordinate equivalences of `CausalNonpurifiability.Linear.Indices`
(`ptraceFst` is the `Equiv.prodComm` instance).

Manuscript anchors: `eq:replacement` (the `Tr_Y` it contains), `eq:choi` normalization `Tr_{A_O} ∑ₐ M_{a|x} = I_{A_I}`.
-/

set_option autoImplicit false

open scoped Kronecker Matrix ComplexOrder

namespace CausalNonpurifiability

section PartialTrace

variable {I O : Type} [Fintype O]

/-- Partial trace over the second (output) factor, by entries (entrywise convention). -/
def ptraceOut (T : Op (I × O)) : Op I := fun i j => ∑ o, T (i, o) (j, o)

theorem ptraceOut_apply (T : Op (I × O)) (i j : I) :
    ptraceOut T i j = ∑ o, T (i, o) (j, o) := rfl

theorem ptraceOut_add (S T : Op (I × O)) : ptraceOut (S + T) = ptraceOut S + ptraceOut T := by
  ext i j
  simp only [ptraceOut_apply, Matrix.add_apply, Finset.sum_add_distrib]

theorem ptraceOut_smul (c : ℂ) (T : Op (I × O)) : ptraceOut (c • T) = c • ptraceOut T := by
  ext i j
  simp only [ptraceOut_apply, Matrix.smul_apply, smul_eq_mul, Finset.mul_sum]

theorem ptraceOut_zero : ptraceOut (0 : Op (I × O)) = 0 := by
  ext i j
  simp only [ptraceOut_apply, Matrix.zero_apply, Finset.sum_const_zero]

theorem ptraceOut_sub (S T : Op (I × O)) : ptraceOut (S - T) = ptraceOut S - ptraceOut T := by
  ext i j
  simp only [ptraceOut_apply, Matrix.sub_apply, Finset.sum_sub_distrib]

theorem ptraceOut_neg (T : Op (I × O)) : ptraceOut (-T) = -ptraceOut T := by
  ext i j
  simp only [ptraceOut_apply, Matrix.neg_apply, Finset.sum_neg_distrib]

/-- `ptraceOut` as a `ℂ`-linear map. -/
def ptraceOutₗ : Op (I × O) →ₗ[ℂ] Op I where
  toFun := ptraceOut
  map_add' := ptraceOut_add
  map_smul' := ptraceOut_smul

@[simp] theorem ptraceOutₗ_apply (T : Op (I × O)) : ptraceOutₗ T = ptraceOut T := rfl

theorem ptraceOut_conjTranspose (T : Op (I × O)) : ptraceOut Tᴴ = (ptraceOut T)ᴴ := by
  ext i j
  simp only [ptraceOut_apply, Matrix.conjTranspose_apply, star_sum]

theorem ptraceOut_isHermitian {T : Op (I × O)} (h : T.IsHermitian) :
    (ptraceOut T).IsHermitian := by
  show (ptraceOut T)ᴴ = ptraceOut T
  rw [← ptraceOut_conjTranspose, h.eq]

/-- Trace of the partial trace is the trace. -/
theorem trace_ptraceOut [Fintype I] (T : Op (I × O)) : (ptraceOut T).trace = T.trace := by
  simp only [Matrix.trace, Matrix.diag_apply, ptraceOut_apply, Fintype.sum_prod_type]

/-- Partial trace of a Kronecker product: `Tr_O (A ⊗ B) = (Tr B) • A`. -/
theorem ptraceOut_kronecker [Fintype I] (A : Op I) (B : Op O) :
    ptraceOut (A ⊗ₖ B) = B.trace • A := by
  ext i j
  simp only [ptraceOut_apply, Matrix.kroneckerMap_apply, Matrix.smul_apply, smul_eq_mul,
    Matrix.trace, Matrix.diag_apply, Finset.sum_mul]
  exact Finset.sum_congr rfl fun o _ => mul_comm _ _

/-- `Tr_O I = |O| • I`. -/
theorem ptraceOut_one [Fintype I] [DecidableEq I] [DecidableEq O] :
    ptraceOut (1 : Op (I × O)) = (Fintype.card O : ℂ) • (1 : Op I) := by
  rw [← Matrix.one_kronecker_one, ptraceOut_kronecker, Matrix.trace_one]

/-- The partial trace is a sum of principal submatrices, hence preserves positivity. -/
theorem ptraceOut_eq_sum_submatrix [Fintype I] (T : Op (I × O)) :
    ptraceOut T = ∑ o, T.submatrix (fun i => (i, o)) (fun i => (i, o)) := by
  ext i j
  simp only [ptraceOut_apply, Matrix.sum_apply, Matrix.submatrix_apply]

theorem ptraceOut_posSemidef [Fintype I] {T : Op (I × O)} (h : T.PosSemidef) :
    (ptraceOut T).PosSemidef := by
  rw [ptraceOut_eq_sum_submatrix]
  exact Finset.sum_induction _ _ (fun _ _ ha hb => ha.add hb) Matrix.PosSemidef.zero
    (fun o _ => h.submatrix _)

omit [Fintype O] in
/-- Partial trace over the *first* factor, via `Equiv.prodComm` reindexing:
`ptraceFst T o o' = ∑ i, T (i, o) (i, o')`. -/
def ptraceFst [Fintype I] (T : Op (I × O)) : Op O :=
  ptraceOut (Matrix.reindex (Equiv.prodComm I O) (Equiv.prodComm I O) T)

omit [Fintype O] in
theorem ptraceFst_apply [Fintype I] (T : Op (I × O)) (o o' : O) :
    ptraceFst T o o' = ∑ i, T (i, o) (i, o') := by
  simp [ptraceFst, ptraceOut_apply, Matrix.reindex_apply, Matrix.submatrix_apply]

end PartialTrace

/-! ### Reindexing helpers -/

section Reindex

variable {ι κ : Type}

theorem reindex_reindex_symm (e : ι ≃ κ) (M : Op κ) :
    Matrix.reindex e e (Matrix.reindex e.symm e.symm M) = M := by
  ext x y
  simp [Matrix.reindex_apply, Matrix.submatrix_apply]

theorem reindex_symm_reindex (e : ι ≃ κ) (M : Op ι) :
    Matrix.reindex e.symm e.symm (Matrix.reindex e e M) = M := by
  ext x y
  simp [Matrix.reindex_apply, Matrix.submatrix_apply]

end Reindex

end CausalNonpurifiability
