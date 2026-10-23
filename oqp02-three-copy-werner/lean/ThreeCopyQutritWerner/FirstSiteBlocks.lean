module

public import ThreeCopyQutritWerner.TwoCutMain

@[expose] public section


/-!
# Literal first-site blocks of the original endpoint form

The endpoint energy is the sum of the two-site cut forms of all first-site
blocks, minus half the cut form of their diagonal sum. These identities
retain the original unnormalized partial traces and arbitrary finite local
dimensions. They do not assume endpoint nonnegativity or classify zeros.
-/

noncomputable section

open scoped BigOperators Matrix

namespace ThreeCopyQutritWerner

/-- The actual row/column block at one physical site. -/
def firstSiteBlock {a d : Type*} (C : Matrix (a × d) (a × d) ℂ) (i j : a) :
    Matrix d d ℂ := C.submatrix (fun r => (i, r)) (fun s => (j, s))

/-- Block extraction cannot increase the rank of the original matrix. -/
theorem firstSiteBlock_rank_le {a d : Type*} [Fintype a] [Fintype d]
    (C : Matrix (a × d) (a × d) ℂ) (i j : a) :
    (firstSiteBlock C i j).rank ≤ C.rank :=
  Matrix.rank_submatrix_le C _ _

/-- Frobenius norm is the sum over the literal physical blocks. -/
theorem frobSq_eq_sum_firstSiteBlocks {a d : Type*} [Fintype a] [Fintype d]
    (C : Matrix (a × d) (a × d) ℂ) :
    frobSq C = ∑ i, ∑ j, frobSq (firstSiteBlock C i j) := by
  simp only [frobSq, firstSiteBlock, Matrix.submatrix_apply, Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro i _
  exact Finset.sum_comm

variable {a b c : Type*} [Fintype a] [Fintype b] [Fintype c]

/-- The first partial trace is the ordinary sum of diagonal blocks. -/
theorem ptrace₁_eq_sum_firstSiteBlocks
    (C : Matrix (a × b × c) (a × b × c) ℂ) :
    ptrace₁ C = ∑ i, firstSiteBlock C i i := by
  ext r s
  simp only [ptrace₁, firstSiteBlock, Matrix.sum_apply, Matrix.submatrix_apply]

/-- The two remaining single-site partial traces are taken inside each block. -/
theorem firstSiteBlock_ptrace₂
    (C : Matrix (a × b × c) (a × b × c) ℂ) (i j : a) :
    firstSiteBlock (ptrace₂ C) i j = ptraceL (firstSiteBlock C i j) := rfl

theorem firstSiteBlock_ptrace₃
    (C : Matrix (a × b × c) (a × b × c) ℂ) (i j : a) :
    firstSiteBlock (ptrace₃ C) i j = ptraceR (firstSiteBlock C i j) := rfl

/-- Tracing the other two sites gives the trace of each original block. -/
theorem ptrace₂₃_eq_firstSiteBlock_trace
    (C : Matrix (a × b × c) (a × b × c) ℂ) (i j : a) :
    ptrace₂₃ C i j = (firstSiteBlock C i j).trace := by
  simp only [ptrace₂₃, Matrix.trace, Matrix.diag_apply, firstSiteBlock,
    Matrix.submatrix_apply, Fintype.sum_prod_type]

/-- Both successive partial traces retain the original physical site ordering. -/
theorem firstSiteBlocks_successive_traces
    (C : Matrix (a × b × c) (a × b × c) ℂ) :
    ptraceL (ptrace₁ C) = ptrace₁₂ C ∧
      ptraceR (ptrace₁ C) = ptrace₁₃ C ∧ (ptrace₁ C).trace = C.trace := by
  constructor
  · ext r s
    simp only [ptraceL, ptrace₁, ptrace₁₂]
    exact Finset.sum_comm
  constructor
  · ext r s
    simp only [ptraceR, ptrace₁, ptrace₁₃]
    exact Finset.sum_comm
  · simp only [Matrix.trace, Matrix.diag_apply, ptrace₁]
    calc
      _ = ∑ i : a, ∑ p : b × c, C (i, p) (i, p) := Finset.sum_comm
      _ = _ := (Fintype.sum_prod_type (fun p : a × b × c => C p p)).symm

/-- Exact block decomposition of the original three-site endpoint form. -/
theorem endpointEnergy_eq_sum_firstSiteBlock_cutForm
    (C : Matrix (a × b × c) (a × b × c) ℂ) :
    endpointEnergy C = (∑ i, ∑ j, cutForm (firstSiteBlock C i j)) -
      cutForm (ptrace₁ C) / 2 := by
  obtain ⟨h12, h13, ht⟩ := firstSiteBlocks_successive_traces C
  have hN := frobSq_eq_sum_firstSiteBlocks C
  have h2 := frobSq_eq_sum_firstSiteBlocks (ptrace₂ C)
  have h3 := frobSq_eq_sum_firstSiteBlocks (ptrace₃ C)
  simp only [firstSiteBlock_ptrace₂] at h2
  simp only [firstSiteBlock_ptrace₃] at h3
  have h23 : frobSq (ptrace₂₃ C) =
      ∑ i, ∑ j, Complex.normSq (firstSiteBlock C i j).trace := by
    simp only [frobSq, ptrace₂₃_eq_firstSiteBlock_trace]
  simp only [endpointEnergy, energy, invN, invA, invB, invT, cutForm,
    Finset.sum_sub_distrib, Finset.sum_add_distrib, ← Finset.sum_div,
    h12, h13, ht, ← hN, ← h2, ← h3, ← h23]
  ring

/-- Every individual block satisfies the proved two-copy inequality. -/
theorem firstSiteBlock_cutForm_nonneg [DecidableEq b] [DecidableEq c]
    (C : Matrix (a × b × c) (a × b × c) ℂ) (hC : C.rank ≤ 2) (i j : a) :
    0 ≤ cutForm (firstSiteBlock C i j) :=
  cutForm_nonneg_of_rank_le_two _ ((firstSiteBlock_rank_le C i j).trans hC)

end ThreeCopyQutritWerner
