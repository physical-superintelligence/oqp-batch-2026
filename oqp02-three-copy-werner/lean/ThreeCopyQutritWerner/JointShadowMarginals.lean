module

public import ThreeCopyQutritWerner.JointShadowPhysical

@[expose] public section


/-!
# The actual logical-plus-site marginal defect

The common logical register is retained, without changing the source columns.
The defect is the sum of squared differences of the three literal joint
marginals. Its invariant identity requires no balanced-Gram premise. Tracing
the logical register costs its dimension; for two columns this gives `B₀ ≤ 2b`.
-/

noncomputable section

open scoped BigOperators Matrix ComplexConjugate

namespace ThreeCopyQutritWerner

section Bipartite

variable {u v : Type*} [Fintype u] [Fintype v]

/-- Complementary pure-state contraction, in the orientation retaining the
second grouped subsystem. -/
theorem jointShadow_complementary_overlap (x y : u × v → ℂ) :
    (hsInner (ptraceL (ketBra x x)) (ptraceL (ketBra y y))).re =
      frobSq (ptraceR (ketBra x y)) := by
  rw [← zeroReserve_hsInner_self_re, hsInner_ptraceR_ketBra_cross,
    hsInner_re_comm]

/-- Equality of the two complementary purities of a literal pure vector. -/
theorem jointShadow_complementary_purity (x : u × v → ℂ) :
    frobSq (ptraceL (ketBra x x)) = frobSq (ptraceR (ketBra x x)) := by
  simpa only [zeroReserve_hsInner_self_re] using
    jointShadow_complementary_overlap x x

/-- The squared difference of the retained marginals is a transition-norm
polarization on the complementary subsystem. -/
theorem jointShadow_complementary_defect (x y : u × v → ℂ) :
    frobSq (ptraceL (ketBra x x) - ptraceL (ketBra y y)) =
      frobSq (ptraceR (ketBra x x)) + frobSq (ptraceR (ketBra y y)) -
        2 * frobSq (ptraceR (ketBra x y)) := by
  rw [frobSq_sub, jointShadow_complementary_purity,
    jointShadow_complementary_purity, jointShadow_complementary_overlap]

/-- Dimension-dependent Frobenius contraction under an unnormalized partial
trace. This applies to every complex matrix, including non-Hermitian ones. -/
theorem jointShadow_ptraceL_frobSq_le (Z : Matrix (u × v) (u × v) ℂ) :
    frobSq (ptraceL Z) ≤ (Fintype.card u : ℝ) * frobSq Z := by
  classical
  have hentry (r s : v) : Complex.normSq (∑ i, Z (i, r) (i, s)) ≤
      (Fintype.card u : ℝ) * ∑ i, ∑ j, Complex.normSq (Z (i, r) (j, s)) := by
    have hc := normSq_sum_mul_le Finset.univ (fun _ : u => (1 : ℂ))
      (fun i => Z (i, r) (i, s))
    have hc' : Complex.normSq (∑ i, Z (i, r) (i, s)) ≤
        (Fintype.card u : ℝ) * ∑ i, Complex.normSq (Z (i, r) (i, s)) := by
      simpa using hc
    refine hc'.trans (mul_le_mul_of_nonneg_left ?_ (Nat.cast_nonneg _))
    exact Finset.sum_le_sum fun i _ =>
      Finset.single_le_sum (fun j _ => Complex.normSq_nonneg (Z (i, r) (j, s)))
        (Finset.mem_univ i)
  have hsum : (∑ r, ∑ s, ∑ i, ∑ j, Complex.normSq (Z (i, r) (j, s))) =
      frobSq Z := by
    unfold frobSq
    simp only [Fintype.sum_prod_type]
    calc
      (∑ r, ∑ s, ∑ i, ∑ j, Complex.normSq (Z (i, r) (j, s))) =
          ∑ r, ∑ i, ∑ s, ∑ j, Complex.normSq (Z (i, r) (j, s)) :=
        Finset.sum_congr rfl fun _ _ => Finset.sum_comm
      _ = ∑ i, ∑ r, ∑ s, ∑ j, Complex.normSq (Z (i, r) (j, s)) :=
        Finset.sum_comm
      _ = ∑ i, ∑ r, ∑ j, ∑ s, Complex.normSq (Z (i, r) (j, s)) :=
        Finset.sum_congr rfl fun _ _ =>
          Finset.sum_congr rfl fun _ _ => Finset.sum_comm
  calc
    frobSq (ptraceL Z) ≤
        ∑ r, ∑ s, (Fintype.card u : ℝ) *
          ∑ i, ∑ j, Complex.normSq (Z (i, r) (j, s)) :=
      Finset.sum_le_sum fun r _ => Finset.sum_le_sum fun s _ => hentry r s
    _ = (Fintype.card u : ℝ) *
        (∑ r, ∑ s, ∑ i, ∑ j, Complex.normSq (Z (i, r) (j, s))) := by
      simp only [Finset.mul_sum]
    _ = (Fintype.card u : ℝ) * frobSq Z := by rw [hsum]

end Bipartite

section Marginals

variable {l a b c : Type*} [Fintype l] [Fintype a] [Fintype b] [Fintype c]

/-- Actual joint marginal on the original logical register and physical site A. -/
def jointShadowMarginalA (X : Matrix (a × b × c) l ℂ) : Matrix (l × a) (l × a) ℂ :=
  ptraceL (ketBra (jointShadowPurification X ∘ jointShadowSplitBC.symm)
    (jointShadowPurification X ∘ jointShadowSplitBC.symm))

/-- Actual joint marginal on the original logical register and physical site B. -/
def jointShadowMarginalB (X : Matrix (a × b × c) l ℂ) : Matrix (l × b) (l × b) ℂ :=
  ptraceL (ketBra (jointShadowPurification X ∘ jointShadowSplitAC.symm)
    (jointShadowPurification X ∘ jointShadowSplitAC.symm))

/-- Actual joint marginal on the original logical register and physical site C. -/
def jointShadowMarginalC (X : Matrix (a × b × c) l ℂ) : Matrix (l × c) (l × c) ℂ :=
  ptraceL (ketBra (jointShadowPurification X ∘ jointShadowSplitAB.symm)
    (jointShadowPurification X ∘ jointShadowSplitAB.symm))

/-- The manuscript's `b`: three actual common-register marginal differences. -/
def jointShadowMarginalDefect (X Y : Matrix (a × b × c) l ℂ) : ℝ :=
  frobSq (jointShadowMarginalA X - jointShadowMarginalA Y) +
    frobSq (jointShadowMarginalB X - jointShadowMarginalB Y) +
    frobSq (jointShadowMarginalC X - jointShadowMarginalC Y)

theorem jointShadowMarginalDefect_nonneg (X Y : Matrix (a × b × c) l ℂ) :
    0 ≤ jointShadowMarginalDefect X Y :=
  add_nonneg (add_nonneg (frobSq_nonneg _) (frobSq_nonneg _)) (frobSq_nonneg _)

/-- Exact identity of the logical-plus-A defect with the physical BC contractions. -/
theorem jointShadowMarginalA_defect (X Y : Matrix (a × b × c) l ℂ) :
    frobSq (jointShadowMarginalA X - jointShadowMarginalA Y) =
      frobSq (ptrace₁ (X * Xᴴ)) + frobSq (ptrace₁ (Y * Yᴴ)) -
        2 * frobSq (ptrace₁ (X * Yᴴ)) := by
  have h := jointShadow_complementary_defect
    (jointShadowPurification X ∘ jointShadowSplitBC.symm)
    (jointShadowPurification Y ∘ jointShadowSplitBC.symm)
  change frobSq (jointShadowMarginalA X - jointShadowMarginalA Y) =
    frobSq (jointShadowReduced jointShadowSplitBC X X) +
      frobSq (jointShadowReduced jointShadowSplitBC Y Y) -
        2 * frobSq (jointShadowReduced jointShadowSplitBC X Y) at h
  simpa only [jointShadowReduced_BC] using h

/-- Exact identity of the logical-plus-B defect with the physical AC contractions. -/
theorem jointShadowMarginalB_defect (X Y : Matrix (a × b × c) l ℂ) :
    frobSq (jointShadowMarginalB X - jointShadowMarginalB Y) =
      frobSq (ptrace₂ (X * Xᴴ)) + frobSq (ptrace₂ (Y * Yᴴ)) -
        2 * frobSq (ptrace₂ (X * Yᴴ)) := by
  have h := jointShadow_complementary_defect
    (jointShadowPurification X ∘ jointShadowSplitAC.symm)
    (jointShadowPurification Y ∘ jointShadowSplitAC.symm)
  change frobSq (jointShadowMarginalB X - jointShadowMarginalB Y) =
    frobSq (jointShadowReduced jointShadowSplitAC X X) +
      frobSq (jointShadowReduced jointShadowSplitAC Y Y) -
        2 * frobSq (jointShadowReduced jointShadowSplitAC X Y) at h
  simpa only [jointShadowReduced_AC] using h

/-- Exact identity of the logical-plus-C defect with the physical AB contractions. -/
theorem jointShadowMarginalC_defect (X Y : Matrix (a × b × c) l ℂ) :
    frobSq (jointShadowMarginalC X - jointShadowMarginalC Y) =
      frobSq (ptrace₃ (X * Xᴴ)) + frobSq (ptrace₃ (Y * Yᴴ)) -
        2 * frobSq (ptrace₃ (X * Yᴴ)) := by
  have h := jointShadow_complementary_defect
    (jointShadowPurification X ∘ jointShadowSplitAB.symm)
    (jointShadowPurification Y ∘ jointShadowSplitAB.symm)
  change frobSq (jointShadowMarginalC X - jointShadowMarginalC Y) =
    frobSq (jointShadowReduced jointShadowSplitAB X X) +
      frobSq (jointShadowReduced jointShadowSplitAB Y Y) -
        2 * frobSq (jointShadowReduced jointShadowSplitAB X Y) at h
  simpa only [jointShadowReduced_AB] using h

/-- The marginal definition of `b` agrees with the manuscript invariant formula,
without normalization or a balanced-Gram assumption. -/
theorem jointShadowMarginalDefect_eq_invA (X Y : Matrix (a × b × c) l ℂ) :
    jointShadowMarginalDefect X Y =
      invA (X * Xᴴ) + invA (Y * Yᴴ) - 2 * invA (X * Yᴴ) := by
  unfold jointShadowMarginalDefect
  rw [jointShadowMarginalA_defect, jointShadowMarginalB_defect,
    jointShadowMarginalC_defect]
  unfold invA
  ring

/-- Tracing precisely the original logical register leaves the actual A marginal. -/
theorem jointShadowMarginalA_ptraceL (X : Matrix (a × b × c) l ℂ) :
    ptraceL (jointShadowMarginalA X) = ptrace₂₃ (X * Xᴴ) := by
  ext i j
  simp only [jointShadowMarginalA, ptraceL, ketBra, jointShadowPurification,
    jointShadowSplitBC, Equiv.coe_fn_symm_mk, Function.comp_apply,
    Fintype.sum_prod_type, ptrace₂₃, Matrix.mul_apply, Matrix.conjTranspose_apply,
    Complex.star_def]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro k _
  rw [Finset.sum_comm]

/-- Tracing precisely the original logical register leaves the actual B marginal. -/
theorem jointShadowMarginalB_ptraceL (X : Matrix (a × b × c) l ℂ) :
    ptraceL (jointShadowMarginalB X) = ptrace₁₃ (X * Xᴴ) := by
  ext i j
  simp only [jointShadowMarginalB, ptraceL, ketBra, jointShadowPurification,
    jointShadowSplitAC, Equiv.coe_fn_symm_mk, Function.comp_apply,
    Fintype.sum_prod_type, ptrace₁₃, Matrix.mul_apply, Matrix.conjTranspose_apply,
    Complex.star_def]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro k _
  rw [Finset.sum_comm]

/-- Tracing precisely the original logical register leaves the actual C marginal. -/
theorem jointShadowMarginalC_ptraceL (X : Matrix (a × b × c) l ℂ) :
    ptraceL (jointShadowMarginalC X) = ptrace₁₂ (X * Xᴴ) := by
  ext i j
  simp only [jointShadowMarginalC, ptraceL, ketBra, jointShadowPurification,
    jointShadowSplitAB, Equiv.coe_fn_symm_mk, Function.comp_apply,
    Fintype.sum_prod_type, ptrace₁₂, Matrix.mul_apply, Matrix.conjTranspose_apply,
    Complex.star_def]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro k _
  rw [Finset.sum_comm]

/-- The faithful physical marginal difference is bounded by the joint defect
times the actual logical dimension. No balanced-Gram assumption is used. -/
theorem jointShadow_invB_sub_le_card_mul_defect (X Y : Matrix (a × b × c) l ℂ) :
    invB (X * Xᴴ - Y * Yᴴ) ≤ (Fintype.card l : ℝ) * jointShadowMarginalDefect X Y := by
  have hA := jointShadow_ptraceL_frobSq_le (jointShadowMarginalA X - jointShadowMarginalA Y)
  have hB := jointShadow_ptraceL_frobSq_le (jointShadowMarginalB X - jointShadowMarginalB Y)
  have hC := jointShadow_ptraceL_frobSq_le (jointShadowMarginalC X - jointShadowMarginalC Y)
  rw [ptraceL_sub, jointShadowMarginalA_ptraceL, jointShadowMarginalA_ptraceL] at hA
  rw [ptraceL_sub, jointShadowMarginalB_ptraceL, jointShadowMarginalB_ptraceL] at hB
  rw [ptraceL_sub, jointShadowMarginalC_ptraceL, jointShadowMarginalC_ptraceL] at hC
  have h₁₂ : ptrace₁₂ (X * Xᴴ - Y * Yᴴ) =
      ptrace₁₂ (X * Xᴴ) - ptrace₁₂ (Y * Yᴴ) := by
    ext i j
    simp only [ptrace₁₂, Matrix.sub_apply, Finset.sum_sub_distrib]
  have h₁₃ : ptrace₁₃ (X * Xᴴ - Y * Yᴴ) =
      ptrace₁₃ (X * Xᴴ) - ptrace₁₃ (Y * Yᴴ) := by
    ext i j
    simp only [ptrace₁₃, Matrix.sub_apply, Finset.sum_sub_distrib]
  have h₂₃ : ptrace₂₃ (X * Xᴴ - Y * Yᴴ) =
      ptrace₂₃ (X * Xᴴ) - ptrace₂₃ (Y * Yᴴ) := by
    ext i j
    simp only [ptrace₂₃, Matrix.sub_apply, Finset.sum_sub_distrib]
  unfold invB jointShadowMarginalDefect
  rw [h₁₂, h₁₃, h₂₃]
  nlinarith [hA, hB, hC]

/-- The manuscript's two-column estimate `B₀ ≤ 2b`, for the literal common
four-register purification and the actual difference `XX†−YY†`. -/
theorem jointShadow_invB_sub_le_two_mul_defect (X Y : Matrix (a × b × c) (Fin 2) ℂ) :
    invB (X * Xᴴ - Y * Yᴴ) ≤ 2 * jointShadowMarginalDefect X Y := by
  simpa only [Fintype.card_fin, Nat.cast_ofNat] using
    jointShadow_invB_sub_le_card_mul_defect X Y

end Marginals

end ThreeCopyQutritWerner
