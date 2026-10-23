module

public import ThreeCopyQutritWerner.Corollaries
public import ThreeCopyQutritWerner.PPTRegion

@[expose] public section


/-!
# Section 3.1 identities, eq. (4) as `IsLeast`, and two small remarks

* eq. (10): if `P` is a Hermitian idempotent of trace 2 with `P C = C`, then
  `R(C) = ‖C - (Tr C / 2) P‖_F²` (`formR_eq_frobSq_sub_proj`);
* eq. (11), two-factor form: for an orthonormal pair `u₁, u₂` and `P = u₁u₁† + u₂u₂†`,
  `∑_{r,s} e(u_r, u_s) = 2 Q(P) = 6 - ‖Tr_L P‖_F² - ‖Tr_R P‖_F²`, where
  `e(u, v)` is `biDefect`, four times the squared norm of `u ⊗ v` antisymmetrized in the `L` and in
  the `R` parts of two replicas (`sum_biDefect_eq_two_mul_cutForm_proj`, `two_mul_cutForm_proj`);
  cut 1 is the case `L = a`, `R = b × c`; cuts 2 and 3 follow by
  regrouping (`sum_biDefect_eq_two_mul_cutForm₂/₃_proj`, `two_mul_cutForm₂/₃_proj`);
* eq. (4) at `d = 3` as an `IsLeast` statement, an implication from the endpoint inequality
  (`isLeast_energy_of_endpoint`); unlike the `sInf` form it cannot hold for a junk value;
* Corollary 2.2, PPT region: `(ρ^{⊗3})^Γ` is positive semidefinite for `α ≤ 1/3`
  (`partialTranspose_tripleCopy_werner_three_posSemidef`), the statement the `PPTRegion`
  docstrings describe;
* Section 1: tracing out one copy can increase the rank of the coefficient matrix
  (`exists_rank_le_two_rank_ptrace₁_eq_three`).
-/

noncomputable section

open scoped ComplexOrder Matrix

namespace ThreeCopyQutritWerner

section Defect

variable {L R : Type*} [Fintype L] [Fintype R]

/-- The Appendix A defect is symmetric: `e(u, v) = e(v, u)`. -/
theorem biDefect_comm (u v : L × R → ℂ) : biDefect u v = biDefect v u := by
  have h1 := four_mul_biDefect u v
  have h2 := four_mul_biDefect v u
  rw [biAnti_comm u v] at h1
  linarith

/-- Manuscript eq. (11), outer equality, two-factor form: for an orthonormal pair `u₁, u₂`,
`∑_{r,s} e(u_r, u_s) = 2 Q(u₁u₁† + u₂u₂†)`. -/
theorem sum_biDefect_eq_two_mul_cutForm_proj (u₁ u₂ : L × R → ℂ) (h1 : vecNormSq u₁ = 1)
    (h2 : vecNormSq u₂ = 1) (h12 : braket u₁ u₂ = 0) :
    biDefect u₁ u₁ + biDefect u₁ u₂ + biDefect u₂ u₁ + biDefect u₂ u₂ =
      2 * cutForm (ketBra u₁ u₁ + ketBra u₂ u₂) := by
  have hτ1 : braket u₁ u₁ = 1 := by rw [braket_self, h1, Complex.ofReal_one]
  have hτ2 : braket u₂ u₂ = 1 := by rw [braket_self, h2, Complex.ofReal_one]
  have key := cutForm_ketBra_add u₁ u₂ u₁ u₂ 1 1 0 1 h1 h1 h2 h2 h12 h12 hτ1 hτ2
  have hz : ptraceNormSq (ketBra u₂ u₁ - ketBra u₂ u₁) = 0 := by
    rw [sub_self]
    simp [ptraceNormSq, ptraceL, ptraceR, frobSq]
  have key' : cutForm (ketBra u₁ u₁ + ketBra u₂ u₂) =
      (biDefect u₁ u₁ + biDefect u₂ u₂ + biDefect u₂ u₁ + biDefect u₂ u₁) / 2 := by
    rw [key, hz, Complex.normSq_zero]
    ring
  have hc := biDefect_comm u₁ u₂
  linarith

/-- Manuscript eq. (11), middle expression: `2 Q(P) = 6 - ‖Tr_L P‖_F² - ‖Tr_R P‖_F²` for the
projector `P = u₁u₁† + u₂u₂†` onto an orthonormal pair. -/
theorem two_mul_cutForm_proj (u₁ u₂ : L × R → ℂ) (h1 : vecNormSq u₁ = 1)
    (h2 : vecNormSq u₂ = 1) (h12 : braket u₁ u₂ = 0) :
    2 * cutForm (ketBra u₁ u₁ + ketBra u₂ u₂) =
      6 - frobSq (ptraceL (ketBra u₁ u₁ + ketBra u₂ u₂)) -
        frobSq (ptraceR (ketBra u₁ u₁ + ketBra u₂ u₂)) := by
  unfold cutForm
  rw [frobSq_proj u₁ u₂ h1 h2 h12, trace_proj u₁ u₂ h1 h2, normSq_two_complex]
  ring

end Defect

section Projection

variable {ι : Type*} [Fintype ι]

/-- `⟨A, B⟩ = Tr(A† B)`. -/
theorem hsInner_eq_trace (A B : Matrix ι ι ℂ) : hsInner A B = (Aᴴ * B).trace := by
  unfold hsInner
  rw [Finset.sum_comm]
  simp only [Matrix.trace, Matrix.diag_apply, Matrix.mul_apply, Matrix.conjTranspose_apply,
    starRingEnd_apply]

/-- `‖M‖_F² = Re Tr(M† M)`. -/
theorem frobSq_eq_re_trace (M : Matrix ι ι ℂ) : frobSq M = ((Mᴴ * M).trace).re := by
  rw [← hsInner_eq_trace, hsInner_re]
  unfold frobSq
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [Complex.mul_re, Complex.conj_re, Complex.conj_im, Complex.normSq_apply]
  ring

end Projection

section OtherCuts

variable {a b c : Type*} [Fintype a] [Fintype b] [Fintype c]

/-- Manuscript eq. (11) at the cut `2 | 13`: with the vectors regrouped on `b × (a × c)`,
`∑_{r,s} e(u_r, u_s) = 2 Q₂(P)`. -/
theorem sum_biDefect_eq_two_mul_cutForm₂_proj (u₁ u₂ : a × b × c → ℂ) (h1 : vecNormSq u₁ = 1)
    (h2 : vecNormSq u₂ = 1) (h12 : braket u₁ u₂ = 0) :
    biDefect (fun q => u₁ (siteEquiv₂ q)) (fun q => u₁ (siteEquiv₂ q)) +
        biDefect (fun q => u₁ (siteEquiv₂ q)) (fun q => u₂ (siteEquiv₂ q)) +
        biDefect (fun q => u₂ (siteEquiv₂ q)) (fun q => u₁ (siteEquiv₂ q)) +
        biDefect (fun q => u₂ (siteEquiv₂ q)) (fun q => u₂ (siteEquiv₂ q)) =
      2 * cutForm₂ (ketBra u₁ u₁ + ketBra u₂ u₂) := by
  rw [cutForm₂_eq_cutForm, submatrix_ketBra_add]
  exact sum_biDefect_eq_two_mul_cutForm_proj _ _ ((vecNormSq_comp_equiv siteEquiv₂ u₁).trans h1)
    ((vecNormSq_comp_equiv siteEquiv₂ u₂).trans h2) ((braket_comp_equiv siteEquiv₂ u₁ u₂).trans h12)

/-- Manuscript eq. (11) at the cut `3 | 12`: with the vectors regrouped on `c × (a × b)`,
`∑_{r,s} e(u_r, u_s) = 2 Q₃(P)`. -/
theorem sum_biDefect_eq_two_mul_cutForm₃_proj (u₁ u₂ : a × b × c → ℂ) (h1 : vecNormSq u₁ = 1)
    (h2 : vecNormSq u₂ = 1) (h12 : braket u₁ u₂ = 0) :
    biDefect (fun q => u₁ (siteEquiv₃ q)) (fun q => u₁ (siteEquiv₃ q)) +
        biDefect (fun q => u₁ (siteEquiv₃ q)) (fun q => u₂ (siteEquiv₃ q)) +
        biDefect (fun q => u₂ (siteEquiv₃ q)) (fun q => u₁ (siteEquiv₃ q)) +
        biDefect (fun q => u₂ (siteEquiv₃ q)) (fun q => u₂ (siteEquiv₃ q)) =
      2 * cutForm₃ (ketBra u₁ u₁ + ketBra u₂ u₂) := by
  rw [cutForm₃_eq_cutForm, submatrix_ketBra_add]
  exact sum_biDefect_eq_two_mul_cutForm_proj _ _ ((vecNormSq_comp_equiv siteEquiv₃ u₁).trans h1)
    ((vecNormSq_comp_equiv siteEquiv₃ u₂).trans h2) ((braket_comp_equiv siteEquiv₃ u₁ u₂).trans h12)

/-- Manuscript eq. (11), middle expression at the cut `2 | 13`. -/
theorem two_mul_cutForm₂_proj (u₁ u₂ : a × b × c → ℂ) (h1 : vecNormSq u₁ = 1)
    (h2 : vecNormSq u₂ = 1) (h12 : braket u₁ u₂ = 0) :
    2 * cutForm₂ (ketBra u₁ u₁ + ketBra u₂ u₂) =
      6 - frobSq (ptrace₂ (ketBra u₁ u₁ + ketBra u₂ u₂)) -
        frobSq (ptrace₁₃ (ketBra u₁ u₁ + ketBra u₂ u₂)) := by
  unfold cutForm₂ invN invT
  rw [frobSq_proj u₁ u₂ h1 h2 h12, trace_proj u₁ u₂ h1 h2, normSq_two_complex]
  ring

/-- Manuscript eq. (11), middle expression at the cut `3 | 12`. -/
theorem two_mul_cutForm₃_proj (u₁ u₂ : a × b × c → ℂ) (h1 : vecNormSq u₁ = 1)
    (h2 : vecNormSq u₂ = 1) (h12 : braket u₁ u₂ = 0) :
    2 * cutForm₃ (ketBra u₁ u₁ + ketBra u₂ u₂) =
      6 - frobSq (ptrace₃ (ketBra u₁ u₁ + ketBra u₂ u₂)) -
        frobSq (ptrace₁₂ (ketBra u₁ u₁ + ketBra u₂ u₂)) := by
  unfold cutForm₃ invN invT
  rw [frobSq_proj u₁ u₂ h1 h2 h12, trace_proj u₁ u₂ h1 h2, normSq_two_complex]
  ring

end OtherCuts

/-- Manuscript eq. (10): if `P` is a Hermitian idempotent of trace 2 containing the range of
`C` (`P C = C`), then `R(C) = ‖C - (Tr C / 2) P‖_F²`, in any finite local dimensions. -/
theorem formR_eq_frobSq_sub_proj {a b c : Type*} [Fintype a] [Fintype b] [Fintype c]
    (C P : Matrix (a × b × c) (a × b × c) ℂ) (hP : P.IsHermitian) (hPP : P * P = P)
    (htr : P.trace = 2) (hPC : P * C = C) :
    formR C = frobSq (C - (C.trace / 2) • P) := by
  have hCP : Cᴴ * P = Cᴴ := by
    calc Cᴴ * P = Cᴴ * Pᴴ := by rw [hP.eq]
      _ = (P * C)ᴴ := (Matrix.conjTranspose_mul P C).symm
      _ = Cᴴ := by rw [hPC]
  have hPF : frobSq P = 2 := by
    have h := frobSq_eq_re_trace P
    rw [hP.eq, hPP, htr] at h
    simpa using h
  have hin : hsInner C ((C.trace / 2) • P) = C.trace / 2 * (starRingEnd ℂ) C.trace := by
    rw [hsInner_eq_trace, Matrix.mul_smul, Matrix.trace_smul, hCP, Matrix.trace_conjTranspose,
      smul_eq_mul] <;> rfl
  have h1 : Complex.normSq (C.trace / 2) = Complex.normSq C.trace / 4 := by
    rw [Complex.normSq_div, normSq_two_complex]
  have h2 : (C.trace / 2 * (starRingEnd ℂ) C.trace).re = Complex.normSq C.trace / 2 := by
    rw [Complex.mul_re, Complex.div_ofNat_re, Complex.div_ofNat_im, Complex.conj_re,
      Complex.conj_im, Complex.normSq_apply]
    ring
  rw [frobSq_sub, frobSq_smul, hPF, hin, h1, h2]
  unfold formR invN invT
  ring

/-- Manuscript eq. (4) at `d = 3`, `IsLeast` form, REDUCTION (hypothesis: the qutrit endpoint
inequality): for `0 ≤ α ≤ 1/2`, `f(α)` is the least value of `q_α` on normalized complex
27 × 27 matrices of rank at most two, and it is attained. -/
theorem isLeast_energy_of_endpoint (hq : QutritEndpointInequality) {α : ℝ} (h0 : 0 ≤ α)
    (h1 : α ≤ 1 / 2) :
    IsLeast {x : ℝ | ∃ C : Matrix (Fin 3 × Fin 3 × Fin 3) (Fin 3 × Fin 3 × Fin 3) ℂ,
      C.rank ≤ 2 ∧ invN C = 1 ∧ energy α C = x} (sharpCurve α) := by
  refine ⟨exists_rank_le_two_energy_eq_sharpCurve α, ?_⟩
  rintro x ⟨C, hC, hN, rfl⟩
  have h := sharpCurve_mul_invN_le_energy_of_endpointEnergy_nonneg C hC h0 h1 (hq C hC)
  rwa [hN, mul_one] at h

/-- For `α ≤ 1/3`, `(ρ_{3,α}^{⊗3})^Γ = (ρ_{3,α}^Γ)^{⊗3}` is positive semidefinite. -/
theorem partialTranspose_tripleCopy_werner_three_posSemidef {α : ℝ} (h : α ≤ 1 / 3) :
    (partialTranspose (tripleCopy (werner 3 α))).PosSemidef := by
  rw [partialTranspose_tripleCopy]
  exact tripleCopy_posSemidef (partialTranspose_werner_three_posSemidef h)

section RankRaise

/-- The witness for the Section 1 remark: `x = ∑ⱼ eⱼ ⊗ eⱼ ⊗ e₀`. -/
def rankRaiseVec : Fin 3 × Fin 3 × Fin 3 → ℂ :=
  fun x => if x.2.1 = x.1 ∧ x.2.2 = 0 then 1 else 0

set_option maxHeartbeats 800000 in
theorem ptrace₁_ketBra_rankRaiseVec :
    ptrace₁ (ketBra rankRaiseVec rankRaiseVec) =
      Matrix.diagonal (fun y : Fin 3 × Fin 3 => if y.2 = 0 then (1 : ℂ) else 0) := by
  ext ⟨j, k⟩ ⟨j', k'⟩
  simp only [ptrace₁, ketBra, rankRaiseVec, Matrix.diagonal_apply, Fin.sum_univ_three]
  fin_cases j <;> fin_cases k <;> fin_cases j' <;> fin_cases k' <;> simp

theorem rank_ptrace₁_ketBra_rankRaiseVec :
    (ptrace₁ (ketBra rankRaiseVec rankRaiseVec)).rank = 3 := by
  rw [ptrace₁_ketBra_rankRaiseVec, Matrix.rank_diagonal]
  refine (Fintype.card_congr ?_).trans (Fintype.card_fin 3)
  exact
    { toFun := fun y => y.1.1
      invFun := fun i => ⟨(i, 0), by simp⟩
      left_inv := fun y => by
        obtain ⟨⟨j, k⟩, hy⟩ := y
        have hk : k = 0 := by
          by_contra hne
          exact hy (by simp [hne])
        subst hk
        rfl
      right_inv := fun _ => rfl }

/-- Section 1: tracing out one copy can increase the rank of the coefficient matrix. A
27 × 27 matrix of rank at most two (here of rank one) whose partial trace over site 1 has
rank 3, so the two-copy rank-two inequality does not apply to that partial trace. -/
theorem exists_rank_le_two_rank_ptrace₁_eq_three :
    ∃ C : Matrix (Fin 3 × Fin 3 × Fin 3) (Fin 3 × Fin 3 × Fin 3) ℂ,
      C.rank ≤ 2 ∧ (ptrace₁ C).rank = 3 := by
  refine ⟨ketBra rankRaiseVec rankRaiseVec, ?_, rank_ptrace₁_ketBra_rankRaiseVec⟩
  refine rank_le_two_of_eq_mul _ (Matrix.of fun x _ => rankRaiseVec x)
    (Matrix.of fun _ y => (1 / 2 : ℂ) * (starRingEnd ℂ) (rankRaiseVec y)) ?_
  ext x y
  simp only [ketBra, Matrix.mul_apply, Matrix.of_apply, Fin.sum_univ_two]
  ring

end RankRaise

end ThreeCopyQutritWerner

end
