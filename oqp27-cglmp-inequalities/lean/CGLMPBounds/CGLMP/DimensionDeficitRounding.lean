module

public import CGLMPBounds.CGLMP.DimensionDeficitFractional

@[expose] public section


/-!
# Rounding an integer-trace positive contraction

Appendix E rounds a positive contraction of integer trace to the projection onto its
largest eigenvalues. The scalar inequality proved here is
`∑ λᵢ² ≤ ∑_{i ∈ S} λᵢ` when `|S| = ∑ λᵢ` and every eigenvalue in `S` is at least
every eigenvalue outside `S`. Consequently the squared Frobenius error in rounding
to that spectral projection is at most `Tr(X-X²)`.

For the source's block projection `Λ = diag(Λ₀,…,Λ_{d-1})`, this scalar inequality
also gives `‖Λ - I_d ⊗ P‖²_F ≤ 2d Tr(X-X²)`, where `X = d⁻¹ ∑ Λₐ`.
Dividing by the ambient dimension `N = 4dn` gives exactly `2 ε_red`.
The block-projection bridge is formalized separately in `DimensionDeficitRankRepair`.
-/

open Matrix
open scoped ComplexOrder

namespace CGLMPBounds

noncomputable section

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The largest `k` entries of a `[0,1]` vector of sum `k` dominate its squared sum. -/
theorem sum_sq_le_sum_top_of_sum_eq_card (s : Finset ι) (w : ι → ℝ)
    (hw : ∀ i, w i ∈ Set.Icc (0 : ℝ) 1) (hsum : ∑ i, w i = (s.card : ℝ))
    (htop : ∀ i ∈ s, ∀ j ∉ s, w j ≤ w i) :
    ∑ i, (w i) ^ 2 ≤ ∑ i ∈ s, w i := by
  rcases s.eq_empty_or_nonempty with rfl | hne
  · have hle : ∑ i, (w i) ^ 2 ≤ ∑ i, w i := by
      apply Finset.sum_le_sum
      intro i _
      have h := mul_nonneg (hw i).1 (sub_nonneg.mpr (hw i).2)
      nlinarith
    simpa only [hsum, Finset.card_empty, Nat.cast_zero, Finset.sum_empty] using hle
  · obtain ⟨a, ha, hmin⟩ := s.exists_min_image w hne
    have hpoint : ∀ i, (w i) ^ 2 ≤
        (if i ∈ s then w i else 0) + w a * (w i - if i ∈ s then 1 else 0) := by
      intro i
      by_cases hi : i ∈ s
      · simp only [if_pos hi]
        have h := mul_nonneg (sub_nonneg.mpr (hw i).2) (sub_nonneg.mpr (hmin i hi))
        nlinarith
      · simp only [if_neg hi, sub_zero, zero_add]
        have h := mul_nonneg (hw i).1 (sub_nonneg.mpr (htop a ha i hi))
        nlinarith
    have hle := Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) => hpoint i)
    have hind : (∑ i, if i ∈ s then (1 : ℝ) else 0) = (s.card : ℝ) := by simp
    have hsel : (∑ i, if i ∈ s then w i else 0) = ∑ i ∈ s, w i := by simp
    simp only [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_sub_distrib,
      hind, hsel, hsum, sub_self, mul_zero, add_zero] at hle
    exact hle

/-- Squared scalar rounding error is at most the contraction defect. -/
theorem sum_top_rounding_sq_le_defect (s : Finset ι) (w : ι → ℝ)
    (hw : ∀ i, w i ∈ Set.Icc (0 : ℝ) 1) (hsum : ∑ i, w i = (s.card : ℝ))
    (htop : ∀ i ∈ s, ∀ j ∉ s, w j ≤ w i) :
    ∑ i, (w i - if i ∈ s then 1 else 0) ^ 2 ≤ ∑ i, w i * (1 - w i) := by
  have htopSum := sum_sq_le_sum_top_of_sum_eq_card s w hw hsum htop
  have hpoint : ∀ i, (w i - if i ∈ s then 1 else 0) ^ 2
      = (w i) ^ 2 - 2 * (if i ∈ s then w i else 0) + (if i ∈ s then 1 else 0) := by
    intro i
    split_ifs <;> ring
  have hL : (∑ i, (w i - if i ∈ s then 1 else 0) ^ 2)
      = (∑ i, (w i) ^ 2) - 2 * (∑ i ∈ s, w i) + (s.card : ℝ) := by
    simp_rw [hpoint]
    simp [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum]
  have hR : (∑ i, w i * (1 - w i)) = (s.card : ℝ) - ∑ i, (w i) ^ 2 := by
    simp_rw [mul_sub, mul_one, ← sq]
    rw [Finset.sum_sub_distrib, hsum]
  rw [hL, hR]
  linarith

/-- A decreasing finite sequence has a subset of its largest `k` entries. -/
theorem exists_top_finset_of_antitone {m k : ℕ} (w : Fin m → ℝ)
    (hanti : Antitone w) (hk : k ≤ m) :
    ∃ s : Finset (Fin m), s.card = k ∧ ∀ i ∈ s, ∀ j ∉ s, w j ≤ w i := by
  let s : Finset (Fin m) := Finset.univ.filter (fun i => i.val < k)
  have hmem : ∀ i, i ∈ s ↔ i.val < k := by intro i; simp [s]
  let e : {i : Fin m // i.val < k} ≃ Fin k :=
    { toFun := fun i => ⟨i.1.val, i.2⟩
      invFun := fun i => ⟨⟨i.val, i.isLt.trans_le hk⟩, i.isLt⟩
      left_inv := fun i => by ext; rfl
      right_inv := fun i => by ext; rfl }
  have hc : s.card = k := by
    have h := Fintype.card_congr e
    simpa only [Fintype.card_subtype, Fintype.card_fin] using h
  refine ⟨s, hc, ?_⟩
  intro i hi j hj
  apply hanti
  have hi' := (hmem i).mp hi
  have hj' : k ≤ j.val := Nat.le_of_not_gt (fun h => hj ((hmem j).mpr h))
  exact Fin.le_iff_val_le_val.mpr (by omega)

/-- The spectral projection associated with a finite subset of eigenvectors. -/
def spectralRoundingProjector {M : Matrix ι ι ℂ} (hM : M.IsHermitian) (s : Finset ι) :
    Matrix ι ι ℂ :=
  Unitary.conjStarAlgAut ℂ (Matrix ι ι ℂ) hM.eigenvectorUnitary
    (Matrix.diagonal (fun i => if i ∈ s then (1 : ℂ) else 0))

theorem spectralRoundingProjector_isHermitian {M : Matrix ι ι ℂ}
    (hM : M.IsHermitian) (s : Finset ι) : (spectralRoundingProjector hM s).IsHermitian := by
  unfold spectralRoundingProjector Matrix.IsHermitian
  rw [Unitary.conjStarAlgAut_apply, Matrix.conjTranspose_mul, Matrix.conjTranspose_mul,
    Matrix.star_eq_conjTranspose, Matrix.conjTranspose_conjTranspose,
    Matrix.diagonal_conjTranspose]
  have hdiag : Matrix.diagonal (star (fun i => if i ∈ s then (1 : ℂ) else 0))
      = Matrix.diagonal (fun i => if i ∈ s then (1 : ℂ) else 0) := by
    congr 1
    funext i
    simp only [Pi.star_apply]
    split_ifs <;> simp
  rw [hdiag, Matrix.mul_assoc]

theorem spectralRoundingProjector_mul_self {M : Matrix ι ι ℂ}
    (hM : M.IsHermitian) (s : Finset ι) :
    spectralRoundingProjector hM s * spectralRoundingProjector hM s
      = spectralRoundingProjector hM s := by
  unfold spectralRoundingProjector
  rw [← map_mul, Matrix.diagonal_mul_diagonal]
  congr 2
  funext i
  split_ifs <;> simp

theorem trace_unitary_conj_matrix (U : Matrix.unitaryGroup ι ℂ) (X : Matrix ι ι ℂ) :
    Matrix.trace (Unitary.conjStarAlgAut ℂ (Matrix ι ι ℂ) U X) = Matrix.trace X := by
  rw [Unitary.conjStarAlgAut_apply, Matrix.trace_mul_cycle, Unitary.coe_star_mul_self,
    Matrix.one_mul]

theorem spectralRoundingProjector_rank {M : Matrix ι ι ℂ}
    (hM : M.IsHermitian) (s : Finset ι) : (spectralRoundingProjector hM s).rank = s.card := by
  have hU : IsUnit (hM.eigenvectorUnitary : Matrix ι ι ℂ) := Unitary.isUnit_coe
  have hUdet := (Matrix.isUnit_iff_isUnit_det _).mp hU
  have hUstar := (Matrix.isUnit_iff_isUnit_det _).mp hU.star
  unfold spectralRoundingProjector
  rw [Unitary.conjStarAlgAut_apply, Matrix.rank_mul_eq_left_of_isUnit_det _ _ hUstar,
    Matrix.rank_mul_eq_right_of_isUnit_det _ _ hUdet, Matrix.rank_diagonal]
  simp

theorem spectralRoundingProjector_trace {M : Matrix ι ι ℂ}
    (hM : M.IsHermitian) (s : Finset ι) :
    Matrix.trace (spectralRoundingProjector hM s) = (s.card : ℂ) := by
  rw [spectralRoundingProjector, trace_unitary_conj_matrix, Matrix.trace_diagonal]
  simp

theorem trace_rounding_error_eq_sum {M : Matrix ι ι ℂ}
    (hM : M.IsHermitian) (s : Finset ι) :
    (Matrix.trace ((M - spectralRoundingProjector hM s)ᴴ
      * (M - spectralRoundingProjector hM s))).re
      = ∑ i, (hM.eigenvalues i - if i ∈ s then 1 else 0) ^ 2 := by
  rw [(hM.sub (spectralRoundingProjector_isHermitian hM s)).eq]
  have hdiff : M - spectralRoundingProjector hM s
      = Unitary.conjStarAlgAut ℂ (Matrix ι ι ℂ) hM.eigenvectorUnitary
          (Matrix.diagonal (RCLike.ofReal ∘ hM.eigenvalues)
            - Matrix.diagonal (fun i => if i ∈ s then (1 : ℂ) else 0)) := by
    rw [map_sub, ← hM.spectral_theorem]
    rfl
  rw [hdiff, ← map_mul, trace_unitary_conj_matrix, Matrix.diagonal_sub,
    Matrix.diagonal_mul_diagonal, Matrix.trace_diagonal, Complex.re_sum]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  simp only [Function.comp_apply, RCLike.ofReal_eq_complex_ofReal]
  split_ifs <;> simp [Complex.mul_re] <;> ring

/-- A positive contraction of integer trace admits a projection of that rank, with squared
Frobenius error bounded by its trace defect. This supplies the spectral rounding step in E. -/
theorem exists_integer_trace_rounding_with_trace {M : Matrix ι ι ℂ}
    (hM : M.PosSemidef) (hC : (1 - M).PosSemidef) (k : ℕ)
    (htrace : (Matrix.trace M).re = (k : ℝ)) :
    ∃ P : Matrix ι ι ℂ, P.IsHermitian ∧ P * P = P ∧ P.rank = k ∧ Matrix.trace P = (k : ℂ) ∧
      (Matrix.trace ((M - P)ᴴ * (M - P))).re ≤ (Matrix.trace (M - M * M)).re := by
  have hw : ∀ i, hM.1.eigenvalues i ∈ Set.Icc (0 : ℝ) 1 :=
    fun i => ⟨hM.eigenvalues_nonneg i, positive_contraction_eigenvalues_le_one hM hC i⟩
  have hsum : ∑ i, hM.1.eigenvalues i = (k : ℝ) := by
    have ht : (Matrix.trace M).re = ∑ i, hM.1.eigenvalues i := by
      simpa only [Complex.re_sum, RCLike.ofReal_eq_complex_ofReal, Complex.ofReal_re] using
        congrArg Complex.re hM.1.trace_eq_sum_eigenvalues
    exact ht.symm.trans htrace
  have hk : k ≤ Fintype.card ι := by
    have hle : ∑ i, hM.1.eigenvalues i ≤ ∑ _ : ι, (1 : ℝ) :=
      Finset.sum_le_sum (fun i _ => (hw i).2)
    rw [hsum] at hle
    simpa only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one,
      Nat.cast_le] using hle
  obtain ⟨s₀, hc₀, htop₀⟩ := exists_top_finset_of_antitone hM.1.eigenvalues₀
    hM.1.eigenvalues₀_antitone hk
  let e : Fin (Fintype.card ι) ≃ ι := Fintype.equivOfCardEq (Fintype.card_fin _)
  let s : Finset ι := s₀.map e.toEmbedding
  have hc : s.card = k := by simpa only [s, Finset.card_map] using hc₀
  have htop : ∀ i ∈ s, ∀ j ∉ s, hM.1.eigenvalues j ≤ hM.1.eigenvalues i := by
    intro i hi j hj
    obtain ⟨i₀, hi₀, rfl⟩ := Finset.mem_map.mp hi
    have hj₀ : e.symm j ∉ s₀ := by
      intro hj₀
      exact hj (Finset.mem_map.mpr ⟨e.symm j, hj₀, e.apply_symm_apply j⟩)
    simpa only [Matrix.IsHermitian.eigenvalues, e, Equiv.toEmbedding_apply,
      Equiv.symm_apply_apply] using
      htop₀ i₀ hi₀ (e.symm j) hj₀
  refine ⟨spectralRoundingProjector hM.1 s, spectralRoundingProjector_isHermitian hM.1 s,
    spectralRoundingProjector_mul_self hM.1 s, ?_, ?_, ?_⟩
  · rw [spectralRoundingProjector_rank, hc]
  · rw [spectralRoundingProjector_trace, hc]
  · rw [trace_rounding_error_eq_sum, re_trace_contraction_defect hM.1]
    exact sum_top_rounding_sq_le_defect s _ hw (hsum.trans (congrArg Nat.cast hc.symm)) htop

/-- The endpoint form of the spectral rounding estimate, with ordinary matrix rank. -/
theorem exists_integer_trace_rounding {M : Matrix ι ι ℂ}
    (hM : M.PosSemidef) (hC : (1 - M).PosSemidef) (k : ℕ)
    (htrace : (Matrix.trace M).re = (k : ℝ)) :
    ∃ P : Matrix ι ι ℂ, P.IsHermitian ∧ P * P = P ∧ P.rank = k ∧
      (Matrix.trace ((M - P)ᴴ * (M - P))).re ≤ (Matrix.trace (M - M * M)).re := by
  obtain ⟨P, hP, hP2, hRank, _, herror⟩ := exists_integer_trace_rounding_with_trace hM hC k htrace
  exact ⟨P, hP, hP2, hRank, herror⟩

end

end CGLMPBounds
