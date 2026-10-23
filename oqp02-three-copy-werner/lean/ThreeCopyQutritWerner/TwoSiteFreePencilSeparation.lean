module

public import ThreeCopyQutritWerner.TwoSitePencilSeparation
public import Mathlib.Topology.Instances.Matrix

@[expose] public section


/-!
# Separation with an additional actual corange coefficient

Finite rank-drop exceptions in the free coefficient are removed by
continuity of the literal minors. This keeps the third input factor even
when some exceptional free-parameter pencils vanish identically.
-/

noncomputable section

open scoped Matrix ComplexConjugate ComplexOrder

namespace ThreeCopyQutritWerner

theorem continuous_twoSiteJointFactorFlatten_det
    (A C E : Matrix (Fin 3 × Fin 3) (Fin 2) ℂ)
    (cols : Fin 3 → ((Fin 3 × Fin 2) ⊕ (Fin 3 × Fin 2))) :
    Continuous (fun t : ℂ =>
      ((twoSiteJointFactorFlatten A (C + t • E)).submatrix id cols).det) := by
  apply Continuous.matrix_det
  apply continuous_pi
  intro i
  apply continuous_pi
  intro j
  cases h : cols j with
  | inl p =>
      simp only [Matrix.submatrix_apply, id_eq, twoSiteJointFactorFlatten, h,
        Sum.elim_inl, twoSiteFactorFlatten]
      exact continuous_const
  | inr p =>
      simp only [Matrix.submatrix_apply, id_eq, twoSiteJointFactorFlatten, h,
        Sum.elim_inr, twoSiteFactorFlatten, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
      fun_prop

theorem twoSite_cut_zero_free_pencil_joint_minors_independent
    (A B C D E : Matrix (Fin 3 × Fin 3) (Fin 2) ℂ)
    (hq : ∀ z t : ℂ, cutForm ((A + z • B) * (C + conj z • D + t • E)ᴴ) = 0)
    (z₀ : ℂ) (hne : (A + z₀ • B) * (C + conj z₀ • D)ᴴ ≠ 0) :
    (∀ z w t : ℂ, ∀ cols : Fin 3 → ((Fin 3 × Fin 2) ⊕ (Fin 3 × Fin 2)),
      ((twoSiteJointFactorFlatten (A + z • B) (C + w • D + t • E)).submatrix id cols).det = 0) ∧
    (∀ z w t : ℂ, ∀ cols : Fin 3 → ((Fin 3 × Fin 2) ⊕ (Fin 3 × Fin 2)),
      ((twoSiteJointFactorFlatten (twoSiteFactorFlip (A + z • B))
        (twoSiteFactorFlip (C + w • D + t • E))).submatrix id cols).det = 0) := by
  have hr : ((A + z₀ • B) * (C + conj z₀ • D)ᴴ).rank ≤ 2 :=
    (Matrix.rank_mul_le_left _ _).trans (by simpa using Matrix.rank_le_card_width (A + z₀ • B))
  have hq₀ : cutForm ((A + z₀ • B) * (C + conj z₀ • D)ᴴ) = 0 := by
    simpa only [zero_smul, add_zero] using hq z₀ 0
  have ht := rank_two_of_nonzero_cutForm_zero _ hr hq₀ hne
  obtain ⟨hX, hYH⟩ := rank_eq_two_of_mul (A + z₀ • B) (C + conj z₀ • D)ᴴ ht
  have hY : (C + conj z₀ • D + (0 : ℂ) • E).rank = 2 := by
    simpa only [Matrix.rank_conjTranspose, zero_smul, add_zero] using hYH
  obtain ⟨s, hs, hsY⟩ := affinePencil_rank_two_off_finite (C + conj z₀ • D) E
    (fun t => by simpa using Matrix.rank_le_card_width (C + conj z₀ • D + t • E)) 0 hY
  have hp (t : ℂ) (hts : t ∉ s) := by
    have hneq : (A + z₀ • B) * ((C + t • E) + conj z₀ • D)ᴴ ≠ 0 := by
      have he : C + t • E + conj z₀ • D = C + conj z₀ • D + t • E := by abel
      rw [he]
      have hrp := (full_two_column_product_rank_ranges _ _ hX (hsY t hts)).1
      intro hez
      rw [hez, Matrix.rank_zero] at hrp
      omega
    have hqt (z : ℂ) : cutForm ((A + z • B) * ((C + t • E) + conj z • D)ᴴ) = 0 := by
      have he : C + t • E + conj z • D = C + conj z • D + t • E := by abel
      rw [he]
      exact hq z t
    exact twoSite_cut_zero_pencil_joint_minors_independent A B (C + t • E) D hqt z₀ hneq
  constructor
  · intro z w t cols
    have he : (fun t : ℂ =>
        ((twoSiteJointFactorFlatten (A + z • B) (C + w • D + t • E)).submatrix id cols).det) =
        fun _ => 0 := by
      apply Continuous.ext_on (hs.countable.dense_compl ℂ)
        (continuous_twoSiteJointFactorFlatten_det (A + z • B) (C + w • D) E cols)
        continuous_const
      intro u hu
      have he : C + u • E + w • D = C + w • D + u • E := by abel
      simpa only [he] using (hp u hu).1 z w cols
    exact congrFun he t
  · intro z w t cols
    have hc : Continuous (fun t : ℂ =>
        ((twoSiteJointFactorFlatten (twoSiteFactorFlip (A + z • B))
          (twoSiteFactorFlip (C + w • D + t • E))).submatrix id cols).det) := by
      simpa only [twoSiteFactorFlip_affine] using
        continuous_twoSiteJointFactorFlatten_det (twoSiteFactorFlip (A + z • B))
          (twoSiteFactorFlip (C + w • D)) (twoSiteFactorFlip E) cols
    have he : (fun t : ℂ =>
        ((twoSiteJointFactorFlatten (twoSiteFactorFlip (A + z • B))
          (twoSiteFactorFlip (C + w • D + t • E))).submatrix id cols).det) = fun _ => 0 := by
      apply Continuous.ext_on (hs.countable.dense_compl ℂ) hc continuous_const
      intro u hu
      have he : C + u • E + w • D = C + w • D + u • E := by abel
      simpa only [he] using (hp u hu).2 z w cols
    exact congrFun he t

end ThreeCopyQutritWerner
