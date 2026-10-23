module

public import CGLMPBounds.Defs.PartitionPairForm
public import CGLMPBounds.Partition.ConsecutiveMeasure
public import CGLMPBounds.Partition.PairKernelIntegral

@[expose] public section


/-! The finite D.2 rectangle sum is the actual upper-triangle integral.
Integrability follows from the genuine pole bounds on distinct cells;
within a cell the unitary self correlation cancels exactly. -/

namespace CGLMPBounds.Partition
open Set MeasureTheory
open scoped Matrix
noncomputable section

theorem stepPairIntegrand_integrable_and_eq_pairForm {d r : ℕ} (hr : 0 < r)
    (ℓ : ConsecutivePartition d) (W : Fin d → Circulation.Mat r)
    (hW : ∀ j, (W j)ᴴ * W j = 1) (S : ℝ → Circulation.Mat r)
    (hcell : ∀ j : Fin d, ∀ t ∈ Ioo (ℓ.boundary j.castSucc) (ℓ.boundary j.succ),
      S t = W j) :
    Integrable (stepPairIntegrand S)
      ((volume.restrict (Ioo (0 : ℝ) 1)).prod (volume.restrict (Ioo (0 : ℝ) 1))) ∧
    (1 / 2 : ℝ) * (∫ p : ℝ × ℝ, stepPairIntegrand S p
      ∂((volume.restrict (Ioo (0 : ℝ) 1)).prod (volume.restrict (Ioo (0 : ℝ) 1)))) =
      consecutivePartitionPairForm ℓ W := by
  let μ : Fin d → Fin d → Measure (ℝ × ℝ) := fun j k =>
    (volume.restrict (Ioo (ℓ.boundary j.castSucc) (ℓ.boundary j.succ))).prod
      (volume.restrict (Ioo (ℓ.boundary k.castSucc) (ℓ.boundary k.succ)))
  let G : Fin d → Fin d → ℝ × ℝ → ℝ := fun j k p =>
    scalarSecant (p.2 - p.1) * (1 - (Circulation.corr (W j) (W k)).re) +
      scalarSecant (1 - p.2 + p.1) * (Circulation.corr (W j) (W k)).im
  have hb (j : Fin d) : ℓ.boundary j.castSucc ≤ ℓ.boundary j.succ :=
    ℓ.monotone_boundary (by change j.val ≤ j.val + 1; omega)
  have hbounds (i : Fin (d + 1)) : ℓ.boundary i ∈ Icc (0 : ℝ) 1 := by
    constructor
    · rw [← ℓ.boundary_zero]; exact ℓ.monotone_boundary (Fin.zero_le i)
    · rw [← ℓ.boundary_one]; exact ℓ.monotone_boundary (Fin.le_last i)
  have hsep {j k : Fin d} (hjk : j < k) :
      ℓ.boundary j.succ ≤ ℓ.boundary k.castSucc :=
    ℓ.monotone_boundary (by change j.val + 1 ≤ k.val; omega)
  have hself (j : Fin d) : Circulation.corr (W j) (W j) = 1 := by
    simp [Circulation.corr, Circulation.tr, hW j, Nat.ne_of_gt hr]
  have he (j k : Fin d) : stepPairIntegrand S =ᵐ[μ j k]
      (fun p => if j < k then G j k p else 0) := by
    dsimp only [μ]
    rw [Measure.prod_restrict]
    apply ae_restrict_of_forall_mem (measurableSet_Ioo.prod measurableSet_Ioo)
    intro p hp
    unfold stepPairIntegrand
    rw [hcell j p.1 hp.1, hcell k p.2 hp.2]
    rcases lt_trichotomy j k with hjk | hjk | hkj
    · have hpt : p.1 < p.2 := lt_trans (hp.1.2.trans_le (hsep hjk)) hp.2.1
      simp only [if_pos hjk, if_pos hpt, G]
    · subst k
      simp [hself]
    · have hpt : ¬p.1 < p.2 := by
        have hpst : p.2 < p.1 := lt_trans (hp.2.2.trans_le (hsep hkj)) hp.1.1
        exact not_lt_of_ge hpst.le
      simp only [if_neg hpt, if_neg (not_lt_of_ge hkj.le)]
  have hG {j k : Fin d} (hjk : j < k) : Integrable (G j k) (μ j k) := by
    have hR := quarterBranch_limit_kernel_integrable
      (hbounds j.castSucc).1 (hb j) (hsep hjk) (hb k) (hbounds k.succ).2
    apply ((hR.mul_const (star (Circulation.corr (W j) (W k)) - 1)).re.const_mul 4).congr
    filter_upwards [] with p
    have hp := quarterBranch_pair_kernel_real (p.2 - p.1) (Circulation.corr (W j) (W k))
    dsimp only [G]
    simp only [RCLike.re_eq_complex_re]
    rw [show 1 - (p.2 - p.1) = 1 - p.2 + p.1 by ring] at hp ⊢
    linarith
  have hi (j k : Fin d) : Integrable (stepPairIntegrand S) (μ j k) := by
    have hh : Integrable (fun p => if j < k then G j k p else 0) (μ j k) := by
      by_cases hjk : j < k
      · simpa only [if_pos hjk] using hG hjk
      · simpa only [if_neg hjk] using (integrable_fun_zero (ℝ × ℝ) ℝ (μ j k))
    exact hh.congr (he j k).symm
  have hsum : (∑ j : Fin d, ∑ k : Fin d, μ j k) =
      (volume.restrict (Ioo (0 : ℝ) 1)).prod (volume.restrict (Ioo (0 : ℝ) 1)) :=
    ℓ.sum_cell_product_measures
  have hisum (j : Fin d) : Integrable (stepPairIntegrand S) (∑ k : Fin d, μ j k) :=
    integrable_finsetSum_measure.mpr (fun k _ => hi j k)
  constructor
  · rw [← hsum]
    exact integrable_finsetSum_measure.mpr (fun j _ => hisum j)
  · rw [← hsum, integral_finsetSum_measure (fun j _ => hisum j)]
    simp_rw [integral_finsetSum_measure (fun k _ => hi _ k)]
    unfold consecutivePartitionPairForm
    congr 1
    apply Finset.sum_congr rfl
    intro j _
    apply Finset.sum_congr rfl
    intro k _
    rw [integral_congr_ae (he j k)]
    by_cases hjk : j < k
    · simp only [if_pos hjk]
      rw [integral_prod _ (hG hjk), intervalIntegral.integral_of_le (hb j),
        integral_Ioc_eq_integral_Ioo]
      apply integral_congr_ae
      filter_upwards [] with s
      rw [intervalIntegral.integral_of_le (hb k), integral_Ioc_eq_integral_Ioo]
    · simp only [if_neg hjk, integral_zero]

end
end CGLMPBounds.Partition
