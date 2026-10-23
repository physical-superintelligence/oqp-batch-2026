module

public import CGLMPBounds.Partition.CircularFubini
public import CGLMPBounds.Partition.TriangleDifferenceIntegral
public import CGLMPBounds.Partition.HardyCoefficientIntegration
public import CGLMPBounds.Partition.BinomialLaw
public import CGLMPBounds.Partition.SourceCountReflection

@[expose] public section


/-! The independent uniform-boundary case of source D.3. The actual
Fourier Hardy average equals the beta-integral form D_d. Positivity is
still the separate C.6 obligation. -/

namespace CGLMPBounds.Partition
open Set MeasureTheory CGLMPBounds.Certificates
open scoped Matrix
noncomputable section

private lemma uniform_triangle_coefficient (d h : ℕ) (hd : 0 < d)
    (hh : h < d) :
    (1 / (2 * (d : ℝ))) * (∫ x in (0 : ℝ)..1, (1 - x) *
      (scalarSecant x * scalarBinomialWeight d h x +
        scalarSecant (1 - x) * scalarBinomialWeight d (d - h) x)) =
      scalarBetaTransform d h scalarSecant / (2 * (d : ℝ) ^ 2) := by
  let F : ℝ → ℝ := fun x => scalarSecant x * scalarBinomialWeight d h x
  have hF : IntervalIntegrable F volume 0 1 := by
    simpa only [F, mul_comm] using binomial_secant_intervalIntegrable d h hh
  have hrew : (∫ x in (0 : ℝ)..1, (1 - x) *
      (scalarSecant x * scalarBinomialWeight d h x +
        scalarSecant (1 - x) * scalarBinomialWeight d (d - h) x)) =
      ∫ x in (0 : ℝ)..1, (1 - x) * (F x + F (1 - x)) := by
    apply intervalIntegral.integral_congr
    intro x _
    simp only [F, scalarBinomialWeight_reflect d h hh.le]
  rw [hrew, reflected_triangle_weight_integral F hF]
  have hEq : (∫ x in (0 : ℝ)..1, F x) =
      ∫ x in (0 : ℝ)..1, scalarBinomialWeight d h x * scalarSecant x := by
    apply intervalIntegral.integral_congr
    intro x _
    exact mul_comm _ _
  rw [hEq]
  unfold scalarBetaTransform
  have hdR : (d : ℝ) ≠ 0 := by exact_mod_cast hd.ne'
  field_simp
  <;> ring

/-- Literal independent-uniform-boundary conclusion of D.3. It identifies
actual negative Fourier energy with the source D_d beta coefficients. -/
theorem uniform_averagedCircularHardyForm_eq_beta {d r : ℕ}
    (hd : 0 < d) (hr : 0 < r) (V : Fin d → Circulation.Mat r)
    (hV : ∀ j, (V j)ᴴ * V j = 1) :
    averagedCircularHardyForm hd (boundaryProductMeasure d) V =
      scalarEdgeForm (fun h => scalarBetaTransform d h scalarSecant /
        (2 * (d : ℝ) ^ 2)) V := by
  let w : ℕ → ℝ → ℝ := fun h x =>
    scalarSecant x * scalarBinomialWeight d h x +
      scalarSecant (1 - x) * scalarBinomialWeight d (d - h) x
  have hw (h : ℕ) (_ : 0 < h) (hhd : h < d) :
      IntervalIntegrable (w h) volume 0 1 := by
    let F : ℝ → ℝ := fun x => scalarSecant x * scalarBinomialWeight d h x
    have hFi : IntervalIntegrable F volume 0 1 := by
      simpa only [F, mul_comm] using binomial_secant_intervalIntegrable d h hhd
    have hFr : IntervalIntegrable (fun x => F (1 - x)) volume 0 1 := by
      simpa using (hFi.comp_sub_left 1).symm
    simpa only [F, w, scalarBinomialWeight_reflect d h hhd.le] using hFi.add hFr
  let F : ℝ → ℝ := fun x => scalarEdgeForm (fun h => w h x) V
  have hFi : IntervalIntegrable F volume 0 1 := scalarEdgeForm_intervalIntegrable w hw V
  have he : averagedCircularHardyForm hd (boundaryProductMeasure d) V =
      (1 / (2 * (d : ℝ))) * (∫ p : ℝ × ℝ,
        (if p.1 < p.2 then F (p.2 - p.1) else 0)
        ∂((volume.restrict (Ioo (0 : ℝ) 1)).prod (volume.restrict (Ioo (0 : ℝ) 1)))) := by
    rw [averagedCircularHardyForm_eq_count_pair_integral hd hr V hV (boundaryProductMeasure d)]
    congr 1
    apply integral_congr_ae
    rw [Measure.prod_restrict]
    apply ae_restrict_of_forall_mem (measurableSet_Ioo.prod measurableSet_Ioo)
    intro p hp
    by_cases hst : p.1 < p.2
    · simp only [if_pos hst]
      have hx : p.2 - p.1 ∈ Icc (0 : ℝ) 1 := by
        constructor <;> linarith [hp.1.1, hp.2.2]
      simp only [F, w]
      simp_rw [boundaryArcCount_binomial d _ p.1 (p.2 - p.1) hx,
        show 1 - (p.2 - p.1) = 1 - p.2 + p.1 by ring]
    · simp only [if_neg hst]
  rw [he, (triangle_difference_integral F hFi).2]
  let W : ℕ → ℝ → ℝ := fun h x => (1 - x) * w h x
  have hW (h : ℕ) (hh0 : 0 < h) (hhd : h < d) :
      IntervalIntegrable (W h) volume 0 1 :=
    (hw h hh0 hhd).continuousOn_mul (by fun_prop)
  have hrew : (∫ x in (0 : ℝ)..1, (1 - x) * F x) =
      ∫ x in (0 : ℝ)..1, scalarEdgeForm (fun h => W h x) V := by
    apply intervalIntegral.integral_congr
    intro x _
    exact scalarEdgeForm_const_mul (1 - x) (fun h => w h x) V
  rw [hrew, scalarEdgeForm_integral W hW V, scalarEdgeForm_const_mul]
  unfold scalarEdgeForm
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  by_cases hij : i < j
  · simp only [if_pos hij]
    have h₁ : 0 < j.val - i.val := by have := i.isLt; have := j.isLt; omega
    have h₂ : j.val - i.val < d := by have := j.isLt; omega
    have hc (h : ℕ) (hhd : h < d) :
        (1 / (2 * (d : ℝ))) * (∫ x in (0 : ℝ)..1, W h x) =
          scalarBetaTransform d h scalarSecant / (2 * (d : ℝ) ^ 2) :=
      uniform_triangle_coefficient d h hd hhd
    rw [hc _ h₂, hc _ (by omega)]
  · simp only [if_neg hij]

end
end CGLMPBounds.Partition
