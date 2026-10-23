module

public import CGLMPBounds.Partition.HardyCoefficientIntegration
public import CGLMPBounds.Partition.CircularFubini
public import CGLMPBounds.Partition.TriangleDifferenceIntegral
public import CGLMPBounds.Partition.SourceCountReflection

@[expose] public section


/-! D.3 for the literal tilted source measure and actual Fourier Hardy
average. Boundary Fubini and the triangular change of variables are
proved in preceding modules. No positivity claim is used or asserted. -/

namespace CGLMPBounds.Partition
open Set MeasureTheory
open scoped Matrix
noncomputable section

private lemma edgeForm_intervalIntegrable {d r : ℕ} (w : ℕ → ℝ → ℝ)
    (hw : ∀ h, 0 < h → h < d → IntervalIntegrable (w h) volume 0 1)
    (V : Fin d → Circulation.Mat r) :
    IntervalIntegrable (fun x => scalarEdgeForm (fun h => w h x) V) volume 0 1 := by
  exact scalarEdgeForm_intervalIntegrable w hw V

private lemma edgeForm_integral {d r : ℕ} (w : ℕ → ℝ → ℝ)
    (hw : ∀ h, 0 < h → h < d → IntervalIntegrable (w h) volume 0 1)
    (V : Fin d → Circulation.Mat r) :
    (∫ x in (0 : ℝ)..1, scalarEdgeForm (fun h => w h x) V) =
      scalarEdgeForm (fun h => ∫ x in (0 : ℝ)..1, w h x) V := by
  exact scalarEdgeForm_integral w hw V

private lemma edgeForm_const_mul {d r : ℕ} (c : ℝ) (w : ℕ → ℝ)
    (V : Fin d → Circulation.Mat r) :
    c * scalarEdgeForm w V = scalarEdgeForm (fun h => c * w h) V := by
  exact scalarEdgeForm_const_mul c w V

/-- Exact source D.3: the average of the actual negative-Fourier-energy
Hardy gap is the coefficient form of the actual count probabilities. -/
theorem source_averagedCircularHardyForm_eq_coefficients {d r : ℕ}
    (hd : 2 ≤ d) (hr : 0 < r) (V : Fin d → Circulation.Mat r)
    (hV : ∀ j, (V j)ᴴ * V j = 1) :
    averagedCircularHardyForm (by omega : 0 < d) (sourcePartitionMeasure d) V =
      scalarEdgeForm (fun h => sourcePartitionCoefficient d h 0) V := by
  have hd0 : 0 < d := by omega
  letI : IsProbabilityMeasure (sourcePartitionMeasure d) :=
    sourcePartitionMeasure_isProbabilityMeasure d hd0
  let w : ℕ → ℝ → ℝ := fun h x =>
    scalarSecant x * (sourcePartitionMeasure d).real {T | boundaryArcCount d 0 x T = h} +
    scalarSecant (1 - x) * (sourcePartitionMeasure d).real {T | boundaryArcCount d 0 x T = d - h}
  have hw (h : ℕ) (hh0 : 0 < h) (hhd : h < d) :
      IntervalIntegrable (w h) volume 0 1 := by
    let F : ℝ → ℝ := fun x => scalarSecant x *
      (sourcePartitionMeasure d).real {T | boundaryArcCount d 0 x T = h}
    have hFi : IntervalIntegrable F volume 0 1 :=
      sourcePartitionCount_weight_intervalIntegrable d h hh0 hhd 0
    have hFr : IntervalIntegrable (fun x => F (1 - x)) volume 0 1 := by
      simpa using (hFi.comp_sub_left 1).symm
    apply (hFi.add hFr).congr_uIoo
    intro x hx
    have hx' : x ∈ Icc (0 : ℝ) 1 := by
      have hx'' : x ∈ Ioo (0 : ℝ) 1 := by simpa using hx
      exact ⟨hx''.1.le, hx''.2.le⟩
    dsimp only [F, w]
    rw [sourcePartition_count_probability_reflect d h hd hhd.le 0 0 x hx']
  let F : ℝ → ℝ := fun x => scalarEdgeForm (fun h => w h x) V
  have hFi : IntervalIntegrable F volume 0 1 := edgeForm_intervalIntegrable w hw V
  have hprob (h : ℕ) (s x : ℝ) (hx : x ∈ Icc (0 : ℝ) 1) :
      (sourcePartitionMeasure d).real {T | boundaryArcCount d s x T = h} =
        (sourcePartitionMeasure d).real {T | boundaryArcCount d 0 x T = h} := by
    rw [sourcePartitionMeasure_count_law d h hd s x hx,
      sourcePartitionMeasure_count_law d h hd 0 x hx]
  have he : averagedCircularHardyForm hd0 (sourcePartitionMeasure d) V =
      (1 / (2 * (d : ℝ))) * (∫ p : ℝ × ℝ,
        (if p.1 < p.2 then F (p.2 - p.1) else 0)
        ∂((volume.restrict (Ioo (0 : ℝ) 1)).prod (volume.restrict (Ioo (0 : ℝ) 1)))) := by
    rw [averagedCircularHardyForm_eq_count_pair_integral hd0 hr V hV (sourcePartitionMeasure d)]
    congr 1
    apply integral_congr_ae
    rw [Measure.prod_restrict]
    apply ae_restrict_of_forall_mem (measurableSet_Ioo.prod measurableSet_Ioo)
    intro p hp
    by_cases hst : p.1 < p.2
    · simp only [if_pos hst]
      have hx : p.2 - p.1 ∈ Icc (0 : ℝ) 1 := by constructor <;> linarith [hp.1.1, hp.2.2]
      simp only [F, w]
      simp_rw [hprob _ p.1 (p.2 - p.1) hx,
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
    exact edgeForm_const_mul (1 - x) (fun h => w h x) V
  rw [hrew, edgeForm_integral W hW V, edgeForm_const_mul]
  unfold scalarEdgeForm
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  by_cases hij : i < j
  · simp only [if_pos hij]
    have h₁ : 0 < j.val - i.val := by have := i.isLt; have := j.isLt; omega
    have h₂ : j.val - i.val < d := by have := j.isLt; omega
    have hc (h : ℕ) (hh0 : 0 < h) (hhd : h < d) :
        (1 / (2 * (d : ℝ))) * (∫ x in (0 : ℝ)..1, W h x) =
          sourcePartitionCoefficient d h 0 :=
      sourcePartitionCoefficient_triangle_normalization d h hh0 hhd 0
    rw [hc _ h₁ h₂, hc _ (by omega) (by omega)]
  · simp only [if_neg hij]

end
end CGLMPBounds.Partition
