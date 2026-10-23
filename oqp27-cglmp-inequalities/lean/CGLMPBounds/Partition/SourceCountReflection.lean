module

public import CGLMPBounds.Partition.SourceCoefficientIntegrability
public import CGLMPBounds.Partition.PotentialSymmetry
public import CGLMPBounds.Certificates.ScalarPartitionContinuity

@[expose] public section


/-! Reflection of the actual D.11 count probabilities and the exact
one-dimensional coefficient normalization in D.3. The complementary arc
term removes the triangle factor (1-x), with no assumed Hardy identity. -/

namespace CGLMPBounds.Partition
open Set MeasureTheory CGLMPBounds.Certificates
noncomputable section

lemma scalarBinomialWeight_second_reflect (d h : ℕ) (hh : h ≤ d) (x : ℝ) :
    iteratedDeriv 2 (scalarBinomialWeight d h) (1 - x) =
      iteratedDeriv 2 (scalarBinomialWeight d (d - h)) x := by
  have he : (fun t => scalarBinomialWeight d h (1 - t)) = scalarBinomialWeight d (d - h) :=
    funext (scalarBinomialWeight_reflect d h hh)
  have hder := congrFun (iteratedDeriv_comp_const_sub 2 (scalarBinomialWeight d h) 1) x
  rw [he] at hder
  simpa using hder.symm

theorem sourcePartition_count_probability_reflect (d h : ℕ) (hd : 2 ≤ d) (hh : h ≤ d)
    (origin origin' x : ℝ) (hx : x ∈ Icc (0 : ℝ) 1) :
    (sourcePartitionMeasure d).real {T | boundaryArcCount d origin (1 - x) T = h} =
      (sourcePartitionMeasure d).real {T | boundaryArcCount d origin' x T = d - h} := by
  have hxc : 1 - x ∈ Icc (0 : ℝ) 1 := by constructor <;> linarith [hx.1, hx.2]
  rw [sourcePartitionMeasure_count_law d h hd origin (1 - x) hxc,
    sourcePartitionMeasure_count_law d (d - h) hd origin' x hx,
    scalarBinomialWeight_reflect d h hh, partitionPotential_symm,
    scalarBinomialWeight_second_reflect d h hh]

lemma reflected_triangle_weight_integral (F : ℝ → ℝ)
    (hF : IntervalIntegrable F volume 0 1) :
    (∫ x in (0 : ℝ)..1, (1 - x) * (F x + F (1 - x))) = ∫ x in (0 : ℝ)..1, F x := by
  have hleft := hF.continuousOn_mul (by fun_prop : ContinuousOn (fun x : ℝ => 1 - x) (uIcc 0 1))
  have hright := hF.continuousOn_mul (by fun_prop : ContinuousOn (fun x : ℝ => x) (uIcc 0 1))
  have hreflect : IntervalIntegrable (fun x : ℝ => (1 - x) * F (1 - x)) volume 0 1 := by
    simpa using (hright.comp_sub_left 1).symm
  calc
    _ = (∫ x in (0 : ℝ)..1, (1 - x) * F x) +
        (∫ x in (0 : ℝ)..1, (1 - x) * F (1 - x)) := by
      simp_rw [mul_add]
      exact intervalIntegral.integral_add hleft hreflect
    _ = (∫ x in (0 : ℝ)..1, (1 - x) * F x) +
        (∫ x in (0 : ℝ)..1, x * F x) := by
      congr 1
      simpa using intervalIntegral.integral_comp_sub_left (fun x : ℝ => x * F x)
        (a := (0 : ℝ)) (b := 1) 1
    _ = _ := by
      rw [← intervalIntegral.integral_add hleft hright]
      apply intervalIntegral.integral_congr
      intro x _
      ring

/-- The actual two arc/count terms have exactly the coefficient D.3:
the complementary reflected arc removes the triangle's length factor. -/
theorem sourcePartitionCoefficient_triangle_normalization (d h : ℕ)
    (hh0 : 0 < h) (hhd : h < d) (origin : ℝ) :
    (1 / (2 * (d : ℝ))) * (∫ x in (0 : ℝ)..1, (1 - x) *
      (scalarSecant x * (sourcePartitionMeasure d).real
        {T | boundaryArcCount d origin x T = h} +
      scalarSecant (1 - x) * (sourcePartitionMeasure d).real
        {T | boundaryArcCount d origin x T = d - h})) =
      sourcePartitionCoefficient d h origin := by
  let F : ℝ → ℝ := fun x => scalarSecant x *
    (sourcePartitionMeasure d).real {T | boundaryArcCount d origin x T = h}
  have he : (∫ x in (0 : ℝ)..1, (1 - x) *
      (scalarSecant x * (sourcePartitionMeasure d).real
        {T | boundaryArcCount d origin x T = h} +
      scalarSecant (1 - x) * (sourcePartitionMeasure d).real
        {T | boundaryArcCount d origin x T = d - h})) =
      ∫ x in (0 : ℝ)..1, (1 - x) * (F x + F (1 - x)) := by
    apply intervalIntegral.integral_congr
    intro x hx
    have hx' : x ∈ Icc (0 : ℝ) 1 := by simpa using hx
    dsimp only [F]
    rw [sourcePartition_count_probability_reflect d h (by omega) hhd.le origin origin x hx']
  rw [he, reflected_triangle_weight_integral F
    (sourcePartitionCount_weight_intervalIntegrable d h hh0 hhd origin)]
  rfl

end
end CGLMPBounds.Partition
