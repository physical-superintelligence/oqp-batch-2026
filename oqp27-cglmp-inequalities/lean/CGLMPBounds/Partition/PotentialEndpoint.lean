module

public import CGLMPBounds.Partition.PotentialFourierCosine

@[expose] public section


/-! The literal endpoint derivatives needed for the D.9 mass and inversion.
A quotient with nonsingular denominator at zero supplies actual local
antiderivatives; equality is transferred within [0,1]. -/

namespace CGLMPBounds.Partition
open Set Filter
open scoped Topology
noncomputable section

def endpointNumerator (x : ℝ) : ℝ :=
  (2 * x - 1) * Real.sin ((Real.pi / 2) * x) * Real.cos ((Real.pi / 2) * x)
def endpointDenominator (x : ℝ) : ℝ :=
  Real.pi * (Real.sin ((Real.pi / 2) * x) - Real.cos ((Real.pi / 2) * x))
private def endpointNumeratorFirst (x : ℝ) : ℝ :=
  2 * Real.sin ((Real.pi / 2) * x) * Real.cos ((Real.pi / 2) * x) +
    (2 * x - 1) * (Real.pi / 2) *
      (Real.cos ((Real.pi / 2) * x) ^ 2 - Real.sin ((Real.pi / 2) * x) ^ 2)
private def endpointDenominatorFirst (x : ℝ) : ℝ :=
  Real.pi * (Real.pi / 2) *
    (Real.cos ((Real.pi / 2) * x) + Real.sin ((Real.pi / 2) * x))

def endpointPartitionPotential (x : ℝ) : ℝ :=
  -(x * (1 - x)) / 2 + endpointNumerator x / endpointDenominator x

private def endpointPartitionPotentialFirst (x : ℝ) : ℝ :=
  x - 1 / 2 +
    (endpointNumeratorFirst x * endpointDenominator x -
      endpointNumerator x * endpointDenominatorFirst x) / endpointDenominator x ^ 2

private lemma endpoint_sin_hasDerivAt (x : ℝ) :
    HasDerivAt (fun t : ℝ => Real.sin ((Real.pi / 2) * t))
      ((Real.pi / 2) * Real.cos ((Real.pi / 2) * x)) x := by
  convert ((hasDerivAt_id x).const_mul (Real.pi / 2)).sin using 1 <;> simp only [id_eq] <;> ring
private lemma endpoint_cos_hasDerivAt (x : ℝ) :
    HasDerivAt (fun t : ℝ => Real.cos ((Real.pi / 2) * t))
      (-(Real.pi / 2) * Real.sin ((Real.pi / 2) * x)) x := by
  convert ((hasDerivAt_id x).const_mul (Real.pi / 2)).cos using 1 <;> simp only [id_eq] <;> ring

private lemma endpointNumerator_hasDerivAt (x : ℝ) :
    HasDerivAt endpointNumerator (endpointNumeratorFirst x) x := by
  have h := ((((hasDerivAt_id x).const_mul 2).sub_const 1).mul
    (endpoint_sin_hasDerivAt x)).mul (endpoint_cos_hasDerivAt x)
  convert h using 1
  · rfl
  · unfold endpointNumeratorFirst
    simp only [Pi.mul_apply, id_eq]
    ring

private lemma endpointDenominator_hasDerivAt (x : ℝ) :
    HasDerivAt endpointDenominator (endpointDenominatorFirst x) x := by
  have h := ((endpoint_sin_hasDerivAt x).sub (endpoint_cos_hasDerivAt x)).const_mul Real.pi
  convert h using 1
  · rfl
  · unfold endpointDenominatorFirst
    ring

private lemma endpointPartitionPotential_hasDerivAt {x : ℝ}
    (hx : endpointDenominator x ≠ 0) :
    HasDerivAt endpointPartitionPotential (endpointPartitionPotentialFirst x) x := by
  have hp := (((hasDerivAt_id x).mul
    ((hasDerivAt_const x (1 : ℝ)).sub (hasDerivAt_id x))).neg).div_const 2
  have hq := (endpointNumerator_hasDerivAt x).div (endpointDenominator_hasDerivAt x) hx
  convert hp.add hq using 1
  · rfl
  · unfold endpointPartitionPotentialFirst
    simp only [Pi.sub_apply, Pi.mul_apply, id_eq]
    ring

private lemma endpointNumeratorFirst_hasDerivAt_zero :
    HasDerivAt endpointNumeratorFirst (2 * Real.pi) 0 := by
  have hs := endpoint_sin_hasDerivAt 0
  have hc := endpoint_cos_hasDerivAt 0
  have hl := ((hasDerivAt_id (0 : ℝ)).const_mul 2).sub_const 1
  have h := ((hs.const_mul 2).mul hc).add
    ((hl.mul_const (Real.pi / 2)).mul ((hc.pow 2).sub (hs.pow 2)))
  convert h using 1
  · rfl
  · norm_num
    <;> ring

private lemma endpointDenominatorFirst_hasDerivAt_zero :
    HasDerivAt endpointDenominatorFirst (Real.pi ^ 3 / 4) 0 := by
  have h := ((endpoint_cos_hasDerivAt 0).add (endpoint_sin_hasDerivAt 0)).const_mul
    (Real.pi * (Real.pi / 2))
  convert h using 1
  · rfl
  · norm_num
    <;> ring

private lemma endpointPartitionPotentialFirst_hasDerivAt_zero :
    HasDerivAt endpointPartitionPotentialFirst (Real.pi / 2 - 1) 0 := by
  have hn := endpointNumerator_hasDerivAt 0
  have hd := endpointDenominator_hasDerivAt 0
  have hnum := (endpointNumeratorFirst_hasDerivAt_zero.mul hd).sub
    (hn.mul endpointDenominatorFirst_hasDerivAt_zero)
  have hden := hd.pow 2
  have hz : endpointDenominator 0 ^ 2 ≠ 0 := by
    simp [endpointDenominator, Real.pi_ne_zero]
  have h := ((hasDerivAt_id (0 : ℝ)).sub_const (1 / 2)).add (hnum.div hden hz)
  convert h using 1
  · rfl
  · norm_num [endpointNumerator, endpointDenominator, endpointNumeratorFirst,
      endpointDenominatorFirst]
    <;> field_simp [Real.pi_ne_zero]
    <;> ring

lemma endpointPartitionPotential_first_zero : deriv endpointPartitionPotential 0 = 0 := by
  have hd : endpointDenominator 0 ≠ 0 := by simp [endpointDenominator, Real.pi_ne_zero]
  rw [(endpointPartitionPotential_hasDerivAt hd).deriv]
  simp [endpointPartitionPotentialFirst, endpointNumerator, endpointDenominator,
    endpointNumeratorFirst, endpointDenominatorFirst]
  <;> field_simp [Real.pi_ne_zero]
  <;> ring

lemma endpointPartitionPotential_second_zero :
    iteratedDeriv 2 endpointPartitionPotential 0 = Real.pi / 2 - 1 := by
  have hd : endpointDenominator 0 ≠ 0 := by simp [endpointDenominator, Real.pi_ne_zero]
  have he : deriv endpointPartitionPotential =ᶠ[𝓝 (0 : ℝ)] endpointPartitionPotentialFirst := by
    filter_upwards [(endpointDenominator_hasDerivAt 0).continuousAt.eventually_ne hd] with x hx
    exact (endpointPartitionPotential_hasDerivAt hx).deriv
  rw [show (2 : ℕ) = 1 + 1 by rfl, iteratedDeriv_succ, iteratedDeriv_one, he.deriv_eq]
  exact endpointPartitionPotentialFirst_hasDerivAt_zero.deriv

lemma partitionPotential_eq_endpoint_near_zero {x : ℝ}
    (hx : x ∈ Ico (0 : ℝ) (1 / 4)) :
    partitionPotential x = endpointPartitionPotential x := by
  by_cases hx0 : x = 0
  · subst x
    simp [partitionPotential_zero, endpointPartitionPotential, endpointNumerator]
  have hxpos : 0 < x := lt_of_le_of_ne hx.1 (Ne.symm hx0)
  have hs : Real.sin (Real.pi * x / 2) ≠ 0 := by
    apply (Real.sin_pos_of_pos_of_lt_pi _ _).ne'
    · positivity
    · nlinarith [Real.pi_pos, hx.2]
  have hc : Real.cos (Real.pi * x / 2) ≠ 0 := by
    apply (Real.cos_pos_of_mem_Ioo _).ne'
    constructor <;> nlinarith [Real.pi_pos, hx.1, hx.2]
  have hsc : Real.sin (Real.pi * x / 2) - Real.cos (Real.pi * x / 2) ≠ 0 := by
    have hcpos := Real.cos_pos_of_mem_Ioo
      (show Real.pi * x / 2 + Real.pi / 4 ∈ Ioo (-(Real.pi / 2)) (Real.pi / 2) by
        constructor <;> nlinarith [Real.pi_pos, hx.1, hx.2])
    rw [Real.cos_add, Real.sin_pi_div_four, Real.cos_pi_div_four] at hcpos
    intro h
    have he := sub_eq_zero.mp h
    rw [he] at hcpos
    nlinarith
  have hx1 : x ≠ 1 := by linarith [hx.2]
  have hxh : x ≠ 1 / 2 := by linarith [hx.2]
  simp only [partitionPotential, if_neg (not_or_intro hx0 hx1), if_neg hxh,
    endpointPartitionPotential, endpointNumerator, endpointDenominator]
  rw [show (Real.pi / 2) * x = Real.pi * x / 2 by ring]
  simp only [one_div]
  rw [inv_sub_inv hc hs]
  congr 1
  field_simp [Real.pi_ne_zero, hs, hc, hsc]
  <;> ring

lemma partitionPotential_eventuallyEq_endpoint_zero :
    partitionPotential =ᶠ[𝓝[Icc (0 : ℝ) 1] 0] endpointPartitionPotential := by
  filter_upwards [self_mem_nhdsWithin,
    (eventually_lt_nhds (by norm_num : (0 : ℝ) < 1 / 4)).filter_mono nhdsWithin_le_nhds]
    with x hx hquarter
  exact partitionPotential_eq_endpoint_near_zero ⟨hx.1, hquarter⟩

lemma analyticAt_endpointPartitionPotential_zero : AnalyticAt ℝ endpointPartitionPotential 0 := by
  have hd : endpointDenominator 0 ≠ 0 := by simp [endpointDenominator, Real.pi_ne_zero]
  unfold endpointPartitionPotential
  exact (by fun_prop : AnalyticAt ℝ (fun x : ℝ => -(x * (1 - x)) / 2) 0).add
    ((by unfold endpointNumerator; fun_prop : AnalyticAt ℝ endpointNumerator 0).div
      (by unfold endpointDenominator; fun_prop : AnalyticAt ℝ endpointDenominator 0) hd)

/-- The actual compact endpoint derivative is zero, as required for periodic
reconstruction of the source potential. -/
theorem partitionPotential_firstWithin_zero :
    iteratedDerivWithin 1 partitionPotential (Icc (0 : ℝ) 1) 0 = 0 := by
  rw [partitionPotential_eventuallyEq_endpoint_zero.iteratedDerivWithin_eq
    (partitionPotential_eq_endpoint_near_zero (by norm_num)),
    iteratedDerivWithin_eq_iteratedDeriv
      (uniqueDiffOn_Icc (by norm_num : (0 : ℝ) < 1))
      analyticAt_endpointPartitionPotential_zero.contDiffAt (by norm_num), iteratedDeriv_one]
  exact endpointPartitionPotential_first_zero

/-- The literal second endpoint derivative responsible for π/4−1/2. -/
theorem partitionPotential_secondWithin_zero :
    iteratedDerivWithin 2 partitionPotential (Icc (0 : ℝ) 1) 0 = Real.pi / 2 - 1 := by
  rw [partitionPotential_eventuallyEq_endpoint_zero.iteratedDerivWithin_eq
    (partitionPotential_eq_endpoint_near_zero (by norm_num)),
    iteratedDerivWithin_eq_iteratedDeriv
      (uniqueDiffOn_Icc (by norm_num : (0 : ℝ) < 1))
      analyticAt_endpointPartitionPotential_zero.contDiffAt (by norm_num)]
  exact endpointPartitionPotential_second_zero

end
end CGLMPBounds.Partition
