module

public import CGLMPBounds.Partition.PotentialEndpoint

@[expose] public section


/-! Reflection, zero mean and the continuous circle function associated with
the actual compact second derivative of D.5. These are ingredients for the
still-separate Fourier inversion and exact mass arguments. -/

namespace CGLMPBounds.Partition
open Set MeasureTheory
open scoped Topology
noncomputable section
local instance : Fact (0 < (1 : ℝ)) := ⟨zero_lt_one⟩

lemma partitionPotential_iteratedWithin_eq_regularized (m : ℕ) {x : ℝ}
    (hx : x ∈ Icc (0 : ℝ) 1) :
    iteratedDerivWithin m partitionPotential (Icc (0 : ℝ) 1) x =
      iteratedDeriv m regularizedPartitionPotential x := by
  have he : EqOn partitionPotential regularizedPartitionPotential (Icc (0 : ℝ) 1) :=
    fun _ ht => partitionPotential_eq_regularized ht
  rw [iteratedDerivWithin_congr he hx]
  exact iteratedDerivWithin_eq_iteratedDeriv
    (uniqueDiffOn_Icc (by norm_num : (0 : ℝ) < 1))
    (analyticAt_regularizedPartitionPotential hx).contDiffAt hx

lemma regularizedPartitionPotential_derivative_reflect (m : ℕ) (x : ℝ) :
    iteratedDeriv m regularizedPartitionPotential x =
      (-1 : ℝ) ^ m * iteratedDeriv m regularizedPartitionPotential (1 - x) := by
  have he : (fun t => regularizedPartitionPotential (1 - t)) = regularizedPartitionPotential :=
    funext regularizedPartitionPotential_symm
  have h := congrFun (iteratedDeriv_comp_const_sub m regularizedPartitionPotential 1) x
  rw [he] at h
  simpa only [smul_eq_mul] using h

theorem partitionPotential_firstWithin_one :
    iteratedDerivWithin 1 partitionPotential (Icc (0 : ℝ) 1) 1 = 0 := by
  have h := regularizedPartitionPotential_derivative_reflect 1 0
  rw [← partitionPotential_iteratedWithin_eq_regularized 1 (by norm_num),
    partitionPotential_firstWithin_zero] at h
  norm_num only [sub_zero, pow_one, neg_one_mul] at h
  rw [partitionPotential_iteratedWithin_eq_regularized 1 (by norm_num)]
  linarith

def partitionPotentialSecond (x : ℝ) : ℝ :=
  iteratedDerivWithin 2 partitionPotential (Icc (0 : ℝ) 1) x

lemma partitionPotentialSecond_reflect {x : ℝ} (hx : x ∈ Icc (0 : ℝ) 1) :
    partitionPotentialSecond (1 - x) = partitionPotentialSecond x := by
  have hx' : 1 - x ∈ Icc (0 : ℝ) 1 := ⟨by linarith [hx.2], by linarith [hx.1]⟩
  unfold partitionPotentialSecond
  rw [partitionPotential_iteratedWithin_eq_regularized 2 hx',
    partitionPotential_iteratedWithin_eq_regularized 2 hx]
  simpa using (regularizedPartitionPotential_derivative_reflect 2 x).symm

lemma partitionPotentialSecond_endpoints : partitionPotentialSecond 0 = partitionPotentialSecond 1 := by
  simpa using (partitionPotentialSecond_reflect (x := (0 : ℝ)) (by norm_num)).symm

lemma partitionPotentialSecond_continuousOn : ContinuousOn partitionPotentialSecond (Icc (0 : ℝ) 1) :=
  partitionPotential_derivativeWithin_continuous 2

lemma integral_partitionPotentialSecond : ∫ x in (0 : ℝ)..1, partitionPotentialSecond x = 0 := by
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le
    (by norm_num : (0 : ℝ) ≤ 1) (partitionPotential_derivativeWithin_continuous 1)
    (fun x hx => (partitionPotential_derivativeWithin_hasDerivWithinAt 1
      (show x ∈ Icc (0 : ℝ) 1 from ⟨hx.1.le, hx.2.le⟩)).hasDerivAt
        (Icc_mem_nhds hx.1 hx.2))
    (partitionPotential_derivativeWithin_intervalIntegrable 2)
  simpa only [partitionPotentialSecond, partitionPotential_firstWithin_one,
    partitionPotential_firstWithin_zero, sub_self] using h

/-- Actual cosine coefficient, with no reconstruction premise. -/
lemma partitionPotentialSecond_cosine (n : ℕ) :
    (∫ x in (0 : ℝ)..1, partitionPotentialSecond x *
      Real.cos (2 * Real.pi * ((n + 1 : ℕ) : ℝ) * x)) = partitionFourierCoefficient n :=
  (partitionFourierCoefficient_eq_cosine n).symm

lemma partitionPotentialSecond_sine (n : ℕ) :
    (∫ x in (0 : ℝ)..1, partitionPotentialSecond x *
      Real.sin (2 * Real.pi * ((n + 1 : ℕ) : ℝ) * x)) = 0 := by
  let k : ℝ := 2 * Real.pi * ((n + 1 : ℕ) : ℝ)
  let f : ℝ → ℝ := fun x => partitionPotentialSecond x * Real.sin (k * x)
  have hr : (∫ x in (0 : ℝ)..1, f (1 - x)) = ∫ x in (0 : ℝ)..1, f x := by
    simpa using intervalIntegral.integral_comp_sub_left f (a := (0 : ℝ)) (b := 1) 1
  have he : (∫ x in (0 : ℝ)..1, f (1 - x)) = -(∫ x in (0 : ℝ)..1, f x) := by
    rw [← intervalIntegral.integral_neg]
    apply intervalIntegral.integral_congr
    intro x hx
    have hx' : x ∈ Icc (0 : ℝ) 1 := by simpa only [uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] using hx
    dsimp [f]
    rw [partitionPotentialSecond_reflect hx']
    have hangle : k * (1 - x) = ((n + 1 : ℕ) : ℝ) * (2 * Real.pi) - k * x := by
      dsimp [k]
      ring
    rw [hangle, Real.sin_nat_mul_two_pi_sub]
    ring
  change (∫ x in (0 : ℝ)..1, f x) = 0
  linarith

/-- The actual continuous periodic extension of the compact second derivative. -/
def partitionSecondCircle : C(AddCircle (1 : ℝ), ℂ) where
  toFun := AddCircle.liftIco 1 0 (fun x => (partitionPotentialSecond x : ℂ))
  continuous_toFun := AddCircle.liftIco_zero_continuous
    (congrArg Complex.ofReal partitionPotentialSecond_endpoints)
    (Complex.continuous_ofReal.comp_continuousOn partitionPotentialSecond_continuousOn)

lemma partitionSecondCircle_zero :
    partitionSecondCircle (0 : AddCircle (1 : ℝ)) = (Real.pi / 2 - 1 : ℝ) := by
  change AddCircle.liftIco 1 0 (fun x => (partitionPotentialSecond x : ℂ))
    ((0 : ℝ) : AddCircle (1 : ℝ)) = _
  rw [AddCircle.liftIco_coe_apply (by norm_num : (0 : ℝ) ∈ Ico 0 (0 + 1))]
  exact congrArg Complex.ofReal partitionPotential_secondWithin_zero

end
end CGLMPBounds.Partition
