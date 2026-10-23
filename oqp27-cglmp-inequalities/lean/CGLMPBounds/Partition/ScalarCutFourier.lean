module

public import CGLMPBounds.Defs.PartitionScalarCut
public import CGLMPBounds.Partition.ScalarQuarterFourier

@[expose] public section


/-! Zero negative Hardy gap of the actual scalar cuts in D.4. Direct
integration on both sides of the cut proves the Fourier moduli unchanged,
including cuts at 0 and 1. No translation invariance is assumed. -/

namespace CGLMPBounds.Partition
open Set MeasureTheory
noncomputable section

private lemma integral_exp_single_jump (c : ℂ) (hc : c ≠ 0)
    (he : Complex.exp c = -Complex.I) (T : ℝ) (hT : T ∈ Icc (0 : ℝ) 1) :
    (∫ t in (0 : ℝ)..1,
      Complex.exp (c * (t : ℂ)) * (if T < t then Complex.I else 1)) =
      (1 - Complex.I) * Complex.exp (c * (T : ℂ)) / c := by
  let F : ℝ → ℂ := fun t =>
    Complex.exp (c * (t : ℂ)) * (if T < t then Complex.I else 1)
  have hleft : EqOn (fun t : ℝ => Complex.exp (c * (t : ℂ))) F (uIoo 0 T) := by
    rw [uIoo_of_le hT.1]
    intro t ht
    simp [F, not_lt.mpr ht.2.le]
  have hright : EqOn (fun t : ℝ => Complex.exp (c * (t : ℂ)) * Complex.I)
      F (uIoo T 1) := by
    rw [uIoo_of_le hT.2]
    intro t ht
    simp [F, ht.1]
  have hi₀ : IntervalIntegrable F volume 0 T := by
    have hc₀ : Continuous (fun t : ℝ => Complex.exp (c * (t : ℂ))) := by fun_prop
    exact (hc₀.intervalIntegrable 0 T).congr_uIoo hleft
  have hi₁ : IntervalIntegrable F volume T 1 := by
    have hc₁ : Continuous (fun t : ℝ => Complex.exp (c * (t : ℂ)) * Complex.I) := by fun_prop
    exact (hc₁.intervalIntegrable T 1).congr_uIoo hright
  change (∫ t in (0 : ℝ)..1, F t) = _
  rw [← intervalIntegral.integral_add_adjacent_intervals hi₀ hi₁,
    ← intervalIntegral.integral_congr_uIoo hleft,
    ← intervalIntegral.integral_congr_uIoo hright,
    intervalIntegral.integral_mul_const,
    integral_exp_mul_complex hc, integral_exp_mul_complex hc]
  simp only [Complex.ofReal_zero, Complex.ofReal_one, mul_zero, mul_one,
    Complex.exp_zero, he]
  field_simp [hc]
  <;> ring_nf
  <;> norm_num [Complex.I_sq]
  <;> ring

/-- Actual negative coefficient at frequency -(n+1), with the cut phase
displayed explicitly. Its modulus is independent of the cut and label. -/
theorem sourceScalarCutBranch_negative_coefficient (a : ℤ) (T : ℝ)
    (hT : T ∈ Icc (0 : ℝ) 1) (n : ℕ) :
    (∫ t in (0 : ℝ)..1,
      Complex.exp (((2 * Real.pi * ((n + 1 : ℕ) : ℝ) * t : ℝ) : ℂ) * Complex.I) *
        sourceScalarCutBranch a T t) =
      (Complex.I ^ (-a) * Complex.I *
        Complex.exp ((((Real.pi / 2 * (4 * (n : ℝ) + 3) * T : ℝ) : ℂ)) * Complex.I)) *
        ((2 : ℂ) * (Complex.I - 1) / ((Real.pi : ℂ) * (4 * (n : ℂ) + 3))) := by
  let c : ℂ := ((Real.pi : ℂ) / 2) * (4 * (n : ℂ) + 3) * Complex.I
  have hp : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  have hn : 4 * (n : ℂ) + 3 ≠ 0 := by
    exact_mod_cast (show 4 * (n : ℝ) + 3 ≠ 0 by positivity)
  have hc : c ≠ 0 := mul_ne_zero
    (mul_ne_zero (div_ne_zero hp (by norm_num)) hn) Complex.I_ne_zero
  have hce : Complex.exp c = -Complex.I := by
    have harg : c = ((n + 1 : ℕ) : ℂ) * (2 * (Real.pi : ℂ) * Complex.I) +
        (-(Real.pi : ℂ) / 2 * Complex.I) := by
      dsimp [c]
      push_cast
      ring
    rw [harg, Complex.exp_add, Complex.exp_nat_mul_two_pi_mul_I,
      Complex.exp_neg_pi_div_two_mul_I, one_mul]
  have heq : (fun t : ℝ =>
      Complex.exp (((2 * Real.pi * ((n + 1 : ℕ) : ℝ) * t : ℝ) : ℂ) * Complex.I) *
        sourceScalarCutBranch a T t) =
      (fun t : ℝ => Complex.I ^ (-a) *
        (Complex.exp (c * (t : ℂ)) * (if T < t then Complex.I else 1))) := by
    funext t
    have he : Complex.exp (((2 * Real.pi * ((n + 1 : ℕ) : ℝ) * t : ℝ) : ℂ) * Complex.I) *
        Complex.exp (((-Real.pi * t / 2 : ℝ) : ℂ) * Complex.I) =
        Complex.exp (c * (t : ℂ)) := by
      rw [← Complex.exp_add]
      congr 1
      dsimp [c]
      push_cast
      ring
    dsimp only [sourceScalarCutBranch]
    calc
      _ = (Complex.exp (((2 * Real.pi * ((n + 1 : ℕ) : ℝ) * t : ℝ) : ℂ) * Complex.I) *
          Complex.exp (((-Real.pi * t / 2 : ℝ) : ℂ) * Complex.I)) *
          Complex.I ^ (-a) * (if T < t then Complex.I else 1) := by ring
      _ = _ := by rw [he]; ring
  rw [heq, intervalIntegral.integral_const_mul, integral_exp_single_jump c hc hce T hT]
  have hargT : c * (T : ℂ) =
      (((Real.pi / 2 * (4 * (n : ℝ) + 3) * T : ℝ) : ℂ)) * Complex.I := by
    dsimp [c]
    push_cast
    ring
  rw [hargT]
  dsimp [c]
  field_simp [hp, hn, Complex.I_ne_zero]
  <;> ring_nf
  <;> norm_num [Complex.I_sq]
  <;> ring

theorem sourceScalarCutBranch_negative_coefficient_norm_sq (a : ℤ) (T : ℝ)
    (hT : T ∈ Icc (0 : ℝ) 1) (n : ℕ) :
    ‖∫ t in (0 : ℝ)..1,
      Complex.exp (((2 * Real.pi * ((n + 1 : ℕ) : ℝ) * t : ℝ) : ℂ) * Complex.I) *
        sourceScalarCutBranch a T t‖ ^ 2 =
      (8 / Real.pi ^ 2) * (1 / (4 * (n : ℝ) + 3) ^ 2) := by
  rw [sourceScalarCutBranch_negative_coefficient a T hT n]
  have hphase : ‖Complex.I ^ (-a) * Complex.I *
      Complex.exp ((((Real.pi / 2 * (4 * (n : ℝ) + 3) * T : ℝ) : ℂ)) * Complex.I)‖ = 1 := by
    simp [norm_mul, Complex.norm_zpow, Complex.norm_exp]
  rw [norm_mul, hphase, one_mul, ← scalar_quarter_negative_coefficient n]
  exact scalar_quarter_negative_coefficient_norm_sq n

/-- Scalar cuts have the source negative Fourier energy at every cut point. -/
theorem sourceScalarCutBranch_negative_energy (a : ℤ) (T : ℝ)
    (hT : T ∈ Icc (0 : ℝ) 1) :
    (∑' n : ℕ, ‖∫ t in (0 : ℝ)..1,
      Complex.exp (((2 * Real.pi * ((n + 1 : ℕ) : ℝ) * t : ℝ) : ℂ) * Complex.I) *
        sourceScalarCutBranch a T t‖ ^ 2) = sourceFourthRootHardyConstant := by
  simp_rw [sourceScalarCutBranch_negative_coefficient_norm_sq a T hT]
  rw [tsum_mul_left, sourceFourthRootHardyConstant_eq_positive_series]

end
end CGLMPBounds.Partition
