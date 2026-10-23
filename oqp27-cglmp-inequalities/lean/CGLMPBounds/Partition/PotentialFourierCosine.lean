module

public import CGLMPBounds.Partition.PotentialFourierSummable

@[expose] public section


/-! Two genuine integrations by parts identify the source D.9 coefficient
with the cosine coefficient of the actual second derivative. The compact
within derivatives provide the required endpoint regularity without adding
any boundary-value assumption. -/

namespace CGLMPBounds.Partition
open Set MeasureTheory
noncomputable section

lemma partitionPotential_derivativeWithin_continuous (m : ℕ) :
    ContinuousOn (iteratedDerivWithin m partitionPotential (Icc (0 : ℝ) 1))
      (Icc (0 : ℝ) 1) :=
  partitionPotential_contDiffOn.continuousOn_iteratedDerivWithin (by simp)
    (uniqueDiffOn_Icc (by norm_num : (0 : ℝ) < 1))

lemma partitionPotential_derivativeWithin_hasDerivWithinAt (m : ℕ) {x : ℝ}
    (hx : x ∈ Icc (0 : ℝ) 1) :
    HasDerivWithinAt (iteratedDerivWithin m partitionPotential (Icc (0 : ℝ) 1))
      (iteratedDerivWithin (m + 1) partitionPotential (Icc (0 : ℝ) 1) x)
      (Icc (0 : ℝ) 1) x := by
  have h := (partitionPotential_contDiffOn.differentiableOn_iteratedDerivWithin
    (m := m) (by simp) (uniqueDiffOn_Icc (by norm_num : (0 : ℝ) < 1)) x hx).hasDerivWithinAt
  simpa only [iteratedDerivWithin_succ] using h

lemma partitionPotential_derivativeWithin_intervalIntegrable (m : ℕ) :
    IntervalIntegrable (iteratedDerivWithin m partitionPotential (Icc (0 : ℝ) 1))
      volume 0 1 :=
  (partitionPotential_derivativeWithin_continuous m).intervalIntegrable_of_Icc (by norm_num)

theorem partitionFourierCoefficient_eq_cosine (n : ℕ) :
    partitionFourierCoefficient n = ∫ x in (0 : ℝ)..1,
      iteratedDerivWithin 2 partitionPotential (Icc (0 : ℝ) 1) x *
        Real.cos (2 * Real.pi * ((n + 1 : ℕ) : ℝ) * x) := by
  let D : ℕ → ℝ → ℝ := fun m =>
    iteratedDerivWithin m partitionPotential (Icc (0 : ℝ) 1)
  let k : ℝ := 2 * Real.pi * ((n + 1 : ℕ) : ℝ)
  have hk : k ≠ 0 := by dsimp [k]; positivity
  have hkn : k = ((n + 1 : ℕ) : ℝ) * (2 * Real.pi) := by dsimp [k]; ring
  have hsin1 : Real.sin k = 0 := by
    rw [hkn]
    simpa using Real.sin_add_nat_mul_two_pi (0 : ℝ) (n + 1)
  have hcos1 : Real.cos k = 1 := by rw [hkn, Real.cos_nat_mul_two_pi]
  have hs (x : ℝ) : HasDerivAt (fun t : ℝ => Real.sin (k * t))
      (k * Real.cos (k * x)) x := by
    convert ((hasDerivAt_id x).const_mul k).sin using 1
    · rfl
    · simp only [id_eq, mul_one]
      ring
  have hc (x : ℝ) : HasDerivAt (fun t : ℝ => 1 - Real.cos (k * t))
      (k * Real.sin (k * x)) x := by
    convert (hasDerivAt_const x (1 : ℝ)).sub
      (((hasDerivAt_id x).const_mul k).cos) using 1
    · rfl
    · simp only [id_eq, mul_one]
      ring
  have hI : uIcc (0 : ℝ) 1 = Icc (0 : ℝ) 1 := uIcc_of_le (by norm_num)
  have h1 := intervalIntegral.integral_mul_deriv_eq_deriv_mul_of_hasDerivWithinAt
    (a := (0 : ℝ)) (b := 1)
    (u := fun x => 1 - Real.cos (k * x)) (u' := fun x => k * Real.sin (k * x))
    (v := D 3) (v' := D 4)
    (fun x _ => (hc x).hasDerivWithinAt)
    (by simpa only [hI] using
      (fun x hx => partitionPotential_derivativeWithin_hasDerivWithinAt 3 hx))
    ((show Continuous (fun x : ℝ => k * Real.sin (k * x)) by fun_prop).intervalIntegrable _ _)
    (partitionPotential_derivativeWithin_intervalIntegrable 4)
  have h2 := intervalIntegral.integral_mul_deriv_eq_deriv_mul_of_hasDerivWithinAt
    (a := (0 : ℝ)) (b := 1)
    (u := fun x => Real.sin (k * x)) (u' := fun x => k * Real.cos (k * x))
    (v := D 2) (v' := D 3)
    (fun x _ => (hs x).hasDerivWithinAt)
    (by simpa only [hI] using
      (fun x hx => partitionPotential_derivativeWithin_hasDerivWithinAt 2 hx))
    ((show Continuous (fun x : ℝ => k * Real.cos (k * x)) by fun_prop).intervalIntegrable _ _)
    (partitionPotential_derivativeWithin_intervalIntegrable 3)
  simp only [mul_one, mul_zero, Real.cos_zero, Real.sin_zero, hcos1, hsin1,
    sub_self, zero_mul, sub_zero, zero_sub] at h1 h2
  have h1' : (∫ x in (0 : ℝ)..1, D 4 x * (1 - Real.cos (k * x))) =
      -k * ∫ x in (0 : ℝ)..1, D 3 x * Real.sin (k * x) := by
    calc
      _ = ∫ x in (0 : ℝ)..1, (1 - Real.cos (k * x)) * D 4 x := by
        apply intervalIntegral.integral_congr
        intro x _
        ring
      _ = -(∫ x in (0 : ℝ)..1, k * Real.sin (k * x) * D 3 x) := h1
      _ = -k * ∫ x in (0 : ℝ)..1, D 3 x * Real.sin (k * x) := by
        rw [show (fun x => k * Real.sin (k * x) * D 3 x) =
          (fun x => k * (D 3 x * Real.sin (k * x))) by funext x; ring,
          intervalIntegral.integral_const_mul]
        ring
  have h2' : (∫ x in (0 : ℝ)..1, D 3 x * Real.sin (k * x)) =
      -k * ∫ x in (0 : ℝ)..1, D 2 x * Real.cos (k * x) := by
    calc
      _ = ∫ x in (0 : ℝ)..1, Real.sin (k * x) * D 3 x := by
        apply intervalIntegral.integral_congr
        intro x _
        ring
      _ = -(∫ x in (0 : ℝ)..1, k * Real.cos (k * x) * D 2 x) := h2
      _ = -k * ∫ x in (0 : ℝ)..1, D 2 x * Real.cos (k * x) := by
        rw [show (fun x => k * Real.cos (k * x) * D 2 x) =
          (fun x => k * (D 2 x * Real.cos (k * x))) by funext x; ring,
          intervalIntegral.integral_const_mul]
        ring
  rw [partitionFourierCoefficient_eq_within]
  change (1 / (4 * Real.pi ^ 2 * ((n + 1 : ℕ) : ℝ) ^ 2)) *
    (∫ x in (0 : ℝ)..1, D 4 x * (1 - Real.cos (k * x))) = _
  rw [h1', h2']
  change _ = ∫ x in (0 : ℝ)..1, D 2 x * Real.cos (k * x)
  dsimp [k]
  field_simp [Real.pi_ne_zero, show ((n + 1 : ℕ) : ℝ) ≠ 0 by positivity]
  <;> ring

end
end CGLMPBounds.Partition
