module

public import CGLMPBounds.Certificates.ScalarSmooth
public import CGLMPBounds.Defs.ScalarBeta

@[expose] public section


/-!
# Identifying the actual correction in (D.6)

On the integration interval, pole subtraction converts the source's twice
differentiated expression into the regularized cosecant series. Endpoint
values are excluded here; the forthcoming integral bridge uses almost-everywhere
equality and proves integrability separately.
-/

namespace CGLMPBounds.Certificates
noncomputable section
open scoped Topology

lemma scalarSecant_reflected (x : ℝ) :
    scalarSecant x = 1 / Real.sin (Real.pi * (1 - x) / 2) := by
  unfold scalarSecant
  rw [show Real.pi * (1 - x) / 2 = Real.pi / 2 - Real.pi * x / 2 by ring,
    Real.sin_pi_div_two_sub]

lemma scalarPhi_reflection_mem {x : ℝ} (hx : x ∈ Set.Ioo (0 : ℝ) 1) :
    1 - x ∈ Set.Ioo (0 : ℝ) 1 := by
  constructor <;> linarith [hx.1, hx.2]

theorem scalarCorrection_base_eq {x : ℝ} (hx : x ∈ Set.Ioo (0 : ℝ) 1) :
    x * (1 - x) * scalarSecant x - 2 * x / Real.pi = scalarPhiSeries 0 (1 - x) := by
  have hy := scalarPhi_reflection_mem hx
  rw [scalarPhiSeries_zero_order ⟨hy.1.le, hy.2.le⟩, scalarSecant_reflected]
  have hy0 : 1 - x ≠ 0 := hy.1.ne'
  field_simp [Real.pi_ne_zero, hy0]
  <;> ring

theorem scalarPhi_reflected_hasDerivAt (m : ℕ) {x : ℝ}
    (hx : x ∈ Set.Ioo (0 : ℝ) 1) :
    HasDerivAt (fun t => scalarPhiSeries m (1 - t)) (-scalarPhiSeries (m + 1) (1 - x)) x := by
  have h := (scalarPhiSeries_hasDerivAt m (scalarPhi_reflection_mem hx)).comp x
    ((hasDerivAt_const x (1 : ℝ)).sub (hasDerivAt_id x))
  simpa only [zero_sub, mul_neg, mul_one] using! h

theorem scalarCorrection_base_hasDerivAt {x : ℝ} (hx : x ∈ Set.Ioo (0 : ℝ) 1) :
    HasDerivAt (fun t => t * (1 - t) * scalarSecant t - 2 * t / Real.pi)
      (-scalarPhiSeries 1 (1 - x)) x := by
  apply (scalarPhi_reflected_hasDerivAt 0 hx).congr_of_eventuallyEq
  filter_upwards [isOpen_Ioo.mem_nhds hx] with t ht
  exact scalarCorrection_base_eq ht

/-- The source correction b is the actual second derivative of the regularized
series, with its minus-one-half coefficient and reflected argument. -/
theorem scalarCorrectionB_eq_series {x : ℝ} (hx : x ∈ Set.Ioo (0 : ℝ) 1) :
    scalarCorrectionB x = -(1 : ℝ) / 2 * scalarPhiSeries 2 (1 - x) := by
  have h := (scalarPhi_reflected_hasDerivAt 1 hx).neg
  have he : deriv (fun t => t * (1 - t) * scalarSecant t - 2 * t / Real.pi) =ᶠ[𝓝 x]
      (fun t => -scalarPhiSeries 1 (1 - t)) := by
    filter_upwards [isOpen_Ioo.mem_nhds hx] with t ht
    exact (scalarCorrection_base_hasDerivAt ht).deriv
  have hsecond := h.congr_of_eventuallyEq he
  have hsecond' := hsecond.deriv
  simp only [neg_neg] at hsecond'
  unfold scalarCorrectionB
  rw [show (2 : ℕ) = 1 + 1 by omega, iteratedDeriv_succ, iteratedDeriv_one, hsecond']

end
end CGLMPBounds.Certificates
