module

public import VacuumBellSeparation.FreeField.WedgeModularPowers
public import VacuumBellSeparation.FreeField.WedgeWaveMultiplierDomain

@[expose] public section


/-!
# The full imaginary-rapidity strip as genuine wedge power graph vectors

The same entire original spacetime test wave used for the Tomita boundary
gives every real power in [0,1/2], with the manuscript angle 2πc and the
maximal physical domain. No analytic continuation identity is assumed.
-/

namespace VacuumBellSeparation

open MeasureTheory

theorem wedgeWave_angle_mem_strip {c : ℝ} (hc : 0 ≤ c) (hc2 : c ≤ 1 / 2) :
    (((2 * Real.pi * c : ℝ) : ℂ) * Complex.I) ∈ closedRapidityStrip := by
  change 0 ≤ (((2 * Real.pi * c : ℝ) : ℂ) * Complex.I).im ∧
    (((2 * Real.pi * c : ℝ) : ℂ) * Complex.I).im ≤ Real.pi
  simp only [Complex.mul_im, Complex.ofReal_re, Complex.I_im, mul_one,
    Complex.ofReal_im, Complex.I_re, mul_zero, add_zero]
  constructor
  · positivity
  · nlinarith [Real.pi_pos]

theorem wedgeWave_mem_physicalRapidityPower_graph {m : ℝ} (hm : 0 < m)
    (F : RealTestFunction) (hF : tsupport F.1 ⊆ leftWedge 0)
    {c : ℝ} (hc : 0 ≤ c) (hc2 : c ≤ 1 / 2) :
    (oneParticleL2 hm F, wedgeWaveL2 hm F hF
      (((2 * Real.pi * c : ℝ) : ℂ) * Complex.I) (wedgeWave_angle_mem_strip hc hc2)) ∈
        (physicalRapidityExponential hm c).graph := by
  rw [physicalRapidityExponential_mem_graph]
  have hz := wedgeWave_angle_mem_strip hc hc2
  have h := oneParticleRapidityFourier_wedgeWave_ae hm F hF hz
  simp only [wedgeWaveExtendedL2, dif_pos hz] at h
  filter_upwards [h] with ξ hξ
  rw [hξ]
  congr 1
  rw [Complex.ofReal_exp]
  congr 1
  unfold rapidityFrequencyExponent
  push_cast
  rw [mul_mul_mul_comm, Complex.I_mul_I]
  ring

end VacuumBellSeparation
