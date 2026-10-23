module

public import CGLMPBounds.Hardy.PoissonBoundaryGeometry

@[expose] public section


/-! A genuine sequence of radii and the actual extended L² norm limit.
This is an adapter from the Fourier/Parseval radial estimate to Vitali. -/
namespace CGLMPBounds.Hardy
noncomputable section
open MeasureTheory Filter Set
open scoped Topology Matrix.Norms.L2Operator
attribute [-instance] CStarMatrix.instHMulOfFintypeOfMulOfAddCommMonoid

def hardyRadialSequence (n : ℕ) : ℝ := 1-1/((n : ℝ)+1)

lemma hardyRadialSequence_mem (n : ℕ) : hardyRadialSequence n ∈ Ico (0 : ℝ) 1 := by
  have hp : (0 : ℝ) < n+1 := by positivity
  have hu : 1/((n : ℝ)+1) ≤ 1 := (div_le_iff₀ hp).mpr (by
    have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    linarith)
  have hl : (0 : ℝ) < 1/((n : ℝ)+1) := one_div_pos.mpr hp
  exact ⟨by dsimp [hardyRadialSequence]; linarith,by dsimp [hardyRadialSequence]; linarith⟩

lemma hardyRadialSequence_tendsto : Tendsto hardyRadialSequence atTop (𝓝[<] 1) := by
  apply tendsto_nhdsWithin_iff.mpr
  constructor
  · change Tendsto (fun n : ℕ => (1 : ℝ)-1/((n : ℝ)+1)) atTop (𝓝 (1 : ℝ))
    simpa only [sub_zero] using
      (tendsto_const_nhds.sub (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)))
  · exact Eventually.of_forall fun n => (hardyRadialSequence_mem n).2

lemma eLpNorm_two_eq_ofReal_sqrt_integral {α E : Type*} [MeasurableSpace α]
    [NormedAddCommGroup E] {μ : Measure α} {f : α → E} (hf : MemLp f 2 μ) :
    eLpNorm f 2 μ = ENNReal.ofReal (Real.sqrt (∫ t, ‖f t‖^2 ∂μ)) := by
  rw [MemLp.eLpNorm_eq_integral_rpow_norm (by norm_num) (by norm_num) hf]
  simp only [ENNReal.toReal_ofNat,Real.rpow_two,Real.sqrt_eq_rpow,one_div]

lemma matrixPoissonRadial_sequence_eLpNorm_tendsto {r : ℕ}
    {B : UnitCircle → Circulation.Mat r} (hB : MemLp B 2 circleMeasure) :
    Tendsto (fun n => eLpNorm
      (matrixPoissonRadial B (hardyRadialSequence n) -
        (fun t => B t+Complex.I • matrixHilbert B t)) 2 circleMeasure)
      atTop (𝓝 0) := by
  have ht := (matrixPoissonRadial_operator_L2_tendsto hB).comp hardyRadialSequence_tendsto
  have hs := (ENNReal.continuous_ofReal.comp Real.continuous_sqrt).continuousAt.tendsto.comp ht
  simp only [Function.comp_def,Real.sqrt_zero,ENNReal.ofReal_zero] at hs
  apply hs.congr'
  exact Eventually.of_forall fun n =>
    (eLpNorm_two_eq_ofReal_sqrt_integral
      (matrixPoissonRadial_error_memLp hB (hardyRadialSequence_mem n))).symm

end
end CGLMPBounds.Hardy
