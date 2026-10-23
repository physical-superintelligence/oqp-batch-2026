module

public import CGLMPBounds.Hardy.CircleFourierCover
public import Mathlib.MeasureTheory.SpecificCodomains.Pi

@[expose] public section


/-! Exact transport of strictly negative frequencies under W(s)=sU(s⁴).
The omitted integer frequencies are proved zero; reindexing is therefore
valid even before invoking Parseval summability. -/

namespace CGLMPBounds.Hardy
open MeasureTheory Matrix
open scoped Matrix.Norms.Elementwise
noncomputable section
local instance : Fact (0 < (1 : ℝ)) := ⟨zero_lt_one⟩

theorem intervalCircleLift_negativeCoefficient {r : ℕ}
    (U : ℝ → Circulation.Mat r) (n : ℕ) :
    matrixCircleFourierCoefficient (intervalCircleLift U) (-((n+1 : ℕ) : ℤ)) =
      Partition.matrixNegativeFourierCoefficient U n := by
  unfold matrixCircleFourierCoefficient
  rw [fourierCoeff_eq_intervalIntegral _ _ 0]
  simp only [div_one, one_smul, zero_add]
  unfold Partition.matrixNegativeFourierCoefficient
  apply intervalIntegral.integral_congr_ae
  filter_upwards [] with t ht
  have ht' : t ∈ Set.Ioc (0 : ℝ) 1 := by simpa only [Set.uIoc_of_le zero_le_one] using ht
  rw [intervalCircleLift, AddCircle.liftIoc_coe_apply (by simpa only [zero_add] using ht')]
  congr 1
  rw [fourier_coe_apply]
  congr 1
  push_cast
  ring

theorem fourthRootCircleLift_negativeEnergy {r : ℕ}
    (U : ℝ → Circulation.Mat r)
    (hU : ∀ i j, MemLp (fun t => U t i j) 2 (volume.restrict (Set.Ioc (0 : ℝ) 1))) :
    matrixCircleNegativeEnergy (fourthRootCircleLift U) =
      Partition.matrixNegativeFourierEnergy U := by
  letI : ENormedAddMonoid (Circulation.Mat r) :=
    inferInstanceAs (ENormedAddMonoid (Fin r → Fin r → ℂ))
  have hi : Integrable U (volume.restrict (Set.Ioc (0 : ℝ) 1)) := by
    apply Integrable.of_eval
    intro i
    apply Integrable.of_eval
    intro j
    exact (hU i j).integrable (by norm_num)
  let g : ℕ → ℕ := fun n => 4*n+2
  let e : ℕ → ℝ := fun n => Circulation.hsSq
    (matrixCircleFourierCoefficient (fourthRootCircleLift U) (-((n+1 : ℕ) : ℤ)))
  have hinj : Function.Injective g := by
    intro a b hab
    dsimp [g] at hab
    omega
  have hsupport : Function.support e ⊆ Set.range g := by
    intro n hn
    by_contra hnot
    have hoff : ¬ ∃ j : ℤ, -((n+1 : ℕ) : ℤ) = 4*j+1 := by
      rintro ⟨j, hj⟩
      have hjneg : j < 0 := by omega
      apply hnot
      refine ⟨(-j-1).toNat, ?_⟩
      dsimp [g]
      have hcast : (((-j-1).toNat : ℕ) : ℤ) = -j-1 := Int.toNat_of_nonneg (by omega)
      omega
    apply hn
    change Circulation.hsSq (matrixCircleFourierCoefficient (fourthRootCircleLift U)
      (-((n + 1 : ℕ) : ℤ))) = 0
    rw [fourthRootCircleLift_fourierCoeff_off U hi _ hoff]
    simp [Circulation.hsSq, Circulation.reTr, Circulation.tr]
  have hterm (n : ℕ) : e (g n) =
      Circulation.hsSq (Partition.matrixNegativeFourierCoefficient U n) := by
    have hindex : -((g n+1 : ℕ) : ℤ) = 4*(-((n+1 : ℕ) : ℤ))+1 := by
      dsimp [g]
      omega
    change Circulation.hsSq (matrixCircleFourierCoefficient (fourthRootCircleLift U)
      (-((g n + 1 : ℕ) : ℤ))) = _
    rw [hindex, fourthRootCircleLift_fourierCoeff U hi,
      intervalCircleLift_negativeCoefficient]
  unfold matrixCircleNegativeEnergy Partition.matrixNegativeFourierEnergy
  change (∑' n, e n) = _
  rw [← hinj.tsum_eq hsupport]
  exact tsum_congr hterm

end
end CGLMPBounds.Hardy
