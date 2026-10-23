module

public import CGLMPBounds.Partition.ConsecutivePairAbel
public import CGLMPBounds.Partition.PairKernelIntegral
public import CGLMPBounds.Partition.HardyAbelLimit
public import CGLMPBounds.Partition.ScalarBaselineAbel

@[expose] public section


/-! The literal identity D.2. Actual bounded matrix Fourier summability,
the scalar baseline, finite matrix pairing and dominated Abel limits are
assembled without assuming the identity or a surrogate positive form.
The general Hardy lower bound is still a separate obligation. -/

namespace CGLMPBounds.Partition
open Set MeasureTheory Filter
open scoped Topology Matrix
noncomputable section

theorem consecutivePartitionHardyGap_eq_pairForm {d r : ℕ} (hr : 0 < r)
    (ℓ : ConsecutivePartition d) (V : Fin d → Circulation.Mat r)
    (hV : ∀ j, (V j)ᴴ * V j = 1) :
    consecutivePartitionHardyGap ℓ V = consecutivePartitionPairForm ℓ V := by
  let A : ℕ → Fin d → ℂ := fun n j =>
    ∫ t in (ℓ.boundary j.castSucc)..(ℓ.boundary j.succ),
      Complex.exp (((( (2 * Real.pi * (n : ℝ) + 3 * Real.pi / 2) * t : ℝ) : ℂ)) * Complex.I)
  let B : ℕ → ℂ := fun n => ∫ t in (0 : ℝ)..1,
    Complex.exp (((( (2 * Real.pi * (n : ℝ) + 3 * Real.pi / 2) * t : ℝ) : ℂ)) * Complex.I)
  let K : ℝ → Fin d → Fin d → ℂ := fun q j k =>
    ∫ p : ℝ × ℝ, quarterBranchAbelKernel q (p.2 - p.1)
      ∂((volume.restrict (Ioo (ℓ.boundary j.castSucc) (ℓ.boundary j.succ))).prod
        (volume.restrict (Ioo (ℓ.boundary k.castSucc) (ℓ.boundary k.succ))))
  let L : Fin d → Fin d → ℂ := fun j k =>
    ∫ p : ℝ × ℝ,
      -(scalarSecant (p.2 - p.1) : ℂ) / 4 +
        Complex.I * (scalarSecant (1 - (p.2 - p.1)) : ℂ) / 4
      ∂((volume.restrict (Ioo (ℓ.boundary j.castSucc) (ℓ.boundary j.succ))).prod
        (volume.restrict (Ioo (ℓ.boundary k.castSucc) (ℓ.boundary k.succ))))
  let Z : Fin d → Fin d → ℂ := fun j k => star (Circulation.corr (V j) (V k)) - 1
  have hcoef (n : ℕ) :
      matrixNegativeFourierCoefficient (consecutivePartitionBranch ℓ V) n =
        ∑ j : Fin d, A n j • (V j)ᴴ := by
    have h := consecutivePartitionBranch_negative_coefficient ℓ V n
    have hw : Real.pi / 2 * (4 * (n : ℝ) + 3) =
        2 * Real.pi * (n : ℝ) + 3 * Real.pi / 2 := by ring
    simpa only [hw] using h
  have hAsum (n : ℕ) : (∑ j : Fin d, A n j) = B n := by
    apply ℓ.sum_cell_integrals
    intro j
    exact (by fun_prop : Continuous _).intervalIntegrable
      (ℓ.boundary j.castSucc) (ℓ.boundary j.succ)
  have hB : HasSum (fun n : ℕ => ‖B n‖ ^ 2) sourceFourthRootHardyConstant := by
    have h := scalar_quarter_combined_energy_summable.hasSum
    have ht : (∑' n : ℕ, ‖B n‖ ^ 2) = sourceFourthRootHardyConstant := by
      dsimp only [B]
      simp_rw [scalar_quarter_combined_coefficient]
      exact scalar_quarter_negative_energy
    rwa [show (∑' n : ℕ, ‖∫ t in (0 : ℝ)..1,
        Complex.exp (((( (2 * Real.pi * (n : ℝ) + 3 * Real.pi / 2) * t : ℝ) : ℂ)) * Complex.I)‖ ^ 2) =
        sourceFourthRootHardyConstant from ht] at h
  have hE := (consecutivePartitionBranch_fourier_summable ℓ V).hasSum
  have hD : HasSum (fun n : ℕ =>
      Circulation.hsSq (∑ j, A n j • (V j)ᴴ) - ‖∑ j, A n j‖ ^ 2)
      (consecutivePartitionHardyGap ℓ V) := by
    have h := hE.sub hB
    simpa only [hcoef, hAsum, matrixNegativeFourierEnergy, consecutivePartitionHardyGap] using h
  have hleft := Real.tendsto_tsum_powerSeries_nhdsWithin_lt hD.tendsto_sum_nat
  have hb (j : Fin d) : ℓ.boundary j.castSucc ≤ ℓ.boundary j.succ :=
    ℓ.monotone_boundary (by exact_mod_cast (show j.val ≤ j.val + 1 by omega))
  have hbounds (i : Fin (d + 1)) : ℓ.boundary i ∈ Icc (0 : ℝ) 1 := by
    constructor
    · rw [← ℓ.boundary_zero]
      exact ℓ.monotone_boundary (Fin.zero_le _)
    · rw [← ℓ.boundary_one]
      exact ℓ.monotone_boundary (Fin.le_last _)
  have hsep {j k : Fin d} (hjk : j < k) : ℓ.boundary j.succ ≤ ℓ.boundary k.castSucc :=
    ℓ.monotone_boundary (by exact_mod_cast (show j.val + 1 ≤ k.val from hjk))
  have hpairlim (j k : Fin d) :
      Tendsto (fun q : ℝ => if j < k then (K q j k * Z j k).re else 0)
        (𝓝[<] (1 : ℝ)) (𝓝 (if j < k then (L j k * Z j k).re else 0)) := by
    by_cases hjk : j < k
    · simp only [if_pos hjk]
      have h := quarterBranchAbelKernel_rectangle_tendsto
        (hbounds j.castSucc).1 (hb j) (hsep hjk) (hb k) (hbounds k.succ).2
      exact (Complex.continuous_re.tendsto _).comp (h.mul_const (Z j k))
    · simp only [if_neg hjk]
      exact tendsto_const_nhds
  have hright := (tendsto_finsetSum Finset.univ (fun j _ =>
    tendsto_finsetSum Finset.univ (fun k _ => hpairlim j k))).const_mul (2 : ℝ)
  have hevent : (fun q : ℝ => ∑' n : ℕ,
      (Circulation.hsSq (∑ j, A n j • (V j)ᴴ) - ‖∑ j, A n j‖ ^ 2) * q ^ n) =ᶠ[𝓝[<] (1 : ℝ)]
      (fun q : ℝ => 2 * ∑ j : Fin d, ∑ k : Fin d,
        if j < k then (K q j k * Z j k).re else 0) := by
    have hpos : ∀ᶠ q : ℝ in 𝓝[<] (1 : ℝ), 0 < q :=
      (eventually_gt_nhds (by norm_num : (0 : ℝ) < 1)).filter_mono nhdsWithin_le_nhds
    filter_upwards [hpos, self_mem_nhdsWithin] with q hq₀ hq₁
    exact (consecutivePartition_damped_pair_hasSum hr ℓ V hV q hq₀.le hq₁).tsum_eq
  have hlimit : consecutivePartitionHardyGap ℓ V =
      2 * ∑ j : Fin d, ∑ k : Fin d, if j < k then (L j k * Z j k).re else 0 :=
    tendsto_nhds_unique (hleft.congr' hevent) hright
  rw [hlimit]
  unfold consecutivePartitionPairForm
  simp only [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro k _
  by_cases hjk : j < k
  · simp only [if_pos hjk]
    exact quarterBranch_pair_kernel_rectangle_identity
      (hbounds j.castSucc).1 (hb j) (hsep hjk) (hb k) (hbounds k.succ).2
      (Circulation.corr (V j) (V k))
  · simp only [if_neg hjk, mul_zero]

end
end CGLMPBounds.Partition
