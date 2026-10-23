module

public import CGLMPBounds.Hardy.HardyMatrixPotentialPinched
public import CGLMPBounds.Hardy.HardyPotentialPinchingInterior

@[expose] public section


/-! The actual C.15 boundary inequality, obtained by continuity of the
full root multiset and the actual scalar closed-strip extension. The full
C.15 integral identity remains a separate slice-convergence obligation. -/

namespace CGLMPBounds.Hardy
noncomputable section
open Set Filter
open scoped Topology
variable {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]

theorem hardyMatrix_boundary_pinching_inequality
    {B Y : Matrix ι ι ℂ} (hB : B.IsHermitian) (hB2 : B^2=1) (hY : Y.IsHermitian) :
    normalizedMatrixAbsTrace (positivePinchingPart B Y) ≤
      matrixHardyPotential (B+Complex.I • Y) := by
  have hleft := continuousOn_hardyPotential_pinching_path hB hB2
    (positivePinching_part_hermitian hB hY)
  have hright := continuousOn_hardyPotential_pinching_path hB hB2 hY
  have hmem : (1 : ℝ) ∈ Icc (0 : ℝ) 1 := ⟨zero_le_one, le_rfl⟩
  have hfilter : 𝓝[<] (1 : ℝ) ≤ 𝓝[Icc (0 : ℝ) 1] 1 := by
    change 𝓝[<] (1 : ℝ) ≤ 𝓝 (1 : ℝ) ⊓ 𝓟 (Icc (0 : ℝ) 1)
    apply le_inf nhdsWithin_le_nhds
    apply Filter.le_principal_iff.mpr
    filter_upwards [Ioo_mem_nhdsLT zero_lt_one] with ρ hρ
    exact ⟨hρ.1.le,hρ.2.le⟩
  have hl := (hleft 1 hmem).tendsto.mono_left hfilter
  have hr := (hright 1 hmem).tendsto.mono_left hfilter
  have he : ∀ᶠ ρ : ℝ in 𝓝[<] 1,
      matrixHardyPotential ((ρ : ℂ) • B+Complex.I • positivePinchingPart B Y) ≤
        matrixHardyPotential ((ρ : ℂ) • B+Complex.I • Y) := by
    filter_upwards [Ioo_mem_nhdsLT zero_lt_one] with ρ hρ
    exact hardyPotential_interior_pinching_nonneg hB hB2 hY ⟨hρ.1.le,hρ.2⟩
  have h := le_of_tendsto_of_tendsto hl hr he
  simpa only [Complex.ofReal_one, one_smul, matrixHardyPotential_pinched_boundary hB hB2 hY] using h

end
end CGLMPBounds.Hardy
