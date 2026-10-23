module

public import CGLMPBounds.Defs.HardyMatrixPotential
public import CGLMPBounds.Hardy.HardyPotentialClosedStrip
public import CGLMPBounds.Hardy.RootContinuity
public import CGLMPBounds.Hardy.HolomorphicPinchingRectangle

@[expose] public section


/-! Continuity of the actual root-trace potential for nonnormal matrices
whose spectra lie in the closed strip. A continuous scalar retraction
extends the observable globally solely for the root-continuity proof;
the manuscript potential itself remains unchanged. -/

namespace CGLMPBounds.Hardy
noncomputable section
open Set Matrix
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

private def closedStripRetraction (z : ℂ) : ℂ :=
  ((max (-1 : ℝ) (min 1 z.re) : ℝ) : ℂ) + Complex.I*z.im

private lemma continuous_closedStripRetraction : Continuous closedStripRetraction := by
  unfold closedStripRetraction
  fun_prop

private lemma closedStripRetraction_mem (z : ℂ) :
    |(closedStripRetraction z).re| ≤ 1 := by
  simp only [closedStripRetraction, Complex.add_re, Complex.ofReal_re,
    Complex.I_mul_re, Complex.ofReal_im, neg_zero, add_zero]
  exact abs_le.mpr ⟨le_max_left _ _, max_le (by norm_num) (min_le_left _ _)⟩

private lemma closedStripRetraction_eq {z : ℂ} (hz : |z.re| ≤ 1) :
    closedStripRetraction z=z := by
  have he : max (-1 : ℝ) (min 1 z.re)=z.re := by
    rw [min_eq_right (abs_le.mp hz).2, max_eq_right (abs_le.mp hz).1]
  rw [closedStripRetraction, he]
  apply Complex.ext <;> simp

lemma matrixHardyPotential_eq_root_sum (A : Matrix ι ι ℂ) :
    matrixHardyPotential A =
      (A.charpoly.roots.map (fun z => (hardyStripPotential z).re)).sum /
        (Fintype.card ι : ℝ) := by
  unfold matrixHardyPotential normalizedSpectralTrace
  rw [← charpolyRootVector_multiset]
  simp only [Multiset.map_map]
  change ((∑ i, hardyStripPotential (charpolyRootVector A i)) /
    (Fintype.card ι : ℂ)).re =
      (∑ i, (hardyStripPotential (charpolyRootVector A i)).re) / (Fintype.card ι : ℝ)
  simp only [Complex.div_natCast_re, Complex.re_sum]

theorem continuousOn_matrixHardyPotential_closed_spectrum :
    ContinuousOn (matrixHardyPotential (ι := ι))
      {A : Matrix ι ι ℂ | ∀ z ∈ spectrum ℂ A, |z.re| ≤ 1} := by
  let f : ℂ → ℝ := fun z => (hardyStripPotential (closedStripRetraction z)).re
  have hf : Continuous f := continuousOn_hardyStripPotential_re_closed.comp_continuous
    continuous_closedStripRetraction closedStripRetraction_mem
  have hc := (continuous_charpoly_root_sum (ι := ι) f hf).div_const (Fintype.card ι : ℝ)
  apply hc.continuousOn.congr
  intro A hA
  rw [matrixHardyPotential_eq_root_sum]
  congr 1
  apply congrArg Multiset.sum
  apply Multiset.map_congr rfl
  intro z hz
  have hzs := Matrix.mem_spectrum_of_isRoot_charpoly (Polynomial.isRoot_of_mem_roots hz)
  simp only [f, closedStripRetraction_eq (hA z hzs)]

theorem continuousOn_hardyPotential_pinching_path [Nonempty ι]
    {B Y : Matrix ι ι ℂ} (hB : B.IsHermitian) (hB2 : B^2=1) (hY : Y.IsHermitian) :
    ContinuousOn (fun ρ : ℝ => matrixHardyPotential ((ρ : ℂ) • B + Complex.I • Y))
      (Icc (0 : ℝ) 1) := by
  apply continuousOn_matrixHardyPotential_closed_spectrum.comp (by fun_prop)
  intro ρ hρ z hz
  exact ((positivePinching_spectra_rectangle hB hB2 hY hρ.1).1 z hz).1.trans hρ.2

end
end CGLMPBounds.Hardy
