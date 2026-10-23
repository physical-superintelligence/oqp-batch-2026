module

public import CGLMPBounds.Partition.MixtureDerivatives
public import CGLMPBounds.Partition.FourierPairAlgebra

@[expose] public section


/-! The generic positive Fourier mixture is exactly a pair-interaction tilt
by the actual second derivative of its shape. This proves the structural
identity behind (D.10), with no source-specific Fourier expansion assumed. -/

namespace CGLMPBounds.Partition
noncomputable section

theorem fourierMixtureDensity_pair_curvature (d : ℕ) (hd : 0 < d)
    (a : ℕ → ℝ) (ha0 : ∀ n, 0 ≤ a n) (ha : Summable a) (T : Fin d → ℝ) :
    fourierMixtureDensity d a T = 1 + (1 / (d : ℝ)) *
      ∑ i : Fin d, ∑ j : Fin d,
        if i < j then fourierMixtureCurvature a (T i - T j) else 0 := by
  classical
  let g : ℕ → Fin d → Fin d → ℝ := fun n i j =>
    if i < j then
      a n * (2 * Real.cos (2 * Real.pi * ((n + 1 : ℕ) : ℝ) * (T i - T j)))
    else 0
  have hg (i j : Fin d) : Summable (fun n => g n i j) := by
    by_cases hij : i < j
    · apply (ha.mul_right 2).of_norm_bounded
      intro n
      simpa only [g, if_pos hij] using
        norm_weighted_fourierCurvature_le a ha0 n (T i - T j)
    · simp only [g, if_neg hij]
      exact summable_zero
  have hgj (i : Fin d) : Summable (fun n => ∑ j : Fin d, g n i j) :=
    summable_sum (fun j _ => hg i j)
  have hgij : Summable (fun n => ∑ i : Fin d, ∑ j : Fin d, g n i j) :=
    summable_sum (fun i _ => hgj i)
  have hswap : (∑' n, ∑ i : Fin d, ∑ j : Fin d, g n i j) =
      ∑ i : Fin d, ∑ j : Fin d,
        if i < j then fourierMixtureCurvature a (T i - T j) else 0 := by
    rw [Summable.tsum_finsetSum (fun i _ => hgj i)]
    apply Finset.sum_congr rfl
    intro i hi
    rw [Summable.tsum_finsetSum (fun j _ => hg i j)]
    apply Finset.sum_congr rfl
    intro j hj
    by_cases hij : i < j <;> simp [g, hij, fourierMixtureCurvature]
  have hpoint (n : ℕ) : a n * fourierBoundaryDensity d (n + 1) T =
      a n + (∑ i : Fin d, ∑ j : Fin d, g n i j) / d := by
    have hsum : (∑ i : Fin d, ∑ j : Fin d, g n i j) =
        a n * (2 * ∑ i : Fin d, ∑ j : Fin d,
          if i < j then Real.cos (2 * Real.pi * ((n + 1 : ℕ) : ℝ) * (T i - T j))
          else 0) := by
      simp only [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i hi
      apply Finset.sum_congr rfl
      intro j hj
      by_cases hij : i < j <;> simp [g, hij]
    rw [hsum, fourierBoundaryDensity_pair_expansion d (n + 1) hd T]
    ring
  unfold fourierMixtureDensity
  simp_rw [hpoint]
  rw [ha.tsum_add (hgij.div_const (d : ℝ)), tsum_div_const, hswap]
  unfold fourierMixtureResidual
  ring

theorem fourierMixtureDensity_pair_second_derivative (d : ℕ) (hd : 0 < d)
    (a : ℕ → ℝ) (ha0 : ∀ n, 0 ≤ a n) (ha : Summable a) (T : Fin d → ℝ) :
    fourierMixtureDensity d a T = 1 + (1 / (d : ℝ)) *
      ∑ i : Fin d, ∑ j : Fin d,
        if i < j then iteratedDeriv 2 (fourierMixtureShape a) (T i - T j) else 0 := by
  simp_rw [iteratedDeriv_two_fourierMixtureShape a ha0 ha]
  exact fourierMixtureDensity_pair_curvature d hd a ha0 ha T

end
end CGLMPBounds.Partition
