module

public import CGLMPBounds.Partition.PotentialProduct

@[expose] public section


/-! Removable endpoint regularity of the actual product v(x)sec(πx/2).
The nonsingular sinc expression justifies integration by parts on [0,1]
without assuming bounded endpoint derivatives. -/

namespace CGLMPBounds.Partition
open Set
noncomputable section

def regularizedSecantCut (x : ℝ) : ℝ :=
  (2 / Real.pi) * x / Real.sinc ((Real.pi / 2) * (1 - x)) - 2 * x / Real.pi

def regularizedPotentialProduct (x : ℝ) : ℝ :=
  -(1 : ℝ) / 2 * regularizedSecantCut x - 1 / (2 * Real.pi) +
    regularizedCotangentMoment (x - 1 / 2) / Real.pi

lemma analyticAt_regularizedSecantCut {x : ℝ} (hx : x ∈ Icc (0 : ℝ) 1) :
    AnalyticAt ℝ regularizedSecantCut x := by
  have harg : |(Real.pi / 2) * (1 - x)| < Real.pi := by
    rw [abs_lt]
    constructor <;> nlinarith [Real.pi_pos, hx.1, hx.2]
  have hs : Real.sinc ((Real.pi / 2) * (1 - x)) ≠ 0 := (Real.sinc_pos harg).ne'
  have hn : AnalyticAt ℝ (fun t : ℝ => (2 / Real.pi) * t) x := by fun_prop
  have hi : AnalyticAt ℝ (fun t : ℝ => (Real.pi / 2) * (1 - t)) x := by fun_prop
  unfold regularizedSecantCut
  exact (hn.div ((analyticAt_real_sinc _).comp hi) hs).sub (by fun_prop)

lemma analyticAt_regularizedPotentialProduct {x : ℝ} (hx : x ∈ Icc (0 : ℝ) 1) :
    AnalyticAt ℝ regularizedPotentialProduct x := by
  have hu : |x - 1 / 2| ≤ 1 := by
    rw [abs_le]
    constructor <;> linarith [hx.1, hx.2]
  unfold regularizedPotentialProduct
  exact ((analyticAt_const.mul (analyticAt_regularizedSecantCut hx)).sub analyticAt_const).add
    (((analyticAt_regularizedCotangentMoment hu).comp
      (f := fun t : ℝ => t - 1 / 2) (x := x) (by fun_prop)).div_const (c := Real.pi))

lemma regularizedSecantCut_eq_interior {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    regularizedSecantCut x = x * (1 - x) * scalarSecant x - 2 * x / Real.pi := by
  have hp := Real.pi_ne_zero
  have harg : (Real.pi / 2) * (1 - x) ≠ 0 :=
    mul_ne_zero (by positivity) (sub_ne_zero.mpr hx.2.ne')
  have hc : Real.cos (Real.pi * x / 2) ≠ 0 := by
    apply (Real.cos_pos_of_mem_Ioo _).ne'
    constructor <;> nlinarith [Real.pi_pos, hx.1, hx.2]
  have hs : Real.sin ((Real.pi / 2) * (1 - x)) = Real.cos (Real.pi * x / 2) := by
    rw [show (Real.pi / 2) * (1 - x) = Real.pi / 2 - Real.pi * x / 2 by ring,
      Real.sin_pi_div_two_sub]
  unfold regularizedSecantCut scalarSecant
  rw [Real.sinc_of_ne_zero harg, hs]
  field_simp [hp, hc]
  <;> ring

lemma regularizedCotangentMoment_half : regularizedCotangentMoment (1 / 2) = 1 / 2 := by
  rw [regularizedCotangentMoment_eq (by norm_num : (1 / 2 : ℝ) ≠ 0)]
  rw [show (Real.pi / 2) * (1 / 2) = Real.pi / 4 by ring,
    Real.cos_pi_div_four, Real.sin_pi_div_four]
  have hs : Real.sqrt 2 ≠ 0 := by positivity
  field_simp [hs]
  <;> ring

lemma regularizedCotangentMoment_even (u : ℝ) :
    regularizedCotangentMoment (-u) = regularizedCotangentMoment u := by
  simp [regularizedCotangentMoment, Real.cos_neg, Real.sinc_neg]

lemma regularizedPotentialProduct_zero : regularizedPotentialProduct 0 = 0 := by
  have hcot : regularizedCotangentMoment ((0 : ℝ) - 1 / 2) = 1 / 2 := by
    rw [show (0 : ℝ) - 1 / 2 = -(1 / 2) by ring,
      regularizedCotangentMoment_even, regularizedCotangentMoment_half]
  simp only [regularizedPotentialProduct, regularizedSecantCut, mul_zero, zero_div,
    sub_zero, hcot]
  ring

lemma regularizedPotentialProduct_one : regularizedPotentialProduct 1 = 0 := by
  have hcot : regularizedCotangentMoment ((1 : ℝ) - 1 / 2) = 1 / 2 := by
    rw [show (1 : ℝ) - 1 / 2 = 1 / 2 by ring, regularizedCotangentMoment_half]
  simp only [regularizedPotentialProduct, regularizedSecantCut, mul_one, sub_self,
    mul_zero, Real.sinc_zero, div_one, hcot]
  ring

lemma potential_secant_product_eq_regularized {x : ℝ} (hx : x ∈ Icc (0 : ℝ) 1) :
    partitionPotential x * scalarSecant x = regularizedPotentialProduct x := by
  by_cases hx0 : x = 0
  · subst x
    rw [partitionPotential_zero, zero_mul, regularizedPotentialProduct_zero]
  by_cases hx1 : x = 1
  · subst x
    rw [partitionPotential_one, zero_mul, regularizedPotentialProduct_one]
  have hxi : x ∈ Ioo (0 : ℝ) 1 :=
    ⟨lt_of_le_of_ne hx.1 (Ne.symm hx0), lt_of_le_of_ne hx.2 hx1⟩
  rw [potential_secant_product_eq hxi, regularizedPotentialProduct,
    regularizedSecantCut_eq_interior hxi]

theorem potential_secant_product_contDiffOn :
    ContDiffOn ℝ ⊤ (fun x => partitionPotential x * scalarSecant x) (Icc (0 : ℝ) 1) := by
  have hreg : ContDiffOn ℝ ⊤ regularizedPotentialProduct (Icc (0 : ℝ) 1) :=
    fun x hx => (analyticAt_regularizedPotentialProduct hx).contDiffAt.contDiffWithinAt
  apply hreg.congr
  exact fun x hx => potential_secant_product_eq_regularized hx

end
end CGLMPBounds.Partition
