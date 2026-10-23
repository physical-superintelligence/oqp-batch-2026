module

public import CGLMPBounds.Hardy.SchwarzPositiveCluster
public import CGLMPBounds.Hardy.SchwarzResolventIntegrationByParts
public import Mathlib.Analysis.Complex.RealDeriv

@[expose] public section


/-! Real derivatives of the actual positive-part trace are the complex
coefficients of its fixed cluster contour. The parameter coefficients then
pass under that contour by the previously proved actual compact-circle
calculus. The final integration-by-parts factor is precisely (k-1)/k from
C.7; its connection to the negative-q coefficient still remains separate. -/

open Complex Filter Set Metric
open scoped Topology Matrix.Norms.Operator

namespace CGLMPBounds.Hardy
noncomputable section

lemma eventually_deriv_ofReal_eq_of_analytic_germ {f : ℝ → ℝ} {g : ℂ → ℂ}
    (hg : AnalyticAt ℂ g 0)
    (heq : (fun t : ℝ => (f t : ℂ)) =ᶠ[𝓝 0] (fun t : ℝ => g (t : ℂ))) :
    (fun t : ℝ => ((deriv f t : ℝ) : ℂ)) =ᶠ[𝓝 0] (fun t : ℝ => deriv g (t : ℂ)) := by
  have hc : Tendsto (fun t : ℝ => (t : ℂ)) (𝓝 0) (𝓝 (0 : ℂ)) := by
    simpa using Complex.continuous_ofReal.tendsto (0 : ℝ)
  filter_upwards [hc.eventually hg.eventually_analyticAt, heq.eventually_nhds] with t ht he
  have hr : f =ᶠ[𝓝 t] (fun u : ℝ => (g (u : ℂ)).re) := by
    filter_upwards [he] with u hu
    simpa using congrArg Complex.re hu
  have hd : HasDerivAt f (deriv g (t : ℂ)).re t :=
    ht.differentiableAt.hasDerivAt.real_of_complex.congr_of_eventuallyEq hr
  have hdc : HasDerivAt (fun u : ℝ => (f u : ℂ)) (deriv g (t : ℂ)) t :=
    ht.differentiableAt.hasDerivAt.comp_ofReal.congr_of_eventuallyEq he
  rw [hd.deriv]
  exact hd.ofReal_comp.unique hdc

lemma iteratedDeriv_ofReal_eq_of_analytic_germ {f : ℝ → ℝ} {g : ℂ → ℂ}
    (hg : AnalyticAt ℂ g 0)
    (heq : (fun t : ℝ => (f t : ℂ)) =ᶠ[𝓝 0] (fun t : ℝ => g (t : ℂ))) (n : ℕ) :
    ((iteratedDeriv n f 0 : ℝ) : ℂ) = iteratedDeriv n g 0 := by
  have hall : ∀ n, (fun t : ℝ => ((iteratedDeriv n f t : ℝ) : ℂ)) =ᶠ[𝓝 0]
      (fun t : ℝ => iteratedDeriv n g (t : ℂ)) := by
    intro n
    induction n generalizing f g with
    | zero => simpa only [iteratedDeriv_zero] using heq
    | succ n ih =>
      simpa only [iteratedDeriv_succ'] using ih hg.deriv
        (eventually_deriv_ofReal_eq_of_analytic_germ hg heq)
  simpa using (hall n).self_of_nhds

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
attribute [-instance] CStarMatrix.instHMulOfFintypeOfMulOfAddCommMonoid

/-- The exact local real Taylor coefficient of τ((H+tY)_+^m), with m>0,
is given by the actual positive-cluster resolvent circle. -/
theorem positiveTraceTaylorCoefficient_eq_circleIntegral {H Y : Matrix ι ι ℂ}
    (hH : H.IsHermitian) (hY : Y.IsHermitian) (hdet : IsUnit H.det)
    {m : ℕ} (hm : 0 < m) (n : ℕ) :
    let R := negativeClusterRadius H.charpoly.roots
    (positiveTraceTaylorCoefficient H Y m n : ℂ) =
      (∮ ζ in C((R : ℂ), R), ζ ^ m *
        Matrix.trace ((resolvent H ζ * Y) ^ n * resolvent H ζ)) /
          (2 * Real.pi * Complex.I : ℂ) / (Fintype.card ι : ℂ) := by
  let R := negativeClusterRadius H.charpoly.roots
  have hR : 0 ≤ R := (negativeClusterRadius_pos _).le
  have hsep : ∀ ζ ∈ sphere (R : ℂ) R, ζ ∉ spectrum ℂ H := by
    intro ζ hζ
    exact circle_not_mem_spectrum_of_root_separation H
      (fun a ha => (positiveClusterRadius_separates _
        (fun b hb => hermitian_root_re_ne_zero hH hdet hb) ha).1) hζ
  have hd := iteratedDeriv_ofReal_eq_of_analytic_germ
    (analyticAt_affine_positive_circlePowerTrace Y hH hdet m)
    (positiveTracePower_eventuallyEq_circlePowerTrace hH hY hdet hm) n
  unfold positiveTraceTaylorCoefficient
  rw [Complex.ofReal_div]
  push_cast
  rw [hd]
  simp only [circlePowerTrace, iteratedDeriv_div_const]
  calc
    _ = (iteratedDeriv n (fun t : ℂ => ∮ ζ in C((R : ℂ), R),
        ζ ^ m * Matrix.trace (resolvent (H + t • Y) ζ)) 0 / (n.factorial : ℂ)) /
          (2 * Real.pi * Complex.I : ℂ) / (Fintype.card ι : ℂ) := by ring
    _ = _ := by rw [circleIntegral_affine_resolvent_taylor_coefficient H Y hR hsep m n]

/-- The source positive contour formula, including its exact integration-
by-parts prefactor. All contour selection hypotheses are discharged by the
source Hermitian and invertibility assumptions. -/
theorem positiveTraceTaylorCoefficient_eq_positive_resolvent_power
    {H Y : Matrix ι ι ℂ} (hH : H.IsHermitian) (hY : Y.IsHermitian)
    (hdet : IsUnit H.det) {k : ℕ} (hk : 2 ≤ k) :
    let R := negativeClusterRadius H.charpoly.roots
    (positiveTraceTaylorCoefficient H Y (k - 1) k : ℂ) =
      (((k - 1 : ℕ) : ℂ) / (k : ℂ)) *
        (∮ ζ in C((R : ℂ), R), ζ ^ (k - 2) *
          Matrix.trace ((resolvent H ζ * Y) ^ k)) /
            (2 * Real.pi * Complex.I : ℂ) / (Fintype.card ι : ℂ) := by
  let R := negativeClusterRadius H.charpoly.roots
  have hsep : ∀ ζ ∈ sphere (R : ℂ) R, ζ ∉ spectrum ℂ H := by
    intro ζ hζ
    exact circle_not_mem_spectrum_of_root_separation H
      (fun a ha => (positiveClusterRadius_separates _
        (fun b hb => hermitian_root_re_ne_zero hH hdet hb) ha).1) hζ
  rw [positiveTraceTaylorCoefficient_eq_circleIntegral hH hY hdet (by omega : 0 < k - 1) k,
    circleIntegral_resolvent_power_eq_ratio H Y (negativeClusterRadius_pos _).le hsep hk]

end
end CGLMPBounds.Hardy
