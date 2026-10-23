module

public import CGLMPBounds.Hardy.PolynomialResolventIntegrationByParts
public import CGLMPBounds.Hardy.SchwarzContourCoefficients
public import CGLMPBounds.Hardy.SchwarzCirclePowerTrace
public import CGLMPBounds.Hardy.PositivePinchingUnitary
public import Mathlib.Analysis.Analytic.IsolatedZeros

@[expose] public section


/-! Actual Taylor coefficients of a matrix power trace on a whole-spectrum
circle. The spectral theorem identifies the contour for real Hermitian
perturbations; analytic uniqueness supplies its complex germ. Actual compact-
circle differentiation and integration by parts give the coefficient N/k. -/

namespace CGLMPBounds.Hardy
noncomputable section
open Complex Matrix Filter Metric Set Unitary
open scoped Topology Matrix.Norms.Operator
attribute [-instance] CStarMatrix.instHMulOfFintypeOfMulOfAddCommMonoid

lemma analytic_eventuallyEq_of_real_line {f g : ℂ → ℂ}
    (hf : AnalyticAt ℂ f 0) (hg : AnalyticAt ℂ g 0)
    (heq : ∀ᶠ t : ℝ in 𝓝 0, f (t : ℂ) = g (t : ℂ)) : f =ᶠ[𝓝 0] g := by
  have ht : Tendsto (fun t : ℝ => (t : ℂ)) (𝓝[≠] 0) (𝓝[≠] (0 : ℂ)) := by
    apply tendsto_nhdsWithin_iff.mpr
    constructor
    · simpa only [Complex.ofReal_zero] using
        (Complex.continuous_ofReal.tendsto (0 : ℝ)).mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with t ht
      change t ≠ 0 at ht
      change (t : ℂ) ≠ 0
      exact_mod_cast ht
  exact (hf.frequently_eq_iff_eventually_eq hg).mp
    (ht.frequently (heq.filter_mono nhdsWithin_le_nhds).frequently)

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

lemma hermitian_trace_pow_eq_root_sum {A : Matrix ι ι ℂ} (hA : A.IsHermitian) (N : ℕ) :
    Matrix.trace (A ^ N) = (A.charpoly.roots.map (fun a => a ^ N)).sum := by
  have htrace : Matrix.trace (A ^ N) =
      ∑ i : ι, ((hA.eigenvalues i : ℝ) : ℂ) ^ N := by
    conv_lhs => rw [hA.spectral_theorem, ← map_pow, trace_conjStarAlgAut,
      Matrix.diagonal_pow, Matrix.trace_diagonal]
    rfl
  rw [htrace, hA.roots_charpoly_eq_eigenvalues]
  simp only [Multiset.map_map, Function.comp_def]
  rfl

lemma circlePowerTrace_eq_trace_pow_of_all_roots {A : Matrix ι ι ℂ}
    (hA : A.IsHermitian) (N : ℕ) {c : ℂ} {R : ℝ} (hR : 0 ≤ R)
    (hin : ∀ a ∈ A.charpoly.roots, a ∈ ball c R) :
    circlePowerTrace A N c R = Matrix.trace (A ^ N) / (Fintype.card ι : ℂ) := by
  have hsep : ∀ a ∈ A.charpoly.roots, a ∉ sphere c R := by
    intro a ha hs
    have hlt : dist a c < R := hin a ha
    have heq := Metric.mem_sphere.mp hs
    linarith
  rw [circlePowerTrace_eq_root_sum A N hR hsep, hermitian_trace_pow_eq_root_sum hA]
  congr 1
  congr 1
  apply Multiset.map_congr rfl
  intro a ha
  rw [if_pos (hin a ha)]

lemma eventually_affine_roots_inside_circle (H Y : Matrix ι ι ℂ) {c : ℂ} {R : ℝ}
    (hin : spectrum ℂ H ⊆ ball c R) :
    ∀ᶠ t in 𝓝 (0 : ℂ), ∀ a ∈ (H + t • Y).charpoly.roots, a ∈ ball c R := by
  have hcont : ContinuousAt (fun t : ℂ => H + t • Y) 0 := by fun_prop
  have hhemi : UpperHemicontinuousAt (fun t : ℂ => spectrum ℂ (H + t • Y)) 0 :=
    ((upperHemicontinuous_spectrum ℂ (Matrix ι ι ℂ)).upperHemicontinuousAt
      (H + (0 : ℂ) • Y)).comp (g := fun t : ℂ => H + t • Y) hcont
  have hsub : spectrum ℂ (H + (0 : ℂ) • Y) ⊆ ball c R := by simpa using hin
  filter_upwards [hhemi.forall_isOpen (ball c R) isOpen_ball hsub] with t ht a ha
  exact ht (Matrix.mem_spectrum_of_isRoot_charpoly (Polynomial.isRoot_of_mem_roots ha))

lemma analyticAt_affine_whole_circlePowerTrace (H Y : Matrix ι ι ℂ) (N : ℕ)
    {c : ℂ} {R : ℝ} (hR : 0 ≤ R) (hin : spectrum ℂ H ⊆ ball c R) :
    AnalyticAt ℂ (fun t : ℂ => circlePowerTrace (H + t • Y) N c R) 0 := by
  have hF : ∀ᶠ t in 𝓝 (0 : ℂ), ∀ ζ ∈ sphere c |R|,
      AnalyticAt ℂ (fun p : ℂ × ℂ =>
        p.2 ^ N * Matrix.trace (resolvent (H + p.1 • Y) p.2)) (t, ζ) := by
    filter_upwards [eventually_affine_roots_inside_circle H Y hin] with t ht
    intro ζ hζ
    apply analyticAt_affine_resolvent_trace_joint
    apply circle_not_mem_spectrum_of_root_separation (H + t • Y) _
      (by simpa only [abs_of_nonneg hR] using hζ)
    intro a ha hs
    have hlt : dist a c < R := ht a ha
    have heq := Metric.mem_sphere.mp hs
    linarith
  apply analyticAt_iff_eventually_differentiableAt.mpr
  filter_upwards [hF.eventually_nhds] with t ht
  have hd := (hasDerivAt_circleIntegral_of_joint_analytic ht).differentiableAt
  exact (hd.div_const (2 * Real.pi * Complex.I : ℂ)).div_const (Fintype.card ι : ℂ)

lemma trace_pow_eventuallyEq_whole_circlePowerTrace {H Y : Matrix ι ι ℂ}
    (hH : H.IsHermitian) (hY : Y.IsHermitian) (N : ℕ)
    {c : ℂ} {R : ℝ} (hR : 0 ≤ R) (hin : spectrum ℂ H ⊆ ball c R) :
    (fun t : ℂ => Matrix.trace ((H + t • Y) ^ N) / (Fintype.card ι : ℂ)) =ᶠ[𝓝 0]
      (fun t => circlePowerTrace (H + t • Y) N c R) := by
  have htrace : AnalyticAt ℂ
      (fun t : ℂ => Matrix.trace ((H + t • Y) ^ N) / (Fintype.card ι : ℂ)) 0 := by
    let tr : Matrix ι ι ℂ →L[ℂ] ℂ := (Matrix.traceLinearMap ι ℂ ℂ).toContinuousLinearMap
    exact ((tr.analyticAt _).comp
      ((analyticAt_const.add (analyticAt_id.smul analyticAt_const)).pow N)).div_const
  apply analytic_eventuallyEq_of_real_line htrace
    (analyticAt_affine_whole_circlePowerTrace H Y N hR hin)
  have hc : Tendsto (fun t : ℝ => (t : ℂ)) (𝓝 0) (𝓝 (0 : ℂ)) := by
    simpa using Complex.continuous_ofReal.tendsto (0 : ℝ)
  filter_upwards [hc.eventually (eventually_affine_roots_inside_circle H Y hin)] with t ht
  have hA : (H + (t : ℂ) • Y).IsHermitian := hH.add (hY.smul (by simp [IsSelfAdjoint]))
  exact (circlePowerTrace_eq_trace_pow_of_all_roots hA N hR ht).symm

theorem trace_pow_taylor_coefficient_whole_circle {H Y : Matrix ι ι ℂ}
    (hH : H.IsHermitian) (hY : Y.IsHermitian) {k N : ℕ} (hk : 0 < k) (hN : 0 < N)
    {c : ℂ} {R : ℝ} (hR : 0 ≤ R) (hin : spectrum ℂ H ⊆ ball c R) :
    iteratedDeriv k (fun t : ℂ => Matrix.trace ((H + t • Y) ^ N)) 0 /
      ((k.factorial : ℂ) * (Fintype.card ι : ℂ)) =
    ((N : ℂ) / k) * (∮ z in C(c, R), z ^ (N - 1) *
      Matrix.trace ((resolvent H z * Y) ^ k)) /
        (2 * Real.pi * Complex.I : ℂ) / (Fintype.card ι : ℂ) := by
  have hsep : ∀ z ∈ sphere c R, z ∉ spectrum ℂ H := by
    intro z hz hs
    have hlt : dist z c < R := hin hs
    have heq := Metric.mem_sphere.mp hz
    linarith
  have hd := (trace_pow_eventuallyEq_whole_circlePowerTrace hH hY N hR hin).iteratedDeriv_eq k
  have he : (∮ z in C(c, R), z ^ N *
      Matrix.trace ((resolvent H z * Y) ^ k * resolvent H z)) =
      ((N : ℂ) / k) * (∮ z in C(c, R), z ^ (N - 1) *
        Matrix.trace ((resolvent H z * Y) ^ k)) := by
    have hb := circleIntegral_polynomial_resolvent_integrationByParts H Y hR hsep hk hN
    have hk0 : (k : ℂ) ≠ 0 := by exact_mod_cast hk.ne'
    apply mul_left_cancel₀ hk0
    calc
      (k : ℂ) * _ = (N : ℂ) * _ := hb
      _ = (k : ℂ) * _ := by field_simp [hk0] <;> ring
  calc
    _ = iteratedDeriv k (fun t : ℂ => Matrix.trace ((H + t • Y) ^ N) /
        (Fintype.card ι : ℂ)) 0 / (k.factorial : ℂ) := by
      rw [iteratedDeriv_div_const]
      ring
    _ = iteratedDeriv k (fun t : ℂ => circlePowerTrace (H + t • Y) N c R) 0 /
        (k.factorial : ℂ) := by rw [hd]
    _ = (iteratedDeriv k (fun t : ℂ => ∮ z in C(c, R),
        z ^ N * Matrix.trace (resolvent (H + t • Y) z)) 0 / (k.factorial : ℂ)) /
        (2 * Real.pi * Complex.I : ℂ) / (Fintype.card ι : ℂ) := by
      simp only [circlePowerTrace, iteratedDeriv_div_const]
      ring
    _ = _ := by rw [circleIntegral_affine_resolvent_taylor_coefficient H Y hR hsep N k, he]

theorem trace_pow_taylor_coefficient_explicit_circle {H Y : Matrix ι ι ℂ}
    (hH : H.IsHermitian) (hY : Y.IsHermitian) {k N : ℕ} (hk : 0 < k) (hN : 0 < N) :
    let R := ‖H‖ * ‖(1 : Matrix ι ι ℂ)‖ + 1
    iteratedDeriv k (fun t : ℂ => Matrix.trace ((H + t • Y) ^ N)) 0 /
      ((k.factorial : ℂ) * (Fintype.card ι : ℂ)) =
    ((N : ℂ) / k) * (∮ z in C((0 : ℂ), R), z ^ (N - 1) *
      Matrix.trace ((resolvent H z * Y) ^ k)) /
        (2 * Real.pi * Complex.I : ℂ) / (Fintype.card ι : ℂ) := by
  apply trace_pow_taylor_coefficient_whole_circle hH hY hk hN (by positivity)
  intro z hz
  rw [Metric.mem_ball, dist_zero_right]
  exact lt_of_le_of_lt (spectrum.norm_le_norm_mul_of_mem hz) (by linarith)

end
end CGLMPBounds.Hardy
