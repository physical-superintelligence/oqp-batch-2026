module

public import CGLMPBounds.Hardy.SchwarzPositiveCoefficients
public import CGLMPBounds.Hardy.SchwarzExteriorTaylor

@[expose] public section


/-! The actual negative exterior coefficient: first line of the C.7 contour
calculation. Its 1/n factor comes from a genuine closed-circle integration
by parts, and its (-1)^n from the affine direction -H^{-1}Y. This avoids
postulating a log-determinant coefficient identity. Contour inversion and
comparison with the positive H contour remain separate obligations. -/

open Complex Matrix Filter Set Metric
open scoped Topology Matrix.Norms.Operator

namespace CGLMPBounds.Hardy
noncomputable section
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
attribute [-instance] CStarMatrix.instHMulOfFintypeOfMulOfAddCommMonoid

lemma exteriorPencil_eq_affine (H Y : Matrix ι ι ℂ) (w : ℂ) :
    exteriorPencil H Y w = H⁻¹ + w • (-(H⁻¹ * Y)) := by
  rw [exteriorPencil, Matrix.mul_sub, Matrix.mul_one, Matrix.mul_smul]
  simp only [sub_eq_add_neg, smul_neg]

lemma circleClusterTrace_eq_circlePowerTrace_one (A : Matrix ι ι ℂ)
    {c : ℂ} {R : ℝ} (hR : 0 ≤ R)
    (hsep : ∀ a ∈ A.charpoly.roots, a ∉ sphere c R) :
    circleClusterTrace A c R = circlePowerTrace A 1 c R := by
  rw [circleClusterTrace_eq_root_sum A hR hsep,
    circlePowerTrace_eq_root_sum A 1 hR hsep]
  simp only [pow_one]

/-- Local identity with the genuine affine trace-resolvent power functional,
not an equality assumed in the exterior function's definition. -/
lemma exteriorClusterQ_eventuallyEq_affine_circlePowerTrace {H : Matrix ι ι ℂ}
    (Y : Matrix ι ι ℂ) (hH : H.IsHermitian) (hdet : IsUnit H.det) :
    let R := negativeClusterRadius H⁻¹.charpoly.roots
    exteriorClusterQ H Y =ᶠ[𝓝 (0 : ℂ)]
      (fun w => circlePowerTrace (H⁻¹ + w • (-(H⁻¹ * Y))) 1 (-(R : ℂ)) R) := by
  let R := negativeClusterRadius H⁻¹.charpoly.roots
  filter_upwards [eventually_exterior_fixed_circle_resolvent Y hH hdet] with w hw
  unfold exteriorClusterQ
  rw [circleClusterTrace_eq_circlePowerTrace_one _ (negativeClusterRadius_pos _).le,
    exteriorPencil_eq_affine]
  intro a ha hs
  exact hw a hs
    (Matrix.mem_spectrum_of_isRoot_charpoly (Polynomial.isRoot_of_mem_roots ha))

/-- Actual derivative/factorial coefficient of q before integration by parts. -/
theorem exteriorTaylorCoefficient_eq_affine_circleIntegral {H : Matrix ι ι ℂ}
    (Y : Matrix ι ι ℂ) (hH : H.IsHermitian) (hdet : IsUnit H.det) (n : ℕ) :
    let R := negativeClusterRadius H⁻¹.charpoly.roots
    exteriorTaylorCoefficient H Y n =
      (∮ ζ in C((-(R : ℂ)), R), ζ *
        Matrix.trace ((resolvent H⁻¹ ζ * (-(H⁻¹ * Y))) ^ n * resolvent H⁻¹ ζ)) /
          (2 * Real.pi * Complex.I : ℂ) / (Fintype.card ι : ℂ) := by
  let R := negativeClusterRadius H⁻¹.charpoly.roots
  have hsep : ∀ ζ ∈ sphere (-(R : ℂ)) R, ζ ∉ spectrum ℂ H⁻¹ := by
    intro ζ hζ
    exact circle_not_mem_spectrum_of_root_separation H⁻¹
      (fun a ha => (negativeClusterRadius_separates _
        (fun b hb => hermitian_inverse_root_re_ne_zero hH hdet hb) ha).1) hζ
  have hd := (exteriorClusterQ_eventuallyEq_affine_circlePowerTrace Y hH hdet).iteratedDeriv_eq n
  unfold exteriorTaylorCoefficient
  rw [hd]
  simp only [circlePowerTrace, iteratedDeriv_div_const]
  calc
    _ = (iteratedDeriv n (fun t : ℂ => ∮ ζ in C((-(R : ℂ)), R),
        ζ ^ 1 * Matrix.trace (resolvent (H⁻¹ + t • (-(H⁻¹ * Y))) ζ)) 0 /
          (n.factorial : ℂ)) / (2 * Real.pi * Complex.I : ℂ) / (Fintype.card ι : ℂ) := by ring
    _ = _ := by
      rw [circleIntegral_affine_resolvent_taylor_coefficient H⁻¹ (-(H⁻¹ * Y))
        (negativeClusterRadius_pos _).le hsep 1 n]
      simp only [pow_one, R]

/-- The linear-weight closed-contour integration-by-parts identity gives
1/n independently of any parameter series or cluster interpretation. -/
lemma circleIntegral_resolvent_linear_power_eq_ratio
    (A B : Matrix ι ι ℂ) {c : ℂ} {R : ℝ} (hR : 0 ≤ R)
    (hsep : ∀ z ∈ sphere c R, z ∉ spectrum ℂ A) {n : ℕ} (hn : 0 < n) :
    (∮ z in C(c, R), z * Matrix.trace ((resolvent A z * B) ^ n * resolvent A z)) =
      (1 / (n : ℂ)) * (∮ z in C(c, R), Matrix.trace ((resolvent A z * B) ^ n)) := by
  let tr : Matrix ι ι ℂ →L[ℂ] ℂ := (Matrix.traceLinearMap ι ℂ ℂ).toContinuousLinearMap
  have hcR := continuousOn_matrix_resolvent A hsep
  have hcT : ContinuousOn (fun z => Matrix.trace ((resolvent A z * B) ^ n)) (sphere c R) :=
    tr.continuous.comp_continuousOn ((hcR.mul continuousOn_const).pow n)
  have hcU : ContinuousOn (fun z => z * Matrix.trace
      ((resolvent A z * B) ^ n * resolvent A z)) (sphere c R) :=
    continuousOn_id.mul (tr.continuous.comp_continuousOn
      (((hcR.mul continuousOn_const).pow n).mul hcR))
  have hiT := hcT.circleIntegrable hR
  have hiU := hcU.circleIntegrable hR
  have hiN : CircleIntegrable (fun z => (n : ℂ) *
      (z * Matrix.trace ((resolvent A z * B) ^ n * resolvent A z))) c R := by
    simpa only [Pi.smul_apply, smul_eq_mul] using! hiU.const_smul (a := (n : ℂ))
  have hzero : (∮ z in C(c, R), Matrix.trace ((resolvent A z * B) ^ n) -
      (n : ℂ) * (z * Matrix.trace ((resolvent A z * B) ^ n * resolvent A z))) = 0 := by
    apply circleIntegral.integral_eq_zero_of_hasDerivWithinAt hR
      (f := fun z => z * Matrix.trace ((resolvent A z * B) ^ n))
    intro z hz
    have ht := hasDerivAt_trace_resolvent_mul_pow A B (hsep z hz) hn
    have hd := (hasDerivAt_id z).mul ht
    have hd' : HasDerivAt (fun z => z * Matrix.trace ((resolvent A z * B) ^ n))
        (Matrix.trace ((resolvent A z * B) ^ n) - (n : ℂ) *
          (z * Matrix.trace ((resolvent A z * B) ^ n * resolvent A z))) z := by
      convert hd using 1 <;> first | rfl | (simp only [id_eq]; ring)
    exact hd'.hasDerivWithinAt
  rw [circleIntegral.integral_sub hiT hiN, circleIntegral.integral_const_mul] at hzero
  have hnn : (n : ℂ) ≠ 0 := by exact_mod_cast hn.ne'
  apply (mul_left_cancel₀ hnn)
  calc
    (n : ℂ) * _ = ∮ z in C(c, R), Matrix.trace ((resolvent A z * B) ^ n) := by
      linear_combination -hzero
    _ = _ := by field_simp [hnn]

/-- Inverting the literal matrix factor H*(ζI-H^{-1}) gives the matrix
appearing in the source's first contour line. This is an algebraic identity;
no change of contour is performed here. -/
lemma inverse_inverse_pencil_resolvent (H : Matrix ι ι ℂ)
    (hdet : IsUnit H.det) (ζ : ℂ) :
    resolvent H⁻¹ ζ * H⁻¹ = Ring.inverse (ζ • H - 1) := by
  have hH : IsUnit H := (Matrix.isUnit_iff_isUnit_det H).mpr hdet
  have hfac : H * (algebraMap ℂ (Matrix ι ι ℂ) ζ - H⁻¹) = ζ • H - 1 := by
    rw [mul_sub, Algebra.algebraMap_eq_smul_one, mul_smul_comm, mul_one,
      Matrix.mul_nonsing_inv H hdet]
  rw [← hfac, Ring.inverse_mul (Or.inl hH), ← Matrix.nonsing_inv_eq_ringInverse H]
  rfl

/-- The actual first contour identity in the source proof of C.7. The
negative H-inverse contour is fixed by the same literal definition as q. -/
theorem exteriorTaylorCoefficient_eq_negative_resolvent_power
    {H : Matrix ι ι ℂ} (Y : Matrix ι ι ℂ) (hH : H.IsHermitian)
    (hdet : IsUnit H.det) {n : ℕ} (hn : 0 < n) :
    let R := negativeClusterRadius H⁻¹.charpoly.roots
    exteriorTaylorCoefficient H Y n =
      ((-1 : ℂ) ^ n / (n : ℂ)) *
        (∮ ζ in C((-(R : ℂ)), R), Matrix.trace ((Ring.inverse (ζ • H - 1) * Y) ^ n)) /
          (2 * Real.pi * Complex.I : ℂ) / (Fintype.card ι : ℂ) := by
  let R := negativeClusterRadius H⁻¹.charpoly.roots
  have hsep : ∀ ζ ∈ sphere (-(R : ℂ)) R, ζ ∉ spectrum ℂ H⁻¹ := by
    intro ζ hζ
    exact circle_not_mem_spectrum_of_root_separation H⁻¹
      (fun a ha => (negativeClusterRadius_separates _
        (fun b hb => hermitian_inverse_root_re_ne_zero hH hdet hb) ha).1) hζ
  rw [exteriorTaylorCoefficient_eq_affine_circleIntegral Y hH hdet n,
    circleIntegral_resolvent_linear_power_eq_ratio H⁻¹ (-(H⁻¹ * Y))
      (negativeClusterRadius_pos _).le hsep hn]
  have hint : (fun ζ : ℂ => Matrix.trace ((resolvent H⁻¹ ζ * (-(H⁻¹ * Y))) ^ n)) =
      fun ζ : ℂ => (-1 : ℂ) ^ n * Matrix.trace ((Ring.inverse (ζ • H - 1) * Y) ^ n) := by
    funext ζ
    rw [mul_neg, ← mul_assoc, inverse_inverse_pencil_resolvent H hdet ζ,
      show -(Ring.inverse (ζ • H - 1) * Y) =
        (-1 : ℂ) • (Ring.inverse (ζ • H - 1) * Y) by simp,
      smul_pow, Matrix.trace_smul, smul_eq_mul]
  rw [hint, circleIntegral.integral_const_mul]
  ring

end
end CGLMPBounds.Hardy
