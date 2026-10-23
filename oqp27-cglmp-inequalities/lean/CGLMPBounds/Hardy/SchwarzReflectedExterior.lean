module

public import CGLMPBounds.Hardy.SchwarzReflection
public import CGLMPBounds.Hardy.SchwarzExteriorIdentity
public import CGLMPBounds.Hardy.SchwarzExteriorTaylor

@[expose] public section


/-!
# Exterior formula on both sides of the slit

The actual local Taylor series has real coefficients, so the actual contour q
commutes with complex conjugation near zero. The upper exterior g/q identity
then passes to the real boundary by continuity and to the lower half-plane by
the literal reflection. No slit integral representation is assumed.

Source: supplement printed p.8, exterior expansion and Schwarz reflection
preceding C.8.
-/

open Complex Matrix Filter Set Metric
open scoped Topology Matrix.Norms.Operator

namespace CGLMPBounds.Hardy
noncomputable section

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
attribute [-instance] CStarMatrix.instHMulOfFintypeOfMulOfAddCommMonoid

lemma exteriorTaylorCoefficient_star {H Y : Matrix ι ι ℂ}
    (hH : H.IsHermitian) (hY : Y.IsHermitian) (hdet : IsUnit H.det) (m : ℕ) :
    star (exteriorTaylorCoefficient H Y m) = exteriorTaylorCoefficient H Y m := by
  apply Complex.ext <;>
    simp [Complex.star_def, exteriorTaylorCoefficient_im_eq_zero hH hY hdet m]

/-- Reality of the actual Taylor coefficients yields local conjugation
symmetry of the actual q, throughout a complex disk. -/
theorem exists_exteriorClusterQ_conj {H Y : Matrix ι ι ℂ}
    (hH : H.IsHermitian) (hY : Y.IsHermitian) (hdet : IsUnit H.det) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ w : ℂ, ‖w‖ < δ →
      exteriorClusterQ H Y (star w) = star (exteriorClusterQ H Y w) := by
  obtain ⟨δ, hδ, hs⟩ := exists_exteriorTaylor_hasSum Y hH hdet
  refine ⟨δ, hδ, ?_⟩
  intro w hw
  have hsw := (hs w hw).star
  have hsc : HasSum
      (fun m : ℕ => exteriorTaylorCoefficient H Y m * (star w) ^ m)
      (star (exteriorClusterQ H Y w)) := by
    simpa only [star_mul', star_pow, exteriorTaylorCoefficient_star hH hY hdet] using hsw
  exact (hs (star w) (by simpa using hw)).unique hsc

lemma norm_inv_lt_of_inv_lt_norm {z : ℂ} {δ : ℝ} (hδ : 0 < δ)
    (hz : δ⁻¹ < ‖z‖) : ‖z⁻¹‖ < δ := by
  have hzp : 0 < ‖z‖ := (inv_pos.mpr hδ).trans hz
  have hm := mul_lt_mul_of_pos_left hz hδ
  rw [mul_inv_cancel₀ hδ.ne'] at hm
  have hd : 1 / ‖z‖ < δ := (div_lt_iff₀ hzp).mpr (by nlinarith)
  simpa only [norm_inv, one_div] using hd

/-- The literal reflected source function equals `-z q(1/z)` on a full
exterior neighborhood, including both real rays. The boundary case is proved
using the actual upper limit and local analyticity of q. -/
theorem exists_reflectedPencilTrace_eq_exterior {H Y : Matrix ι ι ℂ}
    (hH : H.IsHermitian) (hY : Y.IsHermitian) (hdet : IsUnit H.det) :
    ∃ R : ℝ, 0 < R ∧ ∀ z : ℂ, R < ‖z‖ →
      reflectedPencilTrace H Y z = (-z) * exteriorClusterQ H Y z⁻¹ := by
  obtain ⟨R₀, hR₀, hupper⟩ := exists_upperClusterTrace_eq_exterior hH hY hdet
  obtain ⟨r, hr, hA⟩ := (analyticAt_exteriorClusterQ_zero Y hH hdet).exists_ball_analyticOnNhd
  obtain ⟨s, hs, hconj⟩ := exists_exteriorClusterQ_conj hH hY hdet
  let δ := min r s
  have hδ : 0 < δ := lt_min hr hs
  let R := max R₀ δ⁻¹
  have hR : 0 < R := hR₀.trans_le (le_max_left _ _)
  have hsmall : ∀ z : ℂ, R < ‖z‖ → ‖z⁻¹‖ < δ := by
    intro z hz
    exact norm_inv_lt_of_inv_lt_norm hδ ((le_max_right _ _).trans_lt hz)
  have hreal : ∀ x : ℝ, R < ‖(x : ℂ)‖ →
      pencilUpperBoundaryExtension H Y ⟨(x : ℂ), by simp⟩ =
        (-(x : ℂ)) * exteriorClusterQ H Y (x : ℂ)⁻¹ := by
    intro x hx
    have hxn : (x : ℂ) ≠ 0 := norm_pos_iff.mp (hR.trans hx)
    have hxsmall : ‖(x : ℂ)⁻¹‖ < r := (hsmall _ hx).trans_le (min_le_left _ _)
    have hqc := (hA (x : ℂ)⁻¹ (by simpa only [mem_ball_iff_norm, sub_zero] using hxsmall)).continuousAt
    have hc : ContinuousAt (fun z : ℂ => (-z) * exteriorClusterQ H Y z⁻¹) (x : ℂ) :=
      continuousAt_id.neg.mul (hqc.comp (continuousAt_inv₀ hxn))
    have heq : (fun z => upperClusterTrace (traceDensityPencil H Y z))
        =ᶠ[𝓝[{z : ℂ | 0 < z.im}] (x : ℂ)]
        (fun z => (-z) * exteriorClusterQ H Y z⁻¹) := by
      have hn : ∀ᶠ z in 𝓝 (x : ℂ), R₀ < ‖z‖ :=
        continuousAt_const.eventually_lt continuousAt_id.norm
          ((le_max_left _ _).trans_lt hx)
      filter_upwards [hn.filter_mono nhdsWithin_le_nhds, self_mem_nhdsWithin] with z hz hzi
      exact hupper z hz hzi
    haveI := upperHalfPlane_boundary_neBot x
    apply tendsto_nhds_unique (tendsto_pencilUpperBoundaryExtension_real hH hY hdet x)
    exact Tendsto.congr' heq.symm (hc.tendsto.mono_left nhdsWithin_le_nhds)
  refine ⟨R, hR, ?_⟩
  intro z hz
  rcases lt_trichotomy z.im 0 with hzi | hzi | hzi
  · rw [reflectedPencilTrace_eq_lower hH hY hdet hzi]
    have hzs : 0 < (star z).im := by simpa [Complex.star_def] using neg_pos.mpr hzi
    rw [hupper (star z) (by simpa using (le_max_left R₀ δ⁻¹).trans_lt hz) hzs]
    have hqs := hconj z⁻¹ ((hsmall z hz).trans_le (min_le_right _ _))
    rw [← star_inv₀, hqs]
    simp only [star_mul', star_neg, star_star]
  · have hzeq : z = (z.re : ℂ) := by apply Complex.ext <;> simp [hzi]
    rw [hzeq, reflectedPencilTrace_real]
    exact hreal z.re (by simpa only [← hzeq] using hz)
  · rw [reflectedPencilTrace_eq_upper hH hY hdet hzi]
    exact hupper z ((le_max_left _ _).trans_lt hz) hzi

end
end CGLMPBounds.Hardy
