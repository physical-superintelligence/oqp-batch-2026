module

public import CGLMPBounds.Hardy.UpperClusterBoundaryFullRoots
public import CGLMPBounds.Hardy.UpperClusterBoundaryFullTopology
public import CGLMPBounds.Hardy.Support

@[expose] public section


/-!
# Genuine complex boundary extension of the source upper-cluster trace

For the literal source pencil `H⁻¹ * (Y - z I)`, every possible limiting
upper-root sum is a normalized partial sum of the limiting characteristic
roots. There are only finitely many such sums. Interior holomorphy gives
continuity on connected upper half-disks, which makes the limit unique.
The resulting topological extension is continuous on the closed upper
half-plane and its boundary imaginary part is `pi * traceDensity`.

The extension is deliberately different from naively evaluating the strict
upper-root selector on the real axis: real limiting roots may contribute to
the limiting real part. All sums use the source normalization `1 / card ι`.

Canonical source: Lemma C.3, printed p.8, through the continuous-boundary and
imaginary-boundary assertions. The exterior negative-cluster function `q`,
Schwarz reflection, the C.8 slit representation, and C.7 moments are not
asserted here.
-/

open Complex Matrix Filter Set Metric
open scoped Topology Matrix.Norms.Operator

namespace CGLMPBounds.Hardy
noncomputable section

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
attribute [-instance] CStarMatrix.instHMulOfFintypeOfMulOfAddCommMonoid

/-- This finiteness assertion needs no Hermiticity: it follows from the literal
root multiset, its multiplicities, and continuity of the matrix pencil. -/
theorem pencil_upperClusterTrace_cluster_mem_partialSums
    (H Y : Matrix ι ι ℂ) (x : ℝ) {v : ℂ}
    (hv : MapClusterPt v (𝓝[{z : ℂ | 0 < z.im}] (x : ℂ))
      (fun z => upperClusterTrace (traceDensityPencil H Y z))) :
    v ∈ charpolyPartialSumValues (traceDensityPencil H Y (x : ℂ)) := by
  obtain ⟨z, hgz, hz⟩ := hv.exists_seq_tendsto
  apply upperClusterTrace_limit_mem_partialSums
      (A := fun n => traceDensityPencil H Y (z n))
  · exact (analyticAt_traceDensityPencil H Y (x : ℂ)).continuousAt.tendsto.comp
      (hz.mono_right nhdsWithin_le_nhds)
  · exact hgz

/-- Eigenvalue bounds give a genuine compact range near each finite parameter.
No boundary extension or analyticity of the selected sum is assumed here. -/
theorem pencil_upperClusterTrace_locally_compact (H Y : Matrix ι ι ℂ) (x : ℝ) :
    ∃ K : Set ℂ, IsCompact K ∧
      ∀ᶠ z in 𝓝[{z : ℂ | 0 < z.im}] (x : ℂ),
        upperClusterTrace (traceDensityPencil H Y z) ∈ K := by
  let B := traceDensityPencil H Y (x : ℂ)
  let R : ℝ := ((Fintype.card ι : ℝ) *
    ((‖B‖ + 1) * ‖(1 : Matrix ι ι ℂ)‖)) / (Fintype.card ι : ℝ)
  refine ⟨closedBall 0 R, isCompact_closedBall _ _, ?_⟩
  have hnorm : ∀ᶠ z in 𝓝 (x : ℂ), ‖traceDensityPencil H Y z‖ < ‖B‖ + 1 :=
    (analyticAt_traceDensityPencil H Y (x : ℂ)).continuousAt.norm.eventually_lt
      continuousAt_const (lt_add_one ‖B‖)
  filter_upwards [hnorm.filter_mono nhdsWithin_le_nhds] with z hz
  rw [Metric.mem_closedBall, dist_zero_right]
  apply (norm_upperClusterTrace_le _).trans
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
  exact mul_le_mul_of_nonneg_left
    (mul_le_mul_of_nonneg_right hz.le (norm_nonneg _)) (Nat.cast_nonneg _)

/-- The full complex limit exists at every real parameter under exactly the
source's Hermitian/invertible-pencil hypotheses. No limit oracle is assumed. -/
theorem exists_pencil_upperClusterTrace_boundary_limit
    {H Y : Matrix ι ι ℂ} (hH : H.IsHermitian) (hY : Y.IsHermitian)
    (hdet : IsUnit H.det) (x : ℝ) :
    ∃ v, Tendsto (fun z => upperClusterTrace (traceDensityPencil H Y z))
      (𝓝[{z : ℂ | 0 < z.im}] (x : ℂ)) (𝓝 v) := by
  obtain ⟨v, _, hv⟩ := exists_upper_boundary_limit_of_finite_cluster x
    (analyticOnNhd_pencil_upperClusterTrace hH hY hdet).continuousOn
    (pencil_upperClusterTrace_locally_compact H Y x)
    (charpolyPartialSumValues (traceDensityPencil H Y (x : ℂ)) : Set ℂ)
    (Finset.finite_toSet _)
    (fun v hv => pencil_upperClusterTrace_cluster_mem_partialSums H Y x hv)
  exact ⟨v, hv⟩

/-- The actual continuous extension of the source's normalized `g`. Its real
boundary values are limits and are not assigned by the strict root selector. -/
def pencilUpperBoundaryExtension (H Y : Matrix ι ι ℂ) :
    {z : ℂ // 0 ≤ z.im} → ℂ :=
  upperHalfPlaneExtension (fun z => upperClusterTrace (traceDensityPencil H Y z))

theorem continuous_pencilUpperBoundaryExtension
    {H Y : Matrix ι ι ℂ} (hH : H.IsHermitian) (hY : Y.IsHermitian)
    (hdet : IsUnit H.det) : Continuous (pencilUpperBoundaryExtension H Y) := by
  exact continuous_upperHalfPlaneExtension
    (analyticOnNhd_pencil_upperClusterTrace hH hY hdet).continuousOn
    (exists_pencil_upperClusterTrace_boundary_limit hH hY hdet)

theorem pencilUpperBoundaryExtension_eq_interior
    {H Y : Matrix ι ι ℂ} (hH : H.IsHermitian) (hY : Y.IsHermitian)
    (hdet : IsUnit H.det) (z : {z : ℂ // 0 < z.im}) :
    pencilUpperBoundaryExtension H Y (upperHalfPlaneInclusion z) =
      upperClusterTrace (traceDensityPencil H Y z) := by
  exact upperHalfPlaneExtension_eq_interior
    (analyticOnNhd_pencil_upperClusterTrace hH hY hdet).continuousOn z

/-- Exact upper-half-plane convergence to the newly constructed boundary value. -/
theorem tendsto_pencilUpperBoundaryExtension_real
    {H Y : Matrix ι ι ℂ} (hH : H.IsHermitian) (hY : Y.IsHermitian)
    (hdet : IsUnit H.det) (x : ℝ) :
    Tendsto (fun z => upperClusterTrace (traceDensityPencil H Y z))
      (𝓝[{z : ℂ | 0 < z.im}] (x : ℂ))
      (𝓝 (pencilUpperBoundaryExtension H Y ⟨(x : ℂ), by simp⟩)) := by
  obtain ⟨v, hv⟩ := exists_pencil_upperClusterTrace_boundary_limit hH hY hdet x
  have heq : pencilUpperBoundaryExtension H Y ⟨(x : ℂ), by simp⟩ = v :=
    upperHalfPlaneExtension_eq_of_tendsto hv
  rwa [heq]

/-- The continuous extension has the source's exact boundary density. -/
theorem pencilUpperBoundaryExtension_im_real
    {H Y : Matrix ι ι ℂ} (hH : H.IsHermitian) (hY : Y.IsHermitian)
    (hdet : IsUnit H.det) (x : ℝ) :
    (pencilUpperBoundaryExtension H Y ⟨(x : ℂ), by simp⟩).im =
      Real.pi * traceDensity H Y x := by
  haveI := upperHalfPlane_boundary_neBot x
  exact tendsto_nhds_unique
    (Complex.continuous_im.tendsto _ |>.comp
      (tendsto_pencilUpperBoundaryExtension_real hH hY hdet x))
    (tendsto_pencil_upperClusterTrace_im_boundary hH hY x)

/-- The exact jump between the upper bank and its conjugate lower bank.
This is boundary data only; it does not assume a slit-integral formula. -/
theorem pencilUpperBoundaryExtension_sub_conj
    {H Y : Matrix ι ι ℂ} (hH : H.IsHermitian) (hY : Y.IsHermitian)
    (hdet : IsUnit H.det) (x : ℝ) :
    pencilUpperBoundaryExtension H Y ⟨(x : ℂ), by simp⟩ -
        star (pencilUpperBoundaryExtension H Y ⟨(x : ℂ), by simp⟩) =
      (2 * Real.pi * Complex.I : ℂ) * (traceDensity H Y x : ℂ) := by
  apply Complex.ext
  · simp [Complex.star_def, Complex.mul_re, Complex.mul_im]
  · simp [Complex.star_def, Complex.mul_re, Complex.mul_im,
      pencilUpperBoundaryExtension_im_real hH hY hdet x] <;> ring

/-- Off the exact spectral interval, the two conjugate bank values agree.
The full real value may be nonzero; only its imaginary part vanishes. -/
theorem pencilUpperBoundaryExtension_eq_conj_outside_spectralInterval
    {H Y : Matrix ι ι ℂ} (hH : H.IsHermitian) (hY : Y.IsHermitian)
    (hdet : IsUnit H.det) {x : ℝ}
    (hx : x ∉ Set.Icc (sInf (spectrum ℝ Y)) (sSup (spectrum ℝ Y))) :
    pencilUpperBoundaryExtension H Y ⟨(x : ℂ), by simp⟩ =
      star (pencilUpperBoundaryExtension H Y ⟨(x : ℂ), by simp⟩) := by
  apply sub_eq_zero.mp
  rw [pencilUpperBoundaryExtension_sub_conj hH hY hdet x,
    traceDensity_eq_zero_outside_spectralInterval hH hY hdet hx]
  simp

end
end CGLMPBounds.Hardy
