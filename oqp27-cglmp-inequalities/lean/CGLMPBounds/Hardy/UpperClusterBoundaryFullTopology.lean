module

public import Mathlib.Analysis.Complex.Convex
public import Mathlib.Analysis.Normed.Module.Convex
public import Mathlib.Topology.Compactness.Compact
public import Mathlib.Topology.MetricSpace.ProperSpace
public import Mathlib.Order.Interval.Set.Infinite
public import Mathlib.Topology.DenseEmbedding

@[expose] public section


/-!
# A finite-cluster boundary-limit criterion

A continuous function on the upper half-plane with locally compact range and
only finitely many possible boundary cluster values has a genuine complex
boundary limit. The proof uses connected upper half-disks and an intermediate
radius avoiding the finite cluster set. No analytic extension or integral
representation is assumed.

This is infrastructure for the actual matrix-pencil root sum in C.3.
-/

open Complex Metric Set Filter
open scoped Topology

namespace CGLMPBounds.Hardy
noncomputable section

lemma upperHalfPlane_boundary_neBot (x : ℝ) :
    NeBot (𝓝[{z : ℂ | 0 < z.im}] (x : ℂ)) := by
  apply mem_closure_iff_nhdsWithin_neBot.mp
  simp only [Complex.closure_setOfPred_lt_im, Set.mem_setOf_eq, Complex.ofReal_im]
  exact le_rfl

/-- Connectedness rules out switching between finitely many candidate limits.
The compact range hypothesis is used only to obtain one cluster point. -/
theorem exists_upper_boundary_limit_of_finite_cluster
    {f : ℂ → ℂ} (x : ℝ)
    (hf : ContinuousOn f {z : ℂ | 0 < z.im})
    (hcompact : ∃ K : Set ℂ, IsCompact K ∧
      ∀ᶠ z in 𝓝[{z : ℂ | 0 < z.im}] (x : ℂ), f z ∈ K)
    (S : Set ℂ) (hS : S.Finite)
    (hcluster : ∀ v, MapClusterPt v (𝓝[{z : ℂ | 0 < z.im}] (x : ℂ)) f → v ∈ S) :
    ∃ v ∈ S, Tendsto f (𝓝[{z : ℂ | 0 < z.im}] (x : ℂ)) (𝓝 v) := by
  let l := 𝓝[{z : ℂ | 0 < z.im}] (x : ℂ)
  haveI : NeBot l := upperHalfPlane_boundary_neBot x
  obtain ⟨K, hK, hmem⟩ := hcompact
  obtain ⟨v, _, hv⟩ := hK.exists_mapClusterPt
    (show Filter.map f l ≤ 𝓟 K from Filter.le_principal_iff.mpr hmem)
  refine ⟨v, hcluster v hv, Metric.tendsto_nhds.mpr ?_⟩
  intro ε hε
  obtain ⟨ρ, hρ, hρS⟩ := (Set.Ioo_infinite hε).exists_notMem_finite
    (hS.image (fun w => dist w v))
  have havoid : ∀ᶠ z in l, dist (f z) v ≠ ρ := by
    apply Filter.not_frequently.mp
    intro hbad
    have hbad' : ∃ᶠ z in l, f z ∈ sphere v ρ := by
      simpa only [Metric.mem_sphere] using hbad
    obtain ⟨w, hw, hwcluster⟩ :=
      (isCompact_sphere v ρ).exists_mapClusterPt_of_frequently hbad'
    exact hρS ⟨w, hcluster w hwcluster, Metric.mem_sphere.mp hw⟩
  obtain ⟨δ, hδ, hδavoid⟩ := Metric.mem_nhdsWithin_iff.mp havoid
  let D : Set ℂ := ball (x : ℂ) δ ∩ {z : ℂ | 0 < z.im}
  have hDmem : D ∈ l := Metric.mem_nhdsWithin_iff.mpr ⟨δ, hδ, subset_rfl⟩
  have hDconn : IsPreconnected D :=
    ((convex_ball (x : ℂ) δ).inter (convex_halfSpace_im_gt 0)).isPreconnected
  have hdist : ContinuousOn (fun z => dist (f z) v) D := by
    intro z hz
    exact ((hf.mono inter_subset_right) z hz).dist tendsto_const_nhds
  have hnear : ∃ᶠ z in l, dist (f z) v < ρ :=
    hv.frequently (Metric.ball_mem_nhds v hρ.1)
  obtain ⟨z, hznear, hzD⟩ := (hnear.and_eventually hDmem).exists
  have hside : ∀ z ∈ D, dist (f z) v < ρ := by
    intro w hw
    exact hDconn.gt_of_ne hdist (fun a ha => hδavoid ha)
      ⟨z, hzD, hznear⟩ hw
  filter_upwards [hDmem] with w hw
  exact (hside w hw).trans hρ.2

/-- The literal inclusion of the open upper half-plane into its closure. -/
def upperHalfPlaneInclusion : {z : ℂ // 0 < z.im} → {z : ℂ // 0 ≤ z.im} :=
  Set.inclusion (fun (z : ℂ) (hz : 0 < z.im) => le_of_lt hz)

lemma upperHalfPlaneInclusion_isDenseInducing : IsDenseInducing upperHalfPlaneInclusion := by
  have hclosure : {z : ℂ | 0 ≤ z.im} ⊆ closure {z : ℂ | 0 < z.im} := by
    rw [Complex.closure_setOfPred_lt_im]
  refine ⟨(Topology.IsEmbedding.inclusion (fun (z : ℂ) (hz : 0 < z.im) => le_of_lt hz)).isInducing,
    ?_⟩
  exact (denseRange_inclusion_iff (s := {z : ℂ | 0 < z.im})
    (t := {z : ℂ | 0 ≤ z.im})
    (by intro z hz; exact (show 0 < z.im from hz).le)).mpr hclosure

lemma map_val_comap_upperHalfPlaneInclusion (z : {z : ℂ // 0 ≤ z.im}) :
    Filter.map (fun w : {w : ℂ // 0 < w.im} => (w : ℂ))
        (Filter.comap upperHalfPlaneInclusion (𝓝 z)) =
      𝓝[{w : ℂ | 0 < w.im}] (z : ℂ) := by
  rw [nhds_subtype_eq_comap, Filter.comap_comap]
  change Filter.map (fun w : {w : ℂ // 0 < w.im} => (w : ℂ))
      (Filter.comap (fun w : {w : ℂ // 0 < w.im} => (w : ℂ)) (𝓝 (z : ℂ))) = _
  exact Filter.map_comap_setCoe_val (𝓝 (z : ℂ)) {w : ℂ | 0 < w.im}

/-- This is the actual topological limit extension, not the selected-root sum
evaluated naively on real matrices. Continuity is proved below from limits. -/
def upperHalfPlaneExtension (f : ℂ → ℂ) : {z : ℂ // 0 ≤ z.im} → ℂ :=
  upperHalfPlaneInclusion_isDenseInducing.extend (fun z => f z)

lemma upperHalfPlaneExtension_eq_of_tendsto {f : ℂ → ℂ}
    {z : {z : ℂ // 0 ≤ z.im}} {v : ℂ}
    (hv : Tendsto f (𝓝[{w : ℂ | 0 < w.im}] (z : ℂ)) (𝓝 v)) :
    upperHalfPlaneExtension f z = v := by
  apply upperHalfPlaneInclusion_isDenseInducing.extend_eq_of_tendsto
  apply hv.comp
  change Filter.map (fun w : {w : ℂ // 0 < w.im} => (w : ℂ))
      (Filter.comap upperHalfPlaneInclusion (𝓝 z)) ≤ _
  rw [map_val_comap_upperHalfPlaneInclusion]

theorem upperHalfPlaneExtension_eq_interior {f : ℂ → ℂ}
    (hf : ContinuousOn f {z : ℂ | 0 < z.im})
    (z : {z : ℂ // 0 < z.im}) :
    upperHalfPlaneExtension f (upperHalfPlaneInclusion z) = f z := by
  exact upperHalfPlaneExtension_eq_of_tendsto (hf z z.property)

/-- Existence of genuine one-sided limits at every real point supplies a
continuous extension on the whole closed upper half-plane. -/
theorem continuous_upperHalfPlaneExtension {f : ℂ → ℂ}
    (hf : ContinuousOn f {z : ℂ | 0 < z.im})
    (hboundary : ∀ x : ℝ, ∃ v,
      Tendsto f (𝓝[{z : ℂ | 0 < z.im}] (x : ℂ)) (𝓝 v)) :
    Continuous (upperHalfPlaneExtension f) := by
  apply upperHalfPlaneInclusion_isDenseInducing.continuous_extend
  intro z
  have hlim : ∃ v, Tendsto f (𝓝[{w : ℂ | 0 < w.im}] (z : ℂ)) (𝓝 v) := by
    by_cases hz : 0 < (z : ℂ).im
    · exact ⟨f z, hf z hz⟩
    · have him : (z : ℂ).im = 0 := le_antisymm (le_of_not_gt hz) z.property
      have heq : (z : ℂ) = ((z : ℂ).re : ℂ) := by
        apply Complex.ext <;> simp [him]
      rw [heq]
      exact hboundary (z : ℂ).re
  obtain ⟨v, hv⟩ := hlim
  refine ⟨v, hv.comp ?_⟩
  change Filter.map (fun w : {w : ℂ // 0 < w.im} => (w : ℂ))
      (Filter.comap upperHalfPlaneInclusion (𝓝 z)) ≤ _
  rw [map_val_comap_upperHalfPlaneInclusion]

end
end CGLMPBounds.Hardy
