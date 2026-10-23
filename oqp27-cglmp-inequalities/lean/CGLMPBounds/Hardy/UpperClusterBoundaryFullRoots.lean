module

public import CGLMPBounds.Hardy.UpperClusterBoundary
public import Mathlib.Data.Multiset.Powerset
public import Mathlib.Order.Filter.Finite

@[expose] public section


/-!
# Finitely many limiting values of the actual upper-root sum

The possible limits are literal normalized sums of submultisets of the limiting
characteristic roots. Repeated roots keep their multiplicities. Compactness of
root enumerations and a finite subsequence choice prove membership; no
continuous root labelling, cluster-count oracle, or simple-spectrum assumption
is used. This supports the full complex boundary extension in source C.3.
-/

open Complex Matrix Filter Set
open scoped Topology Matrix.Norms.Operator

namespace CGLMPBounds.Hardy
noncomputable section

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
attribute [-instance] CStarMatrix.instHMulOfFintypeOfMulOfAddCommMonoid

/-- All normalized partial sums, allowing every submultiset of the actual roots.
This finite overestimate includes each possible upper boundary value. -/
def charpolyPartialSumValues (A : Matrix ι ι ℂ) : Finset ℂ := by
  classical
  exact (A.charpoly.roots.powerset.map
    (fun s => s.sum / (Fintype.card ι : ℂ))).toFinset

lemma mem_charpolyPartialSumValues {A : Matrix ι ι ℂ} {s : Multiset ℂ}
    (hs : s ≤ A.charpoly.roots) :
    s.sum / (Fintype.card ι : ℂ) ∈ charpolyPartialSumValues A := by
  classical
  unfold charpolyPartialSumValues
  apply Multiset.mem_toFinset.mpr
  exact Multiset.mem_map.mpr ⟨s, Multiset.mem_powerset.mpr hs, rfl⟩

def upperRootIndices (A : Matrix ι ι ℂ) : Finset ι := by
  classical
  exact Finset.univ.filter (fun i => 0 < (charpolyRootVector A i).im)

lemma upperClusterTrace_eq_finset_sum (A : Matrix ι ι ℂ) :
    upperClusterTrace A =
      (∑ i ∈ upperRootIndices A, charpolyRootVector A i) / (Fintype.card ι : ℂ) := by
  classical
  unfold upperClusterTrace
  rw [← charpolyRootVector_multiset]
  simp only [Multiset.map_map, Function.comp_def]
  change (∑ i, if 0 < (charpolyRootVector A i).im then charpolyRootVector A i else 0) /
      (Fintype.card ι : ℂ) = _
  rw [upperRootIndices, Finset.sum_filter]

/-- Every convergent sequence of selected root sums has a limit among the
finite normalized partial sums of the limiting matrix's actual roots. -/
theorem upperClusterTrace_limit_mem_partialSums
    {A : ℕ → Matrix ι ι ℂ} {B : Matrix ι ι ℂ} {v : ℂ}
    (hA : Tendsto A atTop (𝓝 B))
    (hv : Tendsto (fun n => upperClusterTrace (A n)) atTop (𝓝 v)) :
    v ∈ charpolyPartialSumValues B := by
  classical
  obtain ⟨w, φ, hφ, hw, hfactor⟩ := exists_rootVector_subseq_of_tendsto hA
  have hchoice : ∃ᶠ n in atTop, ∃ s : Finset ι, upperRootIndices (A (φ n)) = s :=
    Filter.Frequently.of_forall (fun n => ⟨_, rfl⟩)
  obtain ⟨s, hs⟩ := Filter.frequently_exists.mp hchoice
  obtain ⟨ψ, hψ, hsψ⟩ := extraction_of_frequently_atTop hs
  have hsum : Continuous (fun u : ι → ℂ =>
      (∑ i ∈ s, u i) / (Fintype.card ι : ℂ)) :=
    (continuous_finsetSum s (fun i _ => continuous_apply i)).div_const _
  have hsumlim := (hsum.tendsto w).comp (hw.comp hψ.tendsto_atTop)
  have hselected : (fun n => upperClusterTrace (A (φ (ψ n)))) =
      (fun n => (∑ i ∈ s, charpolyRootVector (A (φ (ψ n))) i) /
        (Fintype.card ι : ℂ)) := by
    funext n
    rw [upperClusterTrace_eq_finset_sum, hsψ n]
  have hupperlim := hv.comp (hφ.tendsto_atTop.comp hψ.tendsto_atTop)
  change Tendsto (fun n => upperClusterTrace (A (φ (ψ n)))) atTop (𝓝 v) at hupperlim
  rw [hselected] at hupperlim
  have heq : v = (∑ i ∈ s, w i) / (Fintype.card ι : ℂ) :=
    tendsto_nhds_unique hupperlim hsumlim
  rw [heq]
  have hsub : s.val.map w ≤ B.charpoly.roots := by
    rw [hfactor, rootVectorPolynomial_roots]
    exact Multiset.map_le_map (Finset.val_le_iff.mpr (Finset.subset_univ s))
  exact mem_charpolyPartialSumValues hsub

/-- A useful local bound for the normalized selected sum. Keeping the displayed
dimension quotient makes the statement valid also for the empty index type. -/
theorem norm_upperClusterTrace_le (A : Matrix ι ι ℂ) :
    ‖upperClusterTrace A‖ ≤
      ((Fintype.card ι : ℝ) * (‖A‖ * ‖(1 : Matrix ι ι ℂ)‖)) /
        (Fintype.card ι : ℝ) := by
  classical
  unfold upperClusterTrace
  rw [← charpolyRootVector_multiset]
  simp only [Multiset.map_map, Function.comp_def]
  change ‖(∑ i, if 0 < (charpolyRootVector A i).im then charpolyRootVector A i else 0) /
      (Fintype.card ι : ℂ)‖ ≤ _
  rw [norm_div, Complex.norm_natCast]
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
  calc
    ‖∑ i, if 0 < (charpolyRootVector A i).im then charpolyRootVector A i else 0‖
        ≤ ∑ i, ‖if 0 < (charpolyRootVector A i).im then charpolyRootVector A i else 0‖ :=
      norm_sum_le _ _
    _ ≤ ∑ _i : ι, ‖A‖ * ‖(1 : Matrix ι ι ℂ)‖ := by
      apply Finset.sum_le_sum
      intro i _
      split_ifs
      · exact (norm_le_pi_norm (charpolyRootVector A) i).trans (norm_charpolyRootVector_le A)
      · simpa only [norm_zero] using mul_nonneg (norm_nonneg A) (norm_nonneg (1 : Matrix ι ι ℂ))
    _ = (Fintype.card ι : ℝ) * (‖A‖ * ‖(1 : Matrix ι ι ℂ)‖) := by simp

end
end CGLMPBounds.Hardy
