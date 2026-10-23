module

public import CGLMPBounds.Partition.CircularBasics
public import CGLMPBounds.Partition.ConsecutiveBasics
public import Mathlib.Data.Finset.Sort

@[expose] public section


/-! A genuine consecutive partition for the literal circular count.
Sorting the distinct boundary points together with 0 and 1 permits
repeated original boundaries and avoids any generic-position premise.
Only geometry is proved here. -/

namespace CGLMPBounds.Partition
open Set
open scoped Matrix
noncomputable section

/-- The actual circular count is constant on the interiors of an actual
finite consecutive partition; each label is evaluated at a real sample
point in its cell, rather than introduced through an identity premise. -/
theorem exists_consecutivePartition_count_cells (d : ℕ) (T : Fin d → ℝ) :
    ∃ (m : ℕ) (ℓ : ConsecutivePartition m) (τ : Fin m → ℝ),
      ∀ j : Fin m,
        τ j ∈ Ioo (ℓ.boundary j.castSucc) (ℓ.boundary j.succ) ∧
        ∀ t ∈ Ioo (ℓ.boundary j.castSucc) (ℓ.boundary j.succ),
          boundaryArcCount d 0 t T = boundaryArcCount d 0 (τ j) T := by
  classical
  let S : Finset ℝ := {0, 1} ∪ Finset.univ.image (fun k : Fin d => Int.fract (T k))
  have hzero : (0 : ℝ) ∈ S := by simp [S]
  have hone : (1 : ℝ) ∈ S := by simp [S]
  have hpoint (k : Fin d) : Int.fract (T k) ∈ S := by simp [S]
  have hbounds {x : ℝ} (hx : x ∈ S) : 0 ≤ x ∧ x ≤ 1 := by
    simp only [S, Finset.mem_union, Finset.mem_insert, Finset.mem_singleton,
      Finset.mem_image, Finset.mem_univ, true_and] at hx
    rcases hx with (rfl | rfl) | ⟨k, rfl⟩
    · norm_num
    · norm_num
    · exact ⟨Int.fract_nonneg _, (Int.fract_lt_one _).le⟩
  have hcardpos : 0 < S.card := Finset.card_pos.mpr ⟨0, hzero⟩
  let m := S.card - 1
  have hcard : S.card = m + 1 := by dsimp [m]; omega
  let e : Fin (m + 1) ↪o ℝ := S.orderEmbOfFin hcard
  have hmem (i : Fin (m + 1)) : e i ∈ S := Finset.orderEmbOfFin_mem S hcard i
  have hsurj {x : ℝ} (hx : x ∈ S) : ∃ i : Fin (m + 1), e i = x := by
    have hx' : x ∈ Set.range e := by
      rw [show Set.range e = (S : Set ℝ) from Finset.range_orderEmbOfFin S hcard]
      exact hx
    exact hx'
  have hezero : e 0 = 0 := by
    obtain ⟨i, hi⟩ := hsurj hzero
    apply le_antisymm
    · simpa only [hi] using e.monotone (Fin.zero_le i)
    · exact (hbounds (hmem 0)).1
  have heone : e (Fin.last m) = 1 := by
    obtain ⟨i, hi⟩ := hsurj hone
    apply le_antisymm
    · exact (hbounds (hmem (Fin.last m))).2
    · simpa only [hi] using e.monotone (Fin.le_last i)
  let ℓ : ConsecutivePartition m := ⟨e, e.monotone, hezero, heone⟩
  let τ : Fin m → ℝ := fun j => (e j.castSucc + e j.succ) / 2
  have hgap (j : Fin m) : e j.castSucc < e j.succ :=
    e.strictMono (by change j.val < j.val + 1; omega)
  have hτ (j : Fin m) : τ j ∈ Ioo (e j.castSucc) (e j.succ) := by
    dsimp only [τ]
    constructor <;> linarith [hgap j]
  have hnone (j : Fin m) {x : ℝ} (hx : x ∈ S) :
      ¬ (e j.castSucc < x ∧ x < e j.succ) := by
    obtain ⟨i, rfl⟩ := hsurj hx
    intro h
    have h₁ : j.castSucc < i := e.lt_iff_lt.mp h.1
    have h₂ : i < j.succ := e.lt_iff_lt.mp h.2
    change j.val < i.val at h₁
    change i.val < j.val + 1 at h₂
    omega
  refine ⟨m, ℓ, τ, ?_⟩
  intro j
  refine ⟨hτ j, ?_⟩
  intro t ht
  have hequiv (k : Fin d) : Int.fract (T k) < t ↔ Int.fract (T k) < τ j := by
    constructor
    · intro hk
      by_contra hn
      have hn' : τ j ≤ Int.fract (T k) := le_of_not_gt hn
      exact hnone j (hpoint k) ⟨(hτ j).1.trans_le hn', hk.trans ht.2⟩
    · intro hk
      by_contra hn
      have hn' : t ≤ Int.fract (T k) := le_of_not_gt hn
      exact hnone j (hpoint k) ⟨ht.1.trans_le hn', hk.trans (hτ j).2⟩
  unfold boundaryArcCount
  simp only [sub_zero]
  congr 1
  exact Finset.filter_congr (fun k _ => hequiv k)

/-- Each actual circular assignment has genuine finite unitary labels
on a consecutive partition, obtained by sampling its literal step map. -/
theorem circularAssignmentStep_consecutive_representation {d r : ℕ} (hd : 0 < d)
    (V : Fin d → Circulation.Mat r) (hV : ∀ j, (V j)ᴴ * V j = 1)
    (a : Fin d) (T : Fin d → ℝ) :
    ∃ (m : ℕ) (ℓ : ConsecutivePartition m) (W : Fin m → Circulation.Mat r),
      (∀ j, (W j)ᴴ * W j = 1) ∧
      ∀ j : Fin m, ∀ t ∈ Ioo (ℓ.boundary j.castSucc) (ℓ.boundary j.succ),
        circularAssignmentStep hd V a T t = W j := by
  obtain ⟨m, ℓ, τ, hτ⟩ := exists_consecutivePartition_count_cells d T
  refine ⟨m, ℓ, fun j => circularAssignmentStep hd V a T (τ j), ?_, ?_⟩
  · intro j
    exact circularAssignmentStep_unitary hd V hV a T (τ j)
  · intro j t ht
    unfold circularAssignmentStep
    rw [(hτ j).2 t ht]

end
end CGLMPBounds.Partition
