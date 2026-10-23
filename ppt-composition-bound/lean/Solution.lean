module

public import PPTCompositionBound

/-!
# Proofs of the statements in `Challenge.lean`

Each theorem below has exactly the statement of its counterpart in `Challenge.lean` and is proved
from the library `PPTCompositionBound`. Comparator checks the match and the axioms used.

* `compose_ppt_maps_entanglementBreaking` and `ebIndex_le_of_isPPTMap` follow from
  `isEntanglementBreaking_compList` and `ebIndex_le` (`PPTCompositionBound/Main.lean`) with
  `j = d - 1`.
* `compose_at_least_ppt_maps_entanglementBreaking` uses `isEntanglementBreaking_compList_of_le`
  (`PPTCompositionBound/AtLeast.lean`).
* The sanity checks come from `PPTCompositionBound/NonTrivial.lean`,
  `PPTCompositionBound/ChoiBridge.lean`, `PPTCompositionBound/Counterexample.lean` and
  `PPTCompositionBound/Maps.lean`; `ebIndex_id_eq_top` is proved here.
-/

public section

open Matrix
open scoped Kronecker ComplexOrder

namespace PPTCompositionBound

theorem compose_ppt_maps_entanglementBreaking (d : ℕ) (hd : 2 ≤ d)
    (Φ : Fin (2 * (d - 1)) → Module.End ℂ (Matrix (Fin d) (Fin d) ℂ))
    (hΦ : ∀ i, IsPPTMap (Φ i)) :
    IsEntanglementBreaking (compList (List.ofFn Φ)) := by
  refine isEntanglementBreaking_compList (d - 1) (List.ofFn Φ) (by simp) (fun φ hφ => ?_)
    (by rw [Fintype.card_fin]; omega)
  rw [List.mem_ofFn] at hφ
  obtain ⟨i, rfl⟩ := hφ
  exact hΦ i

theorem ebIndex_le_of_isPPTMap (d : ℕ) (hd : 2 ≤ d) (T : Module.End ℂ (Matrix (Fin d) (Fin d) ℂ))
    (hT : IsPPTMap T) : ebIndex T ≤ ((2 * (d - 1) : ℕ) : ℕ∞) :=
  ebIndex_le hT (d - 1) (by omega) (by rw [Fintype.card_fin]; omega)

theorem compose_at_least_ppt_maps_entanglementBreaking (d : ℕ) (hd : 2 ≤ d) (N : ℕ)
    (hN : 2 * (d - 1) ≤ N) (Φ : Fin N → Module.End ℂ (Matrix (Fin d) (Fin d) ℂ))
    (hΦ : ∀ i, IsPPTMap (Φ i)) :
    IsEntanglementBreaking (compList (List.ofFn Φ)) := by
  refine isEntanglementBreaking_compList_of_le (d - 1) (List.ofFn Φ) (by simpa using hN)
    (fun φ hφ => ?_) (by rw [Fintype.card_fin]; omega)
  rw [List.mem_ofFn] at hφ
  obtain ⟨i, rfl⟩ := hφ
  exact hΦ i

theorem compose_ppt_map_interleaved_entanglementBreaking (d : ℕ) (hd : 2 ≤ d)
    (T : Module.End ℂ (Matrix (Fin d) (Fin d) ℂ)) (hT : IsPPTMap T)
    (S : Fin (2 * (d - 1) - 1) → Module.End ℂ (Matrix (Fin d) (Fin d) ℂ))
    (hS : ∀ i, IsCompletelyPositive (S i)) :
    IsEntanglementBreaking (compList (T :: List.ofFn fun i => T ∘ₗ S i)) := by
  refine isEntanglementBreaking_compList (d - 1) _ ?_ (fun φ hφ => ?_) (by rw [Fintype.card_fin]; omega)
  · simp only [List.length_cons, List.length_ofFn]
    omega
  · rcases List.mem_cons.mp hφ with rfl | hφ
    · exact hT
    · rw [List.mem_ofFn] at hφ
      obtain ⟨i, rfl⟩ := hφ
      exact hT.comp_isCompletelyPositive (hS i)

theorem exists_posSemidef_not_isSeparable (d : ℕ) (hd : 2 ≤ d) :
    ∃ X : Matrix (Fin 2 × Fin d) (Fin 2 × Fin d) ℂ,
      X.PosSemidef ∧ ¬ PPTCompositionBound.IsSeparable X :=
  ⟨pureState (bellVec d), Matrix.posSemidef_vecMulVec_self_star _, not_isSeparable_bell d hd⟩

theorem id_not_entanglementBreaking (d : ℕ) (hd : 2 ≤ d) :
    ¬ IsEntanglementBreaking (LinearMap.id : Module.End ℂ (Matrix (Fin d) (Fin d) ℂ)) :=
  not_isEntanglementBreaking_id d hd

theorem choi_isCompletelyPositive_iff {d p : ℕ}
    (Φ : Matrix (Fin d) (Fin d) ℂ →ₗ[ℂ] Matrix (Fin p) (Fin p) ℂ) :
    IsCompletelyPositive Φ ↔
      (refMap (Fin d) Φ
        (pureState (fun x : Fin d × Fin d => if x.1 = x.2 then (1 : ℂ) else 0))).PosSemidef :=
  isCompletelyPositive_iff_choi Φ

theorem choi_isPPTMap_iff {d p : ℕ}
    (Φ : Matrix (Fin d) (Fin d) ℂ →ₗ[ℂ] Matrix (Fin p) (Fin p) ℂ) :
    IsPPTMap Φ ↔
      (refMap (Fin d) Φ
          (pureState (fun x : Fin d × Fin d => if x.1 = x.2 then (1 : ℂ) else 0))).PosSemidef ∧
        (partialTransposeRef (refMap (Fin d) Φ
          (pureState (fun x : Fin d × Fin d => if x.1 = x.2 then (1 : ℂ) else 0)))).PosSemidef :=
  isPPTMap_iff_choi Φ

theorem choi_isEntanglementBreaking_iff {d p : ℕ}
    (Φ : Matrix (Fin d) (Fin d) ℂ →ₗ[ℂ] Matrix (Fin p) (Fin p) ℂ) :
    IsEntanglementBreaking Φ ↔
      PPTCompositionBound.IsSeparable (refMap (Fin d) Φ
        (pureState (fun x : Fin d × Fin d => if x.1 = x.2 then (1 : ℂ) else 0))) :=
  isEntanglementBreaking_iff_choi Φ

theorem transposeMap_isCompletelyCopositive_not_isCompletelyPositive :
    IsCompletelyCopositive (transposeMap (Fin 2)) ∧
      ¬ IsCompletelyPositive (transposeMap (Fin 2)) :=
  isCompletelyCopositive_and_not_isCompletelyPositive_transposeMap

theorem compList_pair {d : ℕ} (Φ₁ Φ₂ : Module.End ℂ (Matrix (Fin d) (Fin d) ℂ)) :
    compList [Φ₁, Φ₂] = Φ₂ ∘ₗ Φ₁ := by
  rw [compList_cons, compList_cons, compList_nil, LinearMap.id_comp]

theorem zero_map_isPPTMap_and_ebIndex_eq_one (d : ℕ) :
    IsPPTMap (0 : Module.End ℂ (Matrix (Fin d) (Fin d) ℂ)) ∧
      ebIndex (0 : Module.End ℂ (Matrix (Fin d) (Fin d) ℂ)) = 1 :=
  ⟨isPPTMap_zero, ebIndex_zero⟩

theorem ebIndex_id_eq_top (d : ℕ) (hd : 2 ≤ d) :
    ebIndex (LinearMap.id : Module.End ℂ (Matrix (Fin d) (Fin d) ℂ)) = ⊤ := by
  have hpow : ∀ k : ℕ,
      (LinearMap.id : Module.End ℂ (Matrix (Fin d) (Fin d) ℂ)) ^ k = LinearMap.id := by
    intro k
    induction k with
    | zero => rw [pow_zero]; rfl
    | succ k ih => rw [pow_succ, ih, Module.End.mul_eq_comp, LinearMap.id_comp]
  refine top_le_iff.mp ?_
  unfold ebIndex
  refine le_iInf fun m => le_iInf fun _ => le_iInf fun h => ?_
  rw [hpow m] at h
  exact absurd h (not_isEntanglementBreaking_id d hd)

end PPTCompositionBound
