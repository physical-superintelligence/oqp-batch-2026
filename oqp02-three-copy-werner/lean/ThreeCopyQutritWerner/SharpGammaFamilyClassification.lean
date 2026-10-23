module

public import ThreeCopyQutritWerner.SharpRankOneFamilyOrientation
public import ThreeCopyQutritWerner.SingularValueRank

@[expose] public section


/-!
# Complete physical support alternatives for rank-three sharp-PT families

Any rank-two reshape combination anchors one common coordinate annihilator.
If neither family contains such a combination, the common-null determinant
bound makes both spaces rank-one spaces. Their fixed factors must occupy the
same register. Every alternative describes the original two families.
-/

noncomputable section

open scoped BigOperators Matrix ComplexConjugate

namespace ThreeCopyQutritWerner

/-- Explicit original-coordinate support alternatives for the two actual
families: one common unitary annihilator, or two fixed vectors on one site. -/
def SharpQutritFamilyCommonSupport {ι : Type*} (u v : ι → Fin 3 × Fin 3 → ℂ) : Prop :=
  (∃ U : Matrix (Fin 3) (Fin 3) ℂ, ∃ a : Fin 3, Uᴴ * U = 1 ∧
    ∀ k c, (U * sharpReshape (u k)) a c = 0 ∧ (U * sharpReshape (v k)) a c = 0) ∨
  (∃ a b : Fin 3 → ℂ, (∃ l, a l ≠ 0) ∧ (∃ l, b l ≠ 0) ∧
    ∃ y z : ι → Fin 3 → ℂ, ∀ k, u k = sharpProductVector a (y k) ∧
      v k = sharpProductVector b (z k)) ∨
  (∃ a b : Fin 3 → ℂ, (∃ r, a r ≠ 0) ∧ (∃ r, b r ≠ 0) ∧
    ∃ x z : ι → Fin 3 → ℂ, ∀ k, u k = sharpProductVector (x k) a ∧
      v k = sharpProductVector (z k) b)

/-- Full complex gamma saturation and three distinct original family indices
imply physical common support alternatives, with every combination branch covered. -/
theorem sharpGammaFamily_three_indices_common_support
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (u v : ι → Fin 3 × Fin 3 → ℂ)
    (hu : ∀ i j, braket (u i) (u j) = if i = j then 1 else 0)
    (hv : ∀ i j, braket (v i) (v j) = if i = j then 1 else 0)
    (hg : ∀ i j, sharpPartialTraceGamma (u i) (v i) (u j) (v j) = 1)
    (i j k : ι) (hij : i ≠ j) (hjk : j ≠ k) (hki : k ≠ i) :
    SharpQutritFamilyCommonSupport u v := by
  classical
  by_cases h2u : ∃ z : ι → ℂ, (sharpReshape (fun r => ∑ p, z p * u p r)).rank = 2
  · obtain ⟨z, hz⟩ := h2u
    exact Or.inl (sharpGammaFamily_rank_two_combination_common_coordinates
      u v hu hv hg i j hij z hz)
  · by_cases h2v : ∃ z : ι → ℂ, (sharpReshape (fun r => ∑ p, z p * v p r)).rank = 2
    · obtain ⟨z, hz⟩ := h2v
      exact Or.inl (sharpGammaFamily_right_rank_two_combination_common_coordinates
        u v hu hv hg i j hij z hz)
    · have hru (z : ι → ℂ) : (sharpReshape (fun r => ∑ p, z p * u p r)).rank ≤ 1 := by
        have hle := sharp_rank_le_two_of_det_eq_zero _
          (sharpGammaFamily_common_reshape_det_zero u v hu hv hg z)
        have hne : (sharpReshape (fun r => ∑ p, z p * u p r)).rank ≠ 2 :=
          fun h => h2u ⟨z, h⟩
        omega
      have hgs (p q : ι) : sharpPartialTraceGamma (v p) (u p) (v q) (u q) = 1 := by
        rw [sharpPartialTraceGamma_swap_families, hg, map_one]
      have hrv (z : ι → ℂ) : (sharpReshape (fun r => ∑ p, z p * v p r)).rank ≤ 1 := by
        have hle := sharp_rank_le_two_of_det_eq_zero _
          (sharpGammaFamily_common_reshape_det_zero v u hv hu hgs z)
        have hne : (sharpReshape (fun r => ∑ p, z p * v p r)).rank ≠ 2 :=
          fun h => h2v ⟨z, h⟩
        omega
      exact Or.inr (sharpRankOneFamilies_shared_orientation
        u v hu hv hg hru hrv i j k hij hjk hki)

/-- Every actual rank-three two-qutrit sharp-PT extremizer has the displayed
common support structure for both original positive singular families.
The three indices come from the proved actual rank/cardinality identity. -/
theorem sharpPartialTrace_rank_three_family_common_support
    (X : Matrix (Fin 3 × Fin 3) (Fin 3 × Fin 3) ℂ) (hr : X.rank = 3)
    (hsat : frobSq (ptraceL X) + frobSq (ptraceR X) =
      nuclearTrace X ^ 2 + Complex.normSq X.trace) :
    SharpQutritFamilyCommonSupport (singularLeft X) (singularRight X) := by
  classical
  let e : Fin 3 ≃ SingularPositiveIndex X := Fintype.equivOfCardEq (by
    rw [Fintype.card_fin, singularPositive_card_eq_rank, hr])
  apply sharpGammaFamily_three_indices_common_support
    (singularLeft X) (singularRight X) (singularLeft_braket X) (singularRight_braket X)
    (sharpPartialTrace_singular_gamma_eq_one X hsat) (e 0) (e 1) (e 2)
  · exact fun h => (by decide : (0 : Fin 3) ≠ 1) (e.injective h)
  · exact fun h => (by decide : (1 : Fin 3) ≠ 2) (e.injective h)
  · exact fun h => (by decide : (2 : Fin 3) ≠ 0) (e.injective h)

end ThreeCopyQutritWerner
