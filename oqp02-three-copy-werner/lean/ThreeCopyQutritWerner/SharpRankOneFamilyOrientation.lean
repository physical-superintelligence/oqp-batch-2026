module

public import ThreeCopyQutritWerner.SharpRankOneFixedFactor

@[expose] public section


/-!
# Shared orientation of two all-rank-one gamma families

Each original family has a literal fixed factor. Three distinct indices
exclude the two opposite-orientation cases by the exact gamma three-cycle.
The remaining cases have two fixed vectors on one common local register,
whose span has dimension at most two.
-/

noncomputable section

open scoped BigOperators Matrix ComplexConjugate

namespace ThreeCopyQutritWerner

/-- Two normalized all-rank-one-combination gamma-one families with three
distinct members have their fixed factors on the same physical register. -/
theorem sharpRankOneFamilies_shared_orientation
    {ι L R : Type*} [Fintype ι] [Fintype L] [Fintype R] [DecidableEq ι]
    (u v : ι → L × R → ℂ)
    (hu : ∀ i j, braket (u i) (u j) = if i = j then 1 else 0)
    (hv : ∀ i j, braket (v i) (v j) = if i = j then 1 else 0)
    (hg : ∀ i j, sharpPartialTraceGamma (u i) (v i) (u j) (v j) = 1)
    (hru : ∀ z : ι → ℂ, (sharpReshape (fun r => ∑ i, z i * u i r)).rank ≤ 1)
    (hrv : ∀ z : ι → ℂ, (sharpReshape (fun r => ∑ i, z i * v i r)).rank ≤ 1)
    (i j k : ι) (hij : i ≠ j) (hjk : j ≠ k) (hki : k ≠ i) :
    (∃ a b : L → ℂ, (∃ l, a l ≠ 0) ∧ (∃ l, b l ≠ 0) ∧
      ∃ y z : ι → R → ℂ, ∀ p, u p = sharpProductVector a (y p) ∧
        v p = sharpProductVector b (z p)) ∨
    (∃ a b : R → ℂ, (∃ r, a r ≠ 0) ∧ (∃ r, b r ≠ 0) ∧
      ∃ x z : ι → L → ℂ, ∀ p, u p = sharpProductVector (x p) a ∧
        v p = sharpProductVector (z p) b) := by
  have huf := sharpRankOneFamily_exists_fixed_factor u (sharpFamily_norm_one u hu) hru i
  have hvf := sharpRankOneFamily_exists_fixed_factor v (sharpFamily_norm_one v hv) hrv i
  rcases huf with ⟨a, ha, y, hey⟩ | ⟨a, ha, x, hex⟩
  · rcases hvf with ⟨b, hb, z, hez⟩ | ⟨b, hb, z, hez⟩
    · exact Or.inl ⟨a, b, ha, hb, y, z, fun p => ⟨hey p, hez p⟩⟩
    · have hn := sharpProductFamily_opposite_orientation_impossible a b z y ha hb
        (fun p q => by simpa only [hey] using hu p q)
        (fun p q => by simpa only [hez] using hv p q)
        (fun p q => by simpa only [hey, hez] using hg p q) i j k hij hjk hki
      exact hn.elim
  · rcases hvf with ⟨b, hb, z, hez⟩ | ⟨b, hb, z, hez⟩
    · have hgs (p q : ι) : sharpPartialTraceGamma (v p) (u p) (v q) (u q) = 1 := by
        rw [sharpPartialTraceGamma_swap_families, hg, map_one]
      have hn := sharpProductFamily_opposite_orientation_impossible b a x z hb ha
        (fun p q => by simpa only [hez] using hv p q)
        (fun p q => by simpa only [hex] using hu p q)
        (fun p q => by simpa only [hez, hex] using hgs p q) i j k hij hjk hki
      exact hn.elim
    · exact Or.inr ⟨a, b, ha, hb, x, z, fun p => ⟨hex p, hez p⟩⟩

end ThreeCopyQutritWerner
