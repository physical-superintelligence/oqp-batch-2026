module

public import ThreeCopyQutritWerner.SharpFamilyAnchor

@[expose] public section


/-!
# A linear family of rank-one reshapes has a common factor

The literal two-by-two minor argument for sums of product vectors gives the
common-factor dichotomy. This concerns one vector family; joining the two
gamma-one families and choosing their common thin factor is a separate step.
-/

noncomputable section

open scoped BigOperators Matrix

namespace ThreeCopyQutritWerner

theorem sharpIsMultiple_trans {n : Type*} (x y z : n → ℂ)
    (hxy : TwoPlane.IsMultiple x y) (hyz : TwoPlane.IsMultiple y z) :
    TwoPlane.IsMultiple x z := by
  obtain ⟨a, ha⟩ := hxy
  obtain ⟨b, hb⟩ := hyz
  refine ⟨b * a, ?_⟩
  intro i
  rw [hb, ha]
  ring

theorem sharpIsMultiple_symm {n : Type*} (x y : n → ℂ)
    (hy : ∃ i, y i ≠ 0) (hxy : TwoPlane.IsMultiple x y) :
    TwoPlane.IsMultiple y x := by
  obtain ⟨a, ha⟩ := hxy
  have hne : a ≠ 0 := by
    intro hz
    obtain ⟨i, hi⟩ := hy
    exact hi (by rw [ha, hz, zero_mul])
  refine ⟨a⁻¹, ?_⟩
  intro i
  rw [ha, ← mul_assoc, inv_mul_cancel₀ hne, one_mul]

/-- If all pairwise sums of nonzero products are products, one factor is
common to the entire family. No finite-cardinality restriction is needed. -/
theorem sharpProductFamily_common_factor
    {ι L R : Type*} (x : ι → L → ℂ) (y : ι → R → ℂ)
    (hx : ∀ i, ∃ l, x i l ≠ 0) (hy : ∀ i, ∃ r, y i r ≠ 0)
    (hp : ∀ i j, ∃ a : L → ℂ, ∃ b : R → ℂ,
      ∀ l r, x i l * y i r + x j l * y j r = a l * b r)
    (i₀ : ι) :
    (∀ i, TwoPlane.IsMultiple (x i₀) (x i)) ∨
      (∀ i, TwoPlane.IsMultiple (y i₀) (y i)) := by
  classical
  have hor (i j : ι) : TwoPlane.IsMultiple (x i) (x j) ∨
      TwoPlane.IsMultiple (y i) (y j) := by
    by_contra! hn
    obtain ⟨a, b, hab⟩ := hp i j
    exact TwoPlane.not_product_of_minors (x i) (x j) (y i) (y j)
      (TwoPlane.exists_minor_ne_zero _ _ (hx i) hn.1)
      (TwoPlane.exists_minor_ne_zero _ _ (hy i) hn.2) a b hab
  by_cases hleft : ∀ i, TwoPlane.IsMultiple (x i₀) (x i)
  · exact Or.inl hleft
  · right
    obtain ⟨i, hi⟩ := not_forall.mp hleft
    have hiy := (hor i₀ i).resolve_left hi
    intro j
    by_contra hj
    have hjx := (hor i₀ j).resolve_right hj
    rcases hor i j with hijx | hijy
    · exact hi (sharpIsMultiple_trans _ _ _ hjx
        (sharpIsMultiple_symm _ _ (hx j) hijx))
    · exact hj (sharpIsMultiple_trans _ _ _ hiy hijy)

/-- Actual rectangular rank at most one supplies original product coordinates. -/
theorem sharpReshape_rank_le_one_exists_product
    {L R : Type*} [Fintype L] [Fintype R]
    (x : L × R → ℂ) (hx : (sharpReshape x).rank ≤ 1) :
    ∃ a : L → ℂ, ∃ b : R → ℂ, ∀ l r, x (l, r) = a l * b r := by
  obtain ⟨A, B, hAB⟩ := (rank_le_iff_exists_mul (sharpReshape x) 1).mp hx
  refine ⟨fun l => A l 0, fun r => B 0 r, ?_⟩
  intro l r
  have h := congrFun (congrFun hAB l) r
  simpa only [sharpReshape, Matrix.mul_apply, Fin.sum_univ_one] using h

/-- If every actual common combination has reshape rank at most one, the
whole normalized family has one fixed nonzero local factor. -/
theorem sharpRankOneFamily_exists_common_factor
    {ι L R : Type*} [Fintype ι] [Fintype L] [Fintype R] [DecidableEq ι]
    (u : ι → L × R → ℂ) (hu : ∀ i, vecNormSq (u i) = 1)
    (hr : ∀ z : ι → ℂ, (sharpReshape (fun r => ∑ i, z i * u i r)).rank ≤ 1)
    (i₀ : ι) :
    ∃ x : ι → L → ℂ, ∃ y : ι → R → ℂ,
      (∀ i l r, u i (l, r) = x i l * y i r) ∧
      (∀ i, ∃ l, x i l ≠ 0) ∧ (∀ i, ∃ r, y i r ≠ 0) ∧
      ((∀ i, TwoPlane.IsMultiple (x i₀) (x i)) ∨
        (∀ i, TwoPlane.IsMultiple (y i₀) (y i))) := by
  classical
  have hp (i : ι) : ∃ a : L → ℂ, ∃ b : R → ℂ, ∀ l r, u i (l, r) = a l * b r := by
    apply sharpReshape_rank_le_one_exists_product
    simpa [ite_mul] using hr (fun k => if k = i then 1 else 0)
  choose x y hxy using hp
  have hnon (i : ι) : (∃ l, x i l ≠ 0) ∧ (∃ r, y i r ≠ 0) := by
    obtain ⟨⟨l, r⟩, h⟩ := TwoPlane.exists_ne_zero_of_vecNormSq_eq_one (u i) (hu i)
    rw [hxy] at h
    exact ⟨⟨l, left_ne_zero_of_mul h⟩, ⟨r, right_ne_zero_of_mul h⟩⟩
  have hpair (i j : ι) : ∃ a : L → ℂ, ∃ b : R → ℂ,
      ∀ l r, x i l * y i r + x j l * y j r = a l * b r := by
    have hh : (sharpReshape (fun r => u i r + u j r)).rank ≤ 1 := by
      simpa [add_mul, Finset.sum_add_distrib, ite_mul] using
        hr (fun k => (if k = i then 1 else 0) + (if k = j then 1 else 0))
    obtain ⟨a, b, hab⟩ := sharpReshape_rank_le_one_exists_product _ hh
    exact ⟨a, b, fun l r => by simpa only [hxy] using hab l r⟩
  exact ⟨x, y, hxy, fun i => (hnon i).1, fun i => (hnon i).2,
    sharpProductFamily_common_factor x y (fun i => (hnon i).1)
      (fun i => (hnon i).2) hpair i₀⟩

end ThreeCopyQutritWerner
