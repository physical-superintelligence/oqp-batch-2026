module

public import ThreeCopyQutritWerner.CertificateX2BridgeKinds

@[expose] public section


/-!
# The source Q-form blocks are positive semidefinite

For every arrangement `t` of local types, the three-site source Q-form `x2FullTensor D s N t`
read on the ambient `Fin m_{t₀} × Fin m_{t₁} × Fin m_{t₂}` is a nonnegative combination of
reindexed input blocks `x2InputBlock D s N k`, each a congruence of `N k` (plus the standard-copy
partner congruence). Hence it is positive semidefinite whenever every source block `N k` is.
This is the positivity input of the lifted source Gram `G_s` in the bridge.
-/

noncomputable section

open scoped BigOperators Matrix Kronecker ComplexOrder

namespace ThreeCopyQutritWerner

/-- The source Q-form at arrangement `t` as a matrix on that arrangement's ambient. -/
def x2SourceBlock (D : X2Data) (s : Fin 3) (N : X2Blocks s) (t : Fin 3 → Fin 8) :
    Matrix (Fin (x2Mult s (t 0)) × Fin (x2Mult s (t 1)) × Fin (x2Mult s (t 2)))
      (Fin (x2Mult s (t 0)) × Fin (x2Mult s (t 1)) × Fin (x2Mult s (t 2))) ℚ :=
  Matrix.of fun a b => x2FullTensor D s N t ![(a.1 : ℕ), a.2.1, a.2.2] ![(b.1 : ℕ), b.2.1, b.2.2]

theorem x2InputBlock_posSemidef (D : X2Data) (s : Fin 3) (N : X2Blocks s) (k : x2Key s)
    (hN : (x2Complex (N k)).PosSemidef) : (x2Complex (x2InputBlock D s N k)).PosSemidef := by
  unfold x2InputBlock
  simp only
  rw [x2Complex_add]
  apply Matrix.PosSemidef.add
  · have h := x2_posSemidef_congr (N k)
      ((x2GramKron s k * D.image s k).map (Int.cast : ℤ → ℚ))ᵀ hN
    rwa [Matrix.transpose_transpose] at h
  · split_ifs
    · rw [x2Complex_smul]
      apply Matrix.PosSemidef.smul _ (x2_ratCast_nonneg (by norm_num))
      have h := x2_posSemidef_congr (N k)
        (x2Partner ((x2GramKron s k * D.image s k).map (Int.cast : ℤ → ℚ)))ᵀ hN
      rwa [Matrix.transpose_transpose] at h
    · simp only [x2Complex, Matrix.map_zero (f := fun q : ℚ => (q : ℂ)) (by simp)]
      exact Matrix.PosSemidef.zero

/-- Reindexing a three-site lookup by a coordinate permutation is a submatrix. -/
theorem x2Lookup_comp_eq_submatrix {p q r p' q' r' : ℕ}
    (M : Matrix (Fin p × Fin q × Fin r) (Fin p × Fin q × Fin r) ℚ)
    (π : Fin 3 → Fin 3)
    (e : (Fin p' × Fin q' × Fin r') → (Fin p × Fin q × Fin r))
    (he : ∀ a : Fin p' × Fin q' × Fin r',
      ((e a).1 : ℕ) = (![(a.1 : ℕ), a.2.1, a.2.2] ∘ π) 0 ∧
      ((e a).2.1 : ℕ) = (![(a.1 : ℕ), a.2.1, a.2.2] ∘ π) 1 ∧
      ((e a).2.2 : ℕ) = (![(a.1 : ℕ), a.2.1, a.2.2] ∘ π) 2)
    (a b : Fin p' × Fin q' × Fin r') :
    x2Lookup M (![(a.1 : ℕ), a.2.1, a.2.2] ∘ π) (![(b.1 : ℕ), b.2.1, b.2.2] ∘ π) =
      M (e a) (e b) := by
  obtain ⟨ha0, ha1, ha2⟩ := he a
  obtain ⟨hb0, hb1, hb2⟩ := he b
  unfold x2Lookup
  rw [dif_pos ⟨⟨ha0 ▸ (e a).1.isLt, ha1 ▸ (e a).2.1.isLt, ha2 ▸ (e a).2.2.isLt⟩,
    ⟨hb0 ▸ (e b).1.isLt, hb1 ▸ (e b).2.1.isLt, hb2 ▸ (e b).2.2.isLt⟩⟩]
  congr 1
  · exact Prod.ext (Fin.ext ha0.symm) (Prod.ext (Fin.ext ha1.symm) (Fin.ext ha2.symm))
  · exact Prod.ext (Fin.ext hb0.symm) (Prod.ext (Fin.ext hb1.symm) (Fin.ext hb2.symm))

/-- The reindexing of an arrangement's ambient by a sorting permutation. -/
def x2ArrangeMap (s : Fin 3) (t τ : Fin 3 → Fin 8) (π : Fin 3 → Fin 3) (h : t ∘ π = τ)
    (a : Fin (x2Mult s (t 0)) × Fin (x2Mult s (t 1)) × Fin (x2Mult s (t 2))) :
    Fin (x2Mult s (τ 0)) × Fin (x2Mult s (τ 1)) × Fin (x2Mult s (τ 2)) :=
  let c : Fin 3 → ℕ := ![(a.1 : ℕ), a.2.1, a.2.2]
  have hc : ∀ i, c i < x2Mult s (t i) := by
    intro i
    fin_cases i
    · exact a.1.isLt
    · exact a.2.1.isLt
    · exact a.2.2.isLt
  have hτ : ∀ j, x2Mult s (t (π j)) = x2Mult s (τ j) := fun j => by
    rw [← h]; rfl
  (⟨c (π 0), hτ 0 ▸ hc (π 0)⟩, ⟨c (π 1), hτ 1 ▸ hc (π 1)⟩, ⟨c (π 2), hτ 2 ▸ hc (π 2)⟩)

theorem x2ArrangeMap_val (s : Fin 3) (t τ : Fin 3 → Fin 8) (π : Fin 3 → Fin 3) (h : t ∘ π = τ)
    (a : Fin (x2Mult s (t 0)) × Fin (x2Mult s (t 1)) × Fin (x2Mult s (t 2))) :
    ((x2ArrangeMap s t τ π h a).1 : ℕ) = (![(a.1 : ℕ), a.2.1, a.2.2] ∘ π) 0 ∧
      ((x2ArrangeMap s t τ π h a).2.1 : ℕ) = (![(a.1 : ℕ), a.2.1, a.2.2] ∘ π) 1 ∧
      ((x2ArrangeMap s t τ π h a).2.2 : ℕ) = (![(a.1 : ℕ), a.2.1, a.2.2] ∘ π) 2 :=
  ⟨rfl, rfl, rfl⟩

/-- POSITIVITY OF THE SOURCE Q-FORM BLOCKS: for positive semidefinite source blocks, the source
Q-form is positive semidefinite on every arrangement. -/
theorem x2SourceBlock_posSemidef (D : X2Data) (s : Fin 3) (N : X2Blocks s)
    (hN : ∀ k, (x2Complex (N k)).PosSemidef) (t : Fin 3 → Fin 8) :
    (x2Complex (x2SourceBlock D s N t)).PosSemidef := by
  have hsum : x2SourceBlock D s N t = ∑ k : x2Key s, ∑ p : Fin 6,
      (if h : t ∘ x2Perm3 p = x2KeyTypes s k then
        ((x2ArrangeCount t (x2KeyTypes s k) : ℚ))⁻¹ •
          (x2InputBlock D s N k).submatrix (x2ArrangeMap s t (x2KeyTypes s k) (x2Perm3 p) h)
            (x2ArrangeMap s t (x2KeyTypes s k) (x2Perm3 p) h)
      else 0) := by
    ext a b
    simp only [x2SourceBlock, Matrix.of_apply, x2FullTensor, Matrix.sum_apply]
    apply Finset.sum_congr rfl
    intro k _
    apply Finset.sum_congr rfl
    intro p _
    by_cases h : t ∘ x2Perm3 p = x2KeyTypes s k
    · rw [if_pos h, dif_pos h, Matrix.smul_apply, Matrix.submatrix_apply, smul_eq_mul,
        x2Lookup_comp_eq_submatrix _ (x2Perm3 p) _ (x2ArrangeMap_val s t _ (x2Perm3 p) h)]
    · rw [if_neg h, dif_neg h, Matrix.zero_apply]
  rw [hsum, x2Complex_sum]
  apply Matrix.posSemidef_sum
  intro k _
  rw [x2Complex_sum]
  apply Matrix.posSemidef_sum
  intro p _
  by_cases h : t ∘ x2Perm3 p = x2KeyTypes s k
  · rw [dif_pos h, x2Complex_smul]
    apply Matrix.PosSemidef.smul _ (x2_ratCast_nonneg (inv_nonneg.mpr (Nat.cast_nonneg _)))
    have h' := (x2InputBlock_posSemidef D s N k (hN k)).submatrix
      (x2ArrangeMap s t (x2KeyTypes s k) (x2Perm3 p) h)
    simpa only [x2Complex, Matrix.submatrix_map] using h'
  · rw [dif_neg h]
    simp only [x2Complex, Matrix.map_zero (f := fun q : ℚ => (q : ℂ)) (by simp)]
    exact Matrix.PosSemidef.zero

end ThreeCopyQutritWerner

end
