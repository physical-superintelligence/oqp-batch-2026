module

public import ThreeCopyQutritWerner.ProductRayEquality
public import ThreeCopyQutritWerner.ProductRayFactorization

@[expose] public section


/-!
# Canonical product-ray equality at all three sites

The tensor comparison retains each site separately. These are statements about
all three actual reduced range matrices, without a permutation convention.
-/

noncomputable section

open scoped BigOperators Matrix ComplexOrder

namespace ThreeCopyQutritWerner

/-- Two explicit local source directions bound the physical support at site 2. -/
theorem localRangeDim₂_le_two_of_range_plane
    {a b c : Type*} [Fintype a] [Fintype b] [Fintype c]
    (C : Matrix (a × b × c) (a × b × c) ℂ) (u v : b → ℂ)
    (K L : Matrix (a × c) (a × b × c) ℂ)
    (hC : ∀ i r s, C (r.1, i, r.2) s = u i * K r s + v i * L r s) :
    localRangeDim₂ C ≤ 2 := by
  unfold localRangeDim₂
  apply (rank_le_iff_exists_mul _ 2).mpr
  refine ⟨Matrix.of fun i k => ![u i, v i] k,
    Matrix.of fun k j => ![∑ l : a, ∑ m : c, ∑ s, K (l, m) s * star (C (l, j, m) s),
      ∑ l : a, ∑ m : c, ∑ s, L (l, m) s * star (C (l, j, m) s)] k, ?_⟩
  ext i j
  simp only [ptrace₁₃, Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.of_apply,
    Fin.sum_univ_two]
  change (∑ l : a, ∑ m : c, ∑ s, C (l, i, m) s * star (C (l, j, m) s)) =
    u i * (∑ l : a, ∑ m : c, ∑ s, K (l, m) s * star (C (l, j, m) s)) +
    v i * (∑ l : a, ∑ m : c, ∑ s, L (l, m) s * star (C (l, j, m) s))
  calc
    _ = ∑ l : a, ∑ m : c, ∑ s,
        (u i * K (l, m) s + v i * L (l, m) s) * star (C (l, j, m) s) := by
      apply Finset.sum_congr rfl
      intro l _
      apply Finset.sum_congr rfl
      intro m _
      apply Finset.sum_congr rfl
      intro s _
      rw [hC i (l, m) s]
    _ = _ := by
      simp only [add_mul, mul_assoc, Finset.sum_add_distrib, Finset.mul_sum]

/-- Two explicit local source directions bound the physical support at site 3. -/
theorem localRangeDim₃_le_two_of_range_plane
    {a b c : Type*} [Fintype a] [Fintype b] [Fintype c]
    (C : Matrix (a × b × c) (a × b × c) ℂ) (u v : c → ℂ)
    (K L : Matrix (a × b) (a × b × c) ℂ)
    (hC : ∀ i r s, C (r.1, r.2, i) s = u i * K r s + v i * L r s) :
    localRangeDim₃ C ≤ 2 := by
  unfold localRangeDim₃
  apply (rank_le_iff_exists_mul _ 2).mpr
  refine ⟨Matrix.of fun i k => ![u i, v i] k,
    Matrix.of fun k j => ![∑ l : a, ∑ m : b, ∑ s, K (l, m) s * star (C (l, m, j) s),
      ∑ l : a, ∑ m : b, ∑ s, L (l, m) s * star (C (l, m, j) s)] k, ?_⟩
  ext i j
  simp only [ptrace₁₂, Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.of_apply,
    Fin.sum_univ_two]
  change (∑ l : a, ∑ m : b, ∑ s, C (l, m, i) s * star (C (l, m, j) s)) =
    u i * (∑ l : a, ∑ m : b, ∑ s, K (l, m) s * star (C (l, m, j) s)) +
    v i * (∑ l : a, ∑ m : b, ∑ s, L (l, m) s * star (C (l, m, j) s))
  calc
    _ = ∑ l : a, ∑ m : b, ∑ s,
        (u i * K (l, m) s + v i * L (l, m) s) * star (C (l, m, j) s) := by
      apply Finset.sum_congr rfl
      intro l _
      apply Finset.sum_congr rfl
      intro m _
      apply Finset.sum_congr rfl
      intro s _
      rw [hC i (l, m) s]
    _ = _ := by
      simp only [add_mul, mul_assoc, Finset.sum_add_distrib, Finset.mul_sum]

/-- The residual kernel lies in the site-2 local-defect kernel. -/
theorem productRay_second_defect_kernel (w : ProductRayThreePairs → ℂ)
    (hzero : expectation (tensor₃ productRayA productRayA productRayA -
      tensor₃ productRayB productRayB productRayB) w = 0) :
    tensor₃ (1 : Matrix ProductRayPair ProductRayPair ℂ) (productRayA - productRayB) 1 *ᵥ w = 0 := by
  have hQ := (posSemidef_tensor₃
    (Matrix.PosSemidef.one : (1 : Matrix ProductRayPair ProductRayPair ℂ).PosSemidef)
    productRayA_sub_B_posSemidef
    (Matrix.PosSemidef.one : (1 : Matrix ProductRayPair ProductRayPair ℂ).PosSemidef)).smul
    (by norm_num : (0 : ℝ) ≤ 1 / 16)
  have hdom := tensorCube_dominates_local_defect₂ productRayA productRayB
    productRayA_posSemidef productRayA_add_three_B_posSemidef
    productRayA_sub_B_posSemidef productRayA_sub_half_posSemidef
  have hk := mulVec_eq_zero_of_posSemidef_dominated _ _ hQ hdom w
    (by simpa only [expectation_eq_dotProduct] using hzero)
  rw [Matrix.smul_mulVec] at hk
  exact (smul_eq_zero.mp hk).resolve_left (by norm_num)

theorem tensor₃_mulVec_identity_fiber₂ {n : Type*} [Fintype n] [DecidableEq n]
    (Q : Matrix n n ℂ) (w : n × n × n → ℂ) (j k : n) :
    (fun i => (tensor₃ (1 : Matrix n n ℂ) Q 1 *ᵥ w) (j, i, k)) =
      Q *ᵥ (fun i => w (j, i, k)) := by
  ext i
  simp [tensor₃, Matrix.mulVec, dotProduct, Fintype.sum_prod_type,
    Matrix.one_apply, mul_ite, ite_mul]

theorem productRay_second_defects (b x d : ProductRayShore → ℂ)
    (hzero : endpointEnergy (productRayMatrix b x d) = 0) :
    ∀ r s : Fin 3 × Fin 3,
      x (r.1, 1, r.2) * star (d (s.1, 0, s.2)) = 0 ∧
      x (r.1, 2, r.2) * star (d (s.1, 0, s.2)) = 0 ∧
      x (r.1, 1, r.2) * star (d (s.1, 2, s.2)) = x (r.1, 2, r.2) * star (d (s.1, 1, s.2)) := by
  have hk := productRay_second_defect_kernel _ (productRay_residual_eq_zero b x d hzero)
  intro r s
  have hf : (productRayA - productRayB) *ᵥ
      (fun p => productRayPairTensor x (fun i => star (d i)) ((r.1, s.1), p, (r.2, s.2))) = 0 := by
    rw [← tensor₃_mulVec_identity_fiber₂, hk]
    rfl
  rw [productRayA_sub_B_eq_gram] at hf
  have hrows := (Matrix.conjTranspose_mul_self_mulVec_eq_zero _ _).mp hf
  simpa only [productRayPairTensor] using (productRayQ_mulVec_eq_zero_iff _).mp hrows

theorem productRay_canonical_zero_thin₂ (b x d : ProductRayShore → ℂ)
    (hd : d ≠ 0) (hzero : endpointEnergy (productRayMatrix b x d) = 0) :
    localRangeDim₂ (productRayMatrix b x d) ≤ 2 := by
  have hex : ∃ s, d s ≠ 0 := by
    by_contra h
    push_neg at h
    exact hd (funext h)
  obtain ⟨⟨j, k, l⟩, hs⟩ := hex
  have hdef := productRay_second_defects b x d hzero
  obtain ⟨u, v, hx⟩ := productRay_defects_force_local_plane
    (fun (i : Fin 3) (r : Fin 3 × Fin 3) => x (r.1, i, r.2))
    (fun (i : Fin 3) (s : Fin 3 × Fin 3) => star (d (s.1, i, s.2)))
    ⟨k, (j, l), by simpa only [ne_eq, star_eq_zero] using hs⟩
    (fun r s => (hdef r s).1) (fun r s => (hdef r s).2.1)
    (fun r s => (hdef r s).2.2)
  apply localRangeDim₂_le_two_of_range_plane (productRayMatrix b x d)
    (fun i => if i = 0 then 1 else 0) u
    (fun r s => (if r = (0, 0) then b s else 0) + x (r.1, 0, r.2) * d s)
    (fun r s => v r * d s)
  intro i r s
  change (if (r.1, i, r.2) = (0, 0, 0) then b s else 0) + x (r.1, i, r.2) * d s = _
  rw [hx i r]
  have he : (if (r.1, i, r.2) = (0, 0, 0) then b s else 0) =
      (if i = 0 then 1 else 0) * (if r = (0, 0) then b s else 0) := by
    rcases r with ⟨r₁, r₂⟩
    by_cases hi : i = 0 <;> by_cases h1 : r₁ = 0 <;> by_cases h2 : r₂ = 0 <;>
      simp [Prod.mk.injEq, hi, h1, h2]
  rw [he]
  ring

/-- The residual kernel lies in the site-3 local-defect kernel. -/
theorem productRay_third_defect_kernel (w : ProductRayThreePairs → ℂ)
    (hzero : expectation (tensor₃ productRayA productRayA productRayA -
      tensor₃ productRayB productRayB productRayB) w = 0) :
    tensor₃ (1 : Matrix ProductRayPair ProductRayPair ℂ) 1 (productRayA - productRayB) *ᵥ w = 0 := by
  have hQ := (posSemidef_tensor₃
    (Matrix.PosSemidef.one : (1 : Matrix ProductRayPair ProductRayPair ℂ).PosSemidef)
    (Matrix.PosSemidef.one : (1 : Matrix ProductRayPair ProductRayPair ℂ).PosSemidef)
    productRayA_sub_B_posSemidef).smul
    (by norm_num : (0 : ℝ) ≤ 1 / 16)
  have hdom := tensorCube_dominates_local_defect₃ productRayA productRayB
    productRayA_posSemidef productRayA_add_three_B_posSemidef
    productRayA_sub_B_posSemidef productRayA_sub_half_posSemidef
  have hk := mulVec_eq_zero_of_posSemidef_dominated _ _ hQ hdom w
    (by simpa only [expectation_eq_dotProduct] using hzero)
  rw [Matrix.smul_mulVec] at hk
  exact (smul_eq_zero.mp hk).resolve_left (by norm_num)

theorem tensor₃_mulVec_identity_fiber₃ {n : Type*} [Fintype n] [DecidableEq n]
    (Q : Matrix n n ℂ) (w : n × n × n → ℂ) (j k : n) :
    (fun i => (tensor₃ (1 : Matrix n n ℂ) 1 Q *ᵥ w) (j, k, i)) =
      Q *ᵥ (fun i => w (j, k, i)) := by
  ext i
  simp [tensor₃, Matrix.mulVec, dotProduct, Fintype.sum_prod_type,
    Matrix.one_apply, mul_ite, ite_mul]

theorem productRay_third_defects (b x d : ProductRayShore → ℂ)
    (hzero : endpointEnergy (productRayMatrix b x d) = 0) :
    ∀ r s : Fin 3 × Fin 3,
      x (r.1, r.2, 1) * star (d (s.1, s.2, 0)) = 0 ∧
      x (r.1, r.2, 2) * star (d (s.1, s.2, 0)) = 0 ∧
      x (r.1, r.2, 1) * star (d (s.1, s.2, 2)) = x (r.1, r.2, 2) * star (d (s.1, s.2, 1)) := by
  have hk := productRay_third_defect_kernel _ (productRay_residual_eq_zero b x d hzero)
  intro r s
  have hf : (productRayA - productRayB) *ᵥ
      (fun p => productRayPairTensor x (fun i => star (d i)) ((r.1, s.1), (r.2, s.2), p)) = 0 := by
    rw [← tensor₃_mulVec_identity_fiber₃, hk]
    rfl
  rw [productRayA_sub_B_eq_gram] at hf
  have hrows := (Matrix.conjTranspose_mul_self_mulVec_eq_zero _ _).mp hf
  simpa only [productRayPairTensor] using (productRayQ_mulVec_eq_zero_iff _).mp hrows

theorem productRay_canonical_zero_thin₃ (b x d : ProductRayShore → ℂ)
    (hd : d ≠ 0) (hzero : endpointEnergy (productRayMatrix b x d) = 0) :
    localRangeDim₃ (productRayMatrix b x d) ≤ 2 := by
  have hex : ∃ s, d s ≠ 0 := by
    by_contra h
    push_neg at h
    exact hd (funext h)
  obtain ⟨⟨j, k, l⟩, hs⟩ := hex
  have hdef := productRay_third_defects b x d hzero
  obtain ⟨u, v, hx⟩ := productRay_defects_force_local_plane
    (fun (i : Fin 3) (r : Fin 3 × Fin 3) => x (r.1, r.2, i))
    (fun (i : Fin 3) (s : Fin 3 × Fin 3) => star (d (s.1, s.2, i)))
    ⟨l, (j, k), by simpa only [ne_eq, star_eq_zero] using hs⟩
    (fun r s => (hdef r s).1) (fun r s => (hdef r s).2.1)
    (fun r s => (hdef r s).2.2)
  apply localRangeDim₃_le_two_of_range_plane (productRayMatrix b x d)
    (fun i => if i = 0 then 1 else 0) u
    (fun r s => (if r = (0, 0) then b s else 0) + x (r.1, r.2, 0) * d s)
    (fun r s => v r * d s)
  intro i r s
  change (if (r.1, r.2, i) = (0, 0, 0) then b s else 0) + x (r.1, r.2, i) * d s = _
  rw [hx i r]
  have he : (if (r.1, r.2, i) = (0, 0, 0) then b s else 0) =
      (if i = 0 then 1 else 0) * (if r = (0, 0) then b s else 0) := by
    rcases r with ⟨r₁, r₂⟩
    by_cases hi : i = 0 <;> by_cases h1 : r₁ = 0 <;> by_cases h2 : r₂ = 0 <;>
      simp [Prod.mk.injEq, hi, h1, h2]
  rw [he]
  ring

/-- Full canonical-ray version of the analytic product-ray equality input. -/
theorem canonical_product_ray_zero_localRangeDims
    (C : Matrix ProductRayShore ProductRayShore ℂ) (hr : C.rank = 2)
    (hzero : endpointEnergy C = 0)
    (hrange : ∃ z, C *ᵥ z = fun i => if i = (0, 0, 0) then 1 else 0) :
    localRangeDim₁ C ≤ 2 ∧ localRangeDim₂ C ≤ 2 ∧ localRangeDim₃ C ≤ 2 := by
  obtain ⟨b, x, d, hd, rfl⟩ := exists_productRayMatrix_of_canonical_in_range C hr hrange
  exact ⟨productRay_canonical_zero_thin₁ b x d hd hzero,
    productRay_canonical_zero_thin₂ b x d hd hzero,
    productRay_canonical_zero_thin₃ b x d hd hzero⟩

end ThreeCopyQutritWerner
