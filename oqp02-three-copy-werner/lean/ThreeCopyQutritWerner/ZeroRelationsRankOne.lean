module

public import ThreeCopyQutritWerner.ZeroRelationsAlgebra
public import ThreeCopyQutritWerner.InteriorReduction
public import ThreeCopyQutritWerner.AppendixCInputs

@[expose] public section


/-!
# Appendix C: the rank-one case of the symmetric feature

A nonzero symmetric matrix of rank at most one has the form `κ w wᵀ` with `κ ≠ 0`.
If its first two local antisymmetrizers vanish, the existing minor-factorization lemmas show
that `w` is fully product. When the matrix factors through `C`, a nonzero column is a fully
product vector in the range of `C`. Applied to `H(C,p)`, this supplies the algebraic premise
of the separate analytic equality input `AppCInput2`; that input itself remains open.
-/

noncomputable section

open scoped Matrix

namespace ThreeCopyQutritWerner

/-- Every nonzero symmetric rank-one matrix is a nonzero scalar times `w wᵀ`.
No square-root choice is necessary for the product-ray argument. -/
theorem exists_symmetric_rank_one_factor {n : Type*} [Fintype n]
    (H : Matrix n n ℂ) (hr : H.rank ≤ 1) (h0 : H ≠ 0) (hs : Hᵀ = H) :
    ∃ (w : n → ℂ) (κ : ℂ), w ≠ 0 ∧ κ ≠ 0 ∧ ∀ i j, H i j = κ * w i * w j := by
  obtain ⟨x, y, hxy⟩ := exists_eq_ketBra_of_rank_le_one H hr
  obtain ⟨r, s, hrs⟩ : ∃ r s, H r s ≠ 0 := by
    by_contra hn
    push_neg at hn
    apply h0
    ext i j
    exact hn i j
  have hxr : x r ≠ 0 := by
    intro hx
    apply hrs
    rw [hxy]
    simp [ketBra, hx]
  have he : ∀ i j, x i * (starRingEnd ℂ) (y j) = x j * (starRingEnd ℂ) (y i) := by
    intro i j
    have h := congrFun (congrFun hs j) i
    simpa only [Matrix.transpose_apply, hxy, ketBra] using h
  let κ : ℂ := (starRingEnd ℂ) (y r) / x r
  have hf : ∀ i j, H i j = κ * x i * x j := by
    intro i j
    rw [hxy]
    simp only [ketBra, κ, div_eq_mul_inv]
    have hinv := mul_inv_cancel₀ hxr
    linear_combination x i * (x r)⁻¹ * he r j -
      (x i * (starRingEnd ℂ) (y j)) * hinv
  refine ⟨x, κ, ?_, ?_, hf⟩
  · intro hx
    exact hxr (congrFun hx r)
  · intro hk
    apply h0
    ext i j
    rw [hf, hk]
    simp

section Product

variable {a b c : Type*} [Fintype a] [Fintype b] [Fintype c]

/-- Local symmetry of a nonzero scalar multiple of `w wᵀ` makes `w` fully product. -/
theorem isFullyProduct_of_local_symmetry_rank_one_factor
    (H : Matrix (a × b × c) (a × b × c) ℂ) (w : a × b × c → ℂ)
    (κ : ℂ) (hk : κ ≠ 0) (hf : ∀ i j, H i j = κ * w i * w j)
    (h1 : siteAnti₁ H = 0) (h2 : siteAnti₂ H = 0) : IsFullyProduct w := by
  have hm1 : ∀ i i' r r', w (i, r) * w (i', r') = w (i', r) * w (i, r') := by
    intro i i' r r'
    have he := congrFun (congrFun h1 (i, r)) (i', r')
    simp only [siteAnti₁, Matrix.of_apply, siteSwap₁, Equiv.coe_fn_mk, hf,
      Matrix.zero_apply] at he
    have hz : κ * (w (i, r) * w (i', r') - w (i', r) * w (i, r')) = 0 := by
      linear_combination 2 * he
    exact sub_eq_zero.mp ((mul_eq_zero.mp hz).resolve_left hk)
  have hm2 : ∀ j j' (r r' : a × c),
      w (r.1, j, r.2) * w (r'.1, j', r'.2) =
        w (r.1, j', r.2) * w (r'.1, j, r'.2) := by
    intro j j' r r'
    have he := congrFun (congrFun h2 (r.1, j, r.2)) (r'.1, j', r'.2)
    simp only [siteAnti₂, Matrix.of_apply, siteSwap₂, Equiv.coe_fn_mk, hf,
      Matrix.zero_apply] at he
    have hz : κ * (w (r.1, j, r.2) * w (r'.1, j', r'.2) -
        w (r.1, j', r.2) * w (r'.1, j, r'.2)) = 0 := by
      linear_combination 2 * he
    exact sub_eq_zero.mp ((mul_eq_zero.mp hz).resolve_left hk)
  obtain ⟨α₁, β₁, hw1⟩ := exists_product_of_minors w hm1
  obtain ⟨α₂, β₂, hw2⟩ := exists_product_of_minors
    (fun p : b × a × c => w (p.2.1, p.1, p.2.2)) hm2
  obtain ⟨u, v, z, hw⟩ := exists_full_product w
    ⟨α₁, β₁, fun i j k => hw1 i (j, k)⟩
    ⟨α₂, β₂, fun i j k => hw2 j (i, k)⟩
  exact ⟨u, v, z, fun r => hw r.1 r.2.1 r.2.2⟩

/-- A locally symmetric rank-one matrix whose range is contained in `ran C` gives a nonzero
fully product vector in `ran C`. The inclusion is supplied as a factorization `H=C N`. -/
theorem exists_product_in_range_of_symmetric_rank_one
    (C H N : Matrix (a × b × c) (a × b × c) ℂ) (hCN : H = C * N)
    (hr : H.rank ≤ 1) (h0 : H ≠ 0) (hs : Hᵀ = H)
    (h1 : siteAnti₁ H = 0) (h2 : siteAnti₂ H = 0) :
    ∃ x : a × b × c → ℂ, C *ᵥ x ≠ 0 ∧ IsFullyProduct (C *ᵥ x) := by
  classical
  obtain ⟨w, κ, hw, hk, hf⟩ := exists_symmetric_rank_one_factor H hr h0 hs
  have hp := isFullyProduct_of_local_symmetry_rank_one_factor H w κ hk hf h1 h2
  obtain ⟨t, ht⟩ : ∃ t, w t ≠ 0 := by
    by_contra hn
    push_neg at hn
    exact hw (funext hn)
  have hcol : C *ᵥ (N *ᵥ Pi.single t 1) = fun r => H r t := by
    rw [Matrix.mulVec_mulVec, ← hCN]
    funext r
    simp [Matrix.mulVec, dotProduct, Pi.single_apply]
  refine ⟨N *ᵥ Pi.single t 1, ?_, ?_⟩
  · rw [hcol]
    intro hz
    have he := congrFun hz t
    change H t t = 0 at he
    rw [hf] at he
    exact mul_ne_zero (mul_ne_zero hk ht) ht he
  · rw [hcol]
    obtain ⟨u, v, z, hwprod⟩ := hp
    refine ⟨fun i => κ * w t * u i, v, z, ?_⟩
    intro r
    change H r t = (κ * w t * u r.1) * v r.2.1 * z r.2.2
    rw [hf, hwprod r]
    ring

/-- Appendix C, rank-one branch of `H`: its local symmetries force a product ray in `ran C`.
The endpoint equality and analytic rigidity conclusions are not assumed or proved here. -/
theorem exists_product_in_range_of_hFeature_rank_one
    (X : Matrix (a × b × c) (Fin 2) ℂ) (B : Matrix (Fin 2) (a × b × c) ℂ)
    (hr : (X * B).rank = 2) (hH : (hFeature (X * B) (bivecMat X)).rank = 1)
    (h1 : siteAnti₁ (hFeature (X * B) (bivecMat X)) = 0)
    (h2 : siteAnti₂ (hFeature (X * B) (bivecMat X)) = 0) :
    ∃ x : a × b × c → ℂ, (X * B) *ᵥ x ≠ 0 ∧ IsFullyProduct ((X * B) *ᵥ x) := by
  obtain ⟨N, hN⟩ := hFeature_eq_mul_left_of_rank_two X B hr
  have h0 : hFeature (X * B) (bivecMat X) ≠ 0 := by
    intro hz
    rw [hz, Matrix.rank_zero] at hH
    omega
  exact exists_product_in_range_of_symmetric_rank_one (X * B) _ N hN hH.le h0
    (hFeature_transpose X B) h1 h2

end Product

end ThreeCopyQutritWerner

end
