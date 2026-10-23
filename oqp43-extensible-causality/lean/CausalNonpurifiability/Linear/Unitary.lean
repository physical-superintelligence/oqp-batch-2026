module

public import Mathlib
public import CausalNonpurifiability.Linear.Indices
public import CausalNonpurifiability.Linear.Positive

@[expose] public section


/-!
# `CausalNonpurifiability.Linear.Unitary`

Self-contained linear algebra for the ordered-purification module (`Boundary/Dilation`
consumes these):

* reindexing preserves both unitary equations (`conjTranspose_mul_self_reindex`,
  `self_mul_conjTranspose_reindex`, `biunitary_reindex`) — the `Fintype.equivOfCardEq`
  transport;
* PSD factorization `J = B Bᴴ` (and `Bᴴ B`) from the spectral theorem with `√` of the
  nonnegative eigenvalues (`posSemidef_eq_mul_conjTranspose`, `posSemidef_eq_conjTranspose_mul`)
  — used for `J'_C = B Bᴴ` with the full Choi index as Kraus index;
* unitary completion with prescribed columns: an isometry `V : Matrix N K ℂ` (`Vᴴ V = 1`) with
  an injective column placement `ι : K → N` extends to a unitary `U : Matrix N N ℂ` with
  `U i (ι k) = V i k` (`exists_unitary_completion`), via orthonormal-basis extension in
  `EuclideanSpace ℂ N`; and the product-indexed form
  (`exists_biunitary_extension_prod`: `|β| = |α × γ|`, columns `(a, g₀)` prescribed).

Manuscript anchors: §9, proof of Proposition 9.2 (the isometry "extends to a unitary"),
`eq:purification`.
-/

set_option autoImplicit false

open Matrix
open scoped ComplexOrder InnerProductSpace

namespace CausalNonpurifiability

/-! ### Reindexing preserves the unitary equations -/

section Reindex

variable {α β α' β' : Type}

theorem conjTranspose_mul_self_reindex [Fintype β] [Fintype β'] [DecidableEq α] [DecidableEq α']
    [DecidableEq β] [DecidableEq β'] (eβ : β ≃ β') (eα : α ≃ α') {U : Matrix β α ℂ}
    (hU : Uᴴ * U = 1) : (Matrix.reindex eβ eα U)ᴴ * Matrix.reindex eβ eα U = 1 := by
  rw [Matrix.conjTranspose_reindex, Matrix.reindex_apply, Matrix.reindex_apply,
    Matrix.submatrix_mul_equiv, hU, Matrix.submatrix_one_equiv]

theorem self_mul_conjTranspose_reindex [Fintype α] [Fintype α'] [DecidableEq α] [DecidableEq α']
    [DecidableEq β] [DecidableEq β'] (eβ : β ≃ β') (eα : α ≃ α') {U : Matrix β α ℂ}
    (hU : U * Uᴴ = 1) : Matrix.reindex eβ eα U * (Matrix.reindex eβ eα U)ᴴ = 1 := by
  rw [Matrix.conjTranspose_reindex, Matrix.reindex_apply, Matrix.reindex_apply,
    Matrix.submatrix_mul_equiv, hU, Matrix.submatrix_one_equiv]

/-- Both unitary equations are preserved by reindexing rows and columns along equivalences
(the `Fintype.equivOfCardEq` transport of biunitaries). -/
theorem biunitary_reindex [Fintype α] [Fintype β] [Fintype α'] [Fintype β'] [DecidableEq α]
    [DecidableEq β] [DecidableEq α'] [DecidableEq β'] (eβ : β ≃ β') (eα : α ≃ α')
    {U : Matrix β α ℂ} (hU : Uᴴ * U = 1 ∧ U * Uᴴ = 1) :
    (Matrix.reindex eβ eα U)ᴴ * Matrix.reindex eβ eα U = 1 ∧
      Matrix.reindex eβ eα U * (Matrix.reindex eβ eα U)ᴴ = 1 :=
  ⟨conjTranspose_mul_self_reindex eβ eα hU.1, self_mul_conjTranspose_reindex eβ eα hU.2⟩

end Reindex

/-! ### PSD factorization -/

section Factorization

variable {n : Type} [Fintype n] [DecidableEq n]

/-- Every PSD matrix is a Gram matrix `J = B Bᴴ`: take `B = U · diag √μ` from the spectral
theorem. -/
theorem posSemidef_eq_mul_conjTranspose {J : Matrix n n ℂ} (hJ : J.PosSemidef) :
    ∃ B : Matrix n n ℂ, J = B * Bᴴ := by
  have hH : J.IsHermitian := hJ.1
  set U : Matrix n n ℂ := (hH.eigenvectorUnitary : Matrix n n ℂ) with hUdef
  set D : Matrix n n ℂ :=
    Matrix.diagonal (fun i => ((Real.sqrt (hH.eigenvalues i) : ℝ) : ℂ)) with hDdef
  have hspec : J = U * Matrix.diagonal (RCLike.ofReal ∘ hH.eigenvalues) * Uᴴ := by
    have h := hH.spectral_theorem
    rwa [Unitary.conjStarAlgAut_apply, Matrix.star_eq_conjTranspose] at h
  have hD : D * Dᴴ = Matrix.diagonal (RCLike.ofReal ∘ hH.eigenvalues) := by
    rw [hDdef, Matrix.diagonal_conjTranspose, Matrix.diagonal_mul_diagonal]
    congr 1
    funext i
    simp only [Pi.star_apply, Complex.star_def, Complex.conj_ofReal, Function.comp_apply]
    rw [← Complex.ofReal_mul, Real.mul_self_sqrt (hJ.eigenvalues_nonneg i)]
    rfl
  refine ⟨U * D, ?_⟩
  calc J = U * Matrix.diagonal (RCLike.ofReal ∘ hH.eigenvalues) * Uᴴ := hspec
    _ = U * D * (U * D)ᴴ := by
        rw [Matrix.conjTranspose_mul]
        simp only [Matrix.mul_assoc]
        rw [← Matrix.mul_assoc D Dᴴ, hD]

/-- The `Bᴴ B` form of the factorization. -/
theorem posSemidef_eq_conjTranspose_mul {J : Matrix n n ℂ} (hJ : J.PosSemidef) :
    ∃ B : Matrix n n ℂ, J = Bᴴ * B := by
  obtain ⟨B, hB⟩ := posSemidef_eq_mul_conjTranspose hJ
  exact ⟨Bᴴ, by rw [Matrix.conjTranspose_conjTranspose]; exact hB⟩

end Factorization

/-! ### Unitary completion with prescribed columns -/

section Completion

variable {N K : Type}

/-- The `k`-th column of `V` as a vector of `EuclideanSpace ℂ N`. -/
noncomputable def colVec (V : Matrix N K ℂ) (k : K) : EuclideanSpace ℂ N :=
  WithLp.toLp 2 (fun i => V i k)

theorem inner_colVec [Fintype N] (V : Matrix N K ℂ) (k k' : K) :
    inner ℂ (colVec V k) (colVec V k') = (Vᴴ * V) k k' := by
  rw [EuclideanSpace.inner_eq_star_dotProduct, Matrix.mul_apply]
  simp only [colVec, WithLp.ofLp_toLp, dotProduct, Pi.star_apply, Matrix.conjTranspose_apply]
  exact Finset.sum_congr rfl fun i _ => mul_comm _ _

/-- A left inverse of a square complex matrix is a right inverse: `Uᴴ U = 1 → U Uᴴ = 1`
(through the unitary group). -/
theorem self_mul_conjTranspose_of_conjTranspose_mul_self [Fintype N] [DecidableEq N]
    {U : Matrix N N ℂ} (hU : Uᴴ * U = 1) : U * Uᴴ = 1 := by
  have h : star U * U = 1 := by rw [Matrix.star_eq_conjTranspose]; exact hU
  have h' := Matrix.mem_unitaryGroup_iff.mp (Matrix.mem_unitaryGroup_iff'.mpr h)
  rwa [Matrix.star_eq_conjTranspose] at h'

/-- **Unitary completion with prescribed columns** (manuscript §9: the isometry
"extends to a unitary").  An isometry `V : Matrix N K ℂ` (`Vᴴ V = 1`) whose columns are to sit
at the positions `ι k` (`ι` injective) extends to a unitary `U : Matrix N N ℂ` with
`U i (ι k) = V i k`: the columns of `V` are orthonormal in `EuclideanSpace ℂ N` and extend to an
orthonormal basis indexed by `N` (`Orthonormal.exists_orthonormalBasis_extension_of_card_eq`). -/
theorem exists_unitary_completion [Fintype N] [DecidableEq N] [Fintype K] [DecidableEq K]
    {ι : K → N} (hι : Function.Injective ι) (V : Matrix N K ℂ) (hV : Vᴴ * V = 1) :
    ∃ U : Matrix N N ℂ, Uᴴ * U = 1 ∧ U * Uᴴ = 1 ∧ ∀ i k, U i (ι k) = V i k := by
  classical
  -- the prescribed columns, placed at `ι k` and extended by zero elsewhere
  set v : N → EuclideanSpace ℂ N := Function.extend ι (colVec V) 0 with hvdef
  have hv : ∀ k, v (ι k) = colVec V k := fun k => hι.extend_apply _ _ k
  have horth : Orthonormal ℂ ((Set.range ι).domRestrict v) := by
    rw [orthonormal_iff_ite]
    intro x y
    obtain ⟨k, hk⟩ := x.2
    obtain ⟨k', hk'⟩ := y.2
    have hx : (Set.range ι).domRestrict v x = colVec V k := by
      rw [Set.domRestrict_apply, ← hk, hv]
    have hy : (Set.range ι).domRestrict v y = colVec V k' := by
      rw [Set.domRestrict_apply, ← hk', hv]
    have hxy : (x = y) ↔ (k = k') := by
      rw [Subtype.ext_iff, ← hk, ← hk', hι.eq_iff]
    rw [hx, hy, inner_colVec, hV, Matrix.one_apply]
    by_cases h : k = k' <;> simp [h, hxy]
  obtain ⟨b, hb⟩ :=
    horth.exists_orthonormalBasis_extension_of_card_eq (finrank_euclideanSpace (𝕜 := ℂ) (ι := N))
  set U : Matrix N N ℂ := Matrix.of fun i m => (b m).ofLp i with hUdef
  have hU1 : Uᴴ * U = 1 := by
    ext m m'
    have h := (orthonormal_iff_ite.mp b.orthonormal) m m'
    rw [EuclideanSpace.inner_eq_star_dotProduct] at h
    rw [Matrix.mul_apply, Matrix.one_apply, ← h]
    simp only [hUdef, Matrix.conjTranspose_apply, Matrix.of_apply, dotProduct, Pi.star_apply]
    exact Finset.sum_congr rfl fun i _ => mul_comm _ _
  refine ⟨U, hU1, self_mul_conjTranspose_of_conjTranspose_mul_self hU1, fun i k => ?_⟩
  rw [hUdef, Matrix.of_apply, hb (ι k) ⟨k, rfl⟩, hv, colVec, WithLp.ofLp_toLp]

/-- `submatrix` form of the column condition of `exists_unitary_completion`. -/
theorem exists_unitary_completion_submatrix [Fintype N] [DecidableEq N] [Fintype K] [DecidableEq K]
    {ι : K → N} (hι : Function.Injective ι) (V : Matrix N K ℂ) (hV : Vᴴ * V = 1) :
    ∃ U : Matrix N N ℂ, Uᴴ * U = 1 ∧ U * Uᴴ = 1 ∧ U.submatrix id ι = V := by
  obtain ⟨U, h1, h2, hcol⟩ := exists_unitary_completion hι V hV
  exact ⟨U, h1, h2, Matrix.ext fun i k => hcol i k⟩

end Completion

section CompletionProd

variable {α β γ : Type} [Fintype α] [Fintype β] [Fintype γ] [DecidableEq α] [DecidableEq β]
  [DecidableEq γ]

/-- Product-indexed form: an isometry `V : ℂ^α → ℂ^β` extends to a biunitary `U : ℂ^{α × γ} → ℂ^β`
(`|β| = |α × γ|`) whose columns `(a, g₀)` are the columns of `V`. -/
theorem exists_biunitary_extension_prod (g₀ : γ)
    (hcard : Fintype.card β = Fintype.card (α × γ)) (V : Matrix β α ℂ) (hV : Vᴴ * V = 1) :
    ∃ U : Matrix β (α × γ) ℂ, (Uᴴ * U = 1 ∧ U * Uᴴ = 1) ∧ ∀ b a, U b (a, g₀) = V b a := by
  classical
  set e : α × γ ≃ β := Fintype.equivOfCardEq hcard.symm with hedef
  have hι : Function.Injective (fun a : α => e (a, g₀)) := fun a a' h =>
    (Prod.mk.inj (e.injective h)).1
  obtain ⟨U', h1, h2, hcol⟩ := exists_unitary_completion hι V hV
  refine ⟨Matrix.reindex (Equiv.refl β) e.symm U', ⟨?_, ?_⟩, fun b a => ?_⟩
  · exact conjTranspose_mul_self_reindex _ _ h1
  · exact self_mul_conjTranspose_reindex _ _ h2
  · simp only [Matrix.reindex_apply, Matrix.submatrix_apply, Equiv.symm_symm, Equiv.refl_symm,
      Equiv.coe_refl, id_eq]
    exact hcol b a

end CompletionProd

end CausalNonpurifiability
