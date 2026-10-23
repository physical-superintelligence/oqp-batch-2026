module

public import Mathlib

@[expose] public section


/-!
# `CausalNonpurifiability.Purification.Sector`

Linear algebra behind Steps 4–7 of the proof of Theorem 6.1 (manuscript Appendix A,
`app:purcs`): a splitting of the space of the global past into two orthogonal parts.

The manuscript obtains a decomposition `P = ⊕ₖ Lₖ ⊗ Rₖ` from the structure theorem for
finite-dimensional `*`-algebras (`eq:algebra-split`) and shows that every sector has a causal
order. **Proof route:** the formal proof uses two parts: the smallest subspace `K` that contains the
ranges of the operators `ah k` (the parts of Alice's operators that depend on Bob's output) and
is invariant under the operators `a i`, and its orthogonal complement. The hypotheses are the
commutation relations of Step 4 and the product relation `bh g * ah k = 0`, which is
`eq:LV-c` (Step 6).

* `sectorSpace a ah` — the subspace `K`.
* `exists_orthogonal_split` — orthogonal decomposition of a vector along a subspace, stated with
  the dot product.
* `exists_sector_split` — the splitting `e₀ = v₁ + v₂` with `ah k v₁ = 0`, `bh g v₂ = 0` and
  vanishing cross terms.
-/

set_option autoImplicit false

open Matrix
open scoped ComplexOrder

namespace CausalNonpurifiability

section Sector

variable {P : Type} [Fintype P] [DecidableEq P]

/-- `⟨u, M v⟩ = ⟨Mᴴ u, v⟩` for the standard sesquilinear form `(u, v) ↦ star u ⬝ᵥ v` on `ℂ^P`. -/
theorem star_dotProduct_mulVec_adjoint (M : Matrix P P ℂ) (u v : P → ℂ) :
    star u ⬝ᵥ (M *ᵥ v) = star (Mᴴ *ᵥ u) ⬝ᵥ v := by
  simp only [dotProduct, Matrix.mulVec, Pi.star_apply, Matrix.conjTranspose_apply, star_sum,
    star_mul', star_star, Finset.mul_sum, Finset.sum_mul]
  refine Finset.sum_comm.trans ?_
  exact Finset.sum_congr rfl fun y _ => Finset.sum_congr rfl fun x _ => by ring

/-- `⟨v, u⟩` is the complex conjugate of `⟨u, v⟩`. -/
theorem star_dotProduct_eq_star (u v : P → ℂ) : star v ⬝ᵥ u = star (star u ⬝ᵥ v) := by
  simp only [dotProduct, Pi.star_apply, star_sum, star_mul', star_star]
  exact Finset.sum_congr rfl fun x _ => mul_comm _ _

/-- Orthogonal decomposition of a vector along a subspace of `ℂ^P`, in dot-product form:
`e₀ = v₁ + v₂` with `v₂ ∈ K` and `v₁ ⟂ K`. -/
theorem exists_orthogonal_split (K : Submodule ℂ (P → ℂ)) (e₀ : P → ℂ) :
    ∃ v₁ v₂ : P → ℂ, e₀ = v₁ + v₂ ∧ v₂ ∈ K ∧ ∀ u ∈ K, star u ⬝ᵥ v₁ = 0 := by
  let K' : Submodule ℂ (EuclideanSpace ℂ P) :=
    { carrier := {y | y.ofLp ∈ K}
      add_mem' := fun {x y} hx hy => by
        have h : (x + y).ofLp = x.ofLp + y.ofLp := rfl
        show (x + y).ofLp ∈ K
        rw [h]
        exact K.add_mem hx hy
      zero_mem' := by
        have h : (0 : EuclideanSpace ℂ P).ofLp = 0 := rfl
        show (0 : EuclideanSpace ℂ P).ofLp ∈ K
        rw [h]
        exact K.zero_mem
      smul_mem' := fun c {x} hx => by
        have h : (c • x).ofLp = c • x.ofLp := rfl
        show (c • x).ofLp ∈ K
        rw [h]
        exact K.smul_mem c hx }
  haveI : CompleteSpace K' := FiniteDimensional.complete ℂ K'
  have hsplit : ∃ y ∈ K', ∃ z ∈ K'.orthogonal, (WithLp.toLp 2 e₀ : EuclideanSpace ℂ P) = y + z := by
    first
      | exact Submodule.exists_add_mem_mem_orthogonal (K := K') _
      | exact (by
          have hmem : (WithLp.toLp 2 e₀ : EuclideanSpace ℂ P) ∈ K' ⊔ K'.orthogonal := by
            rw [Submodule.sup_orthogonal_of_completeSpace]
            exact Submodule.mem_top
          obtain ⟨y, hy, z, hz, h⟩ := Submodule.mem_sup.mp hmem
          exact ⟨y, hy, z, hz, h.symm⟩)
  obtain ⟨y, hy, z, hz, hyz⟩ := hsplit
  refine ⟨z.ofLp, y.ofLp, ?_, hy, ?_⟩
  · have h : (WithLp.toLp 2 e₀ : EuclideanSpace ℂ P).ofLp = (y + z).ofLp :=
      congrArg WithLp.ofLp hyz
    have h2 : (y + z).ofLp = y.ofLp + z.ofLp := rfl
    rw [h2] at h
    rw [add_comm]
    exact h
  · intro u hu
    have hu' : (WithLp.toLp 2 u : EuclideanSpace ℂ P) ∈ K' := hu
    have h0 : inner ℂ (WithLp.toLp 2 u : EuclideanSpace ℂ P) z = 0 := by
      first
        | exact Submodule.inner_right_of_mem_orthogonal hu' hz
        | exact (Submodule.mem_orthogonal K' z).mp hz _ hu'
    rw [EuclideanSpace.inner_eq_star_dotProduct] at h0
    simpa [dotProduct, mul_comm] using h0

variable {ιA ιH ιB ιG : Type}

/-- The smallest subspace of `ℂ^P` that contains the ranges of all `ah k` and is invariant under
all `a i`. -/
def sectorSpace (a : ιA → Matrix P P ℂ) (ah : ιH → Matrix P P ℂ) : Submodule ℂ (P → ℂ) :=
  sInf {K | (∀ k w, ah k *ᵥ w ∈ K) ∧ ∀ i, ∀ v ∈ K, a i *ᵥ v ∈ K}

theorem range_mem_sectorSpace (a : ιA → Matrix P P ℂ) (ah : ιH → Matrix P P ℂ) (k : ιH)
    (w : P → ℂ) : ah k *ᵥ w ∈ sectorSpace a ah :=
  Submodule.mem_sInf.mpr fun _ hK => hK.1 k w

theorem mulVec_mem_sectorSpace (a : ιA → Matrix P P ℂ) (ah : ιH → Matrix P P ℂ) (i : ιA)
    {v : P → ℂ} (hv : v ∈ sectorSpace a ah) : a i *ᵥ v ∈ sectorSpace a ah :=
  Submodule.mem_sInf.mpr fun K hK => hK.2 i v (Submodule.mem_sInf.mp hv K hK)

/-- Induction principle: a subspace with the two closure properties contains `sectorSpace`. -/
theorem sectorSpace_le (a : ιA → Matrix P P ℂ) (ah : ιH → Matrix P P ℂ)
    (K : Submodule ℂ (P → ℂ)) (h1 : ∀ k w, ah k *ᵥ w ∈ K)
    (h2 : ∀ i, ∀ v ∈ K, a i *ᵥ v ∈ K) : sectorSpace a ah ≤ K :=
  sInf_le ⟨h1, h2⟩

/-- **Two-part splitting.** Let `a i`, `b j` be two families of operators on `ℂ^P` that are
closed under adjoints and commute with each other, and let `ah k`, `bh g` be further operators
with `ah` closed under adjoints, `ah k` commuting with every `b j`, `a i` commuting with every
`bh g`, and `bh g * ah k = 0`. Then every vector is a sum `v₁ + v₂` such that every `ah k`
annihilates `v₁`, every `bh g` annihilates `v₂`, and the operators `a i * b j` have no matrix
elements between `v₁` and `v₂`. -/
theorem exists_sector_split
    (a : ιA → Matrix P P ℂ) (ah : ιH → Matrix P P ℂ)
    (b : ιB → Matrix P P ℂ) (bh : ιG → Matrix P P ℂ)
    (ha_star : ∀ i, ∃ i', (a i)ᴴ = a i')
    (hah_star : ∀ k, ∃ k', (ah k)ᴴ = ah k')
    (hb_star : ∀ j, ∃ j', (b j)ᴴ = b j')
    (hab : ∀ i j, a i * b j = b j * a i)
    (hahb : ∀ k j, ah k * b j = b j * ah k)
    (habh : ∀ i g, a i * bh g = bh g * a i)
    (hzero : ∀ g k, bh g * ah k = 0)
    (e₀ : P → ℂ) :
    ∃ v₁ v₂ : P → ℂ, e₀ = v₁ + v₂ ∧
      (∀ k, ah k *ᵥ v₁ = 0) ∧ (∀ g, bh g *ᵥ v₂ = 0) ∧
      (∀ i j, star v₁ ⬝ᵥ ((a i * b j) *ᵥ v₂) = 0) ∧
      (∀ i j, star v₂ ⬝ᵥ ((a i * b j) *ᵥ v₁) = 0) := by
  have hK_ah : ∀ k w, ah k *ᵥ w ∈ sectorSpace a ah := range_mem_sectorSpace a ah
  have hK_a : ∀ i, ∀ v ∈ sectorSpace a ah, a i *ᵥ v ∈ sectorSpace a ah :=
    fun i v hv => mulVec_mem_sectorSpace a ah i hv
  -- every `bh g` annihilates the subspace
  have hK_bh : ∀ g, ∀ v ∈ sectorSpace a ah, bh g *ᵥ v = 0 := by
    intro g
    have hle : sectorSpace a ah ≤ LinearMap.ker (Matrix.mulVecLin (bh g)) := by
      refine sectorSpace_le a ah _ ?_ ?_
      · intro k w
        rw [LinearMap.mem_ker, Matrix.mulVecLin_apply, Matrix.mulVec_mulVec, hzero,
          Matrix.zero_mulVec]
      · intro i v hv
        rw [LinearMap.mem_ker, Matrix.mulVecLin_apply] at hv ⊢
        rw [Matrix.mulVec_mulVec, ← habh, ← Matrix.mulVec_mulVec, hv, Matrix.mulVec_zero]
    intro v hv
    have h := hle hv
    rwa [LinearMap.mem_ker, Matrix.mulVecLin_apply] at h
  -- the subspace is invariant under every `b j`
  have hK_b : ∀ j, ∀ v ∈ sectorSpace a ah, b j *ᵥ v ∈ sectorSpace a ah := by
    intro j
    have hle : sectorSpace a ah ≤ (sectorSpace a ah).comap (Matrix.mulVecLin (b j)) := by
      refine sectorSpace_le a ah _ ?_ ?_
      · intro k w
        rw [Submodule.mem_comap, Matrix.mulVecLin_apply, Matrix.mulVec_mulVec, ← hahb,
          ← Matrix.mulVec_mulVec]
        exact hK_ah k _
      · intro i v hv
        rw [Submodule.mem_comap, Matrix.mulVecLin_apply] at hv ⊢
        rw [Matrix.mulVec_mulVec, ← hab, ← Matrix.mulVec_mulVec]
        exact hK_a i _ hv
    intro v hv
    have h := hle hv
    rwa [Submodule.mem_comap, Matrix.mulVecLin_apply] at h
  obtain ⟨v₁, v₂, hsum, hv₂, horth⟩ := exists_orthogonal_split (sectorSpace a ah) e₀
  have horth' : ∀ u ∈ sectorSpace a ah, star v₁ ⬝ᵥ u = 0 := by
    intro u hu
    rw [star_dotProduct_eq_star, horth u hu, star_zero]
  refine ⟨v₁, v₂, hsum, ?_, fun g => hK_bh g v₂ hv₂, ?_, ?_⟩
  · intro k
    obtain ⟨k', hk'⟩ := hah_star k
    have h0 : star (ah k *ᵥ v₁) ⬝ᵥ (ah k *ᵥ v₁) = 0 := by
      rw [star_dotProduct_mulVec_adjoint, hk']
      exact horth _ (hK_ah k' _)
    have h1 : star (ah k *ᵥ v₁) ⬝ᵥ ((1 : Matrix P P ℂ) *ᵥ (ah k *ᵥ v₁)) = 0 := by
      rw [Matrix.one_mulVec]
      exact h0
    have h2 := (Matrix.PosSemidef.one : (1 : Matrix P P ℂ).PosSemidef).dotProduct_mulVec_zero_iff.mp h1
    rwa [Matrix.one_mulVec] at h2
  · intro i j
    apply horth'
    rw [← Matrix.mulVec_mulVec]
    exact hK_a i _ (hK_b j _ hv₂)
  · intro i j
    obtain ⟨i', hi'⟩ := ha_star i
    obtain ⟨j', hj'⟩ := hb_star j
    rw [star_dotProduct_mulVec_adjoint, Matrix.conjTranspose_mul, hi', hj',
      ← Matrix.mulVec_mulVec]
    exact horth _ (hK_b j' _ (hK_a i' _ hv₂))

end Sector

end CausalNonpurifiability
