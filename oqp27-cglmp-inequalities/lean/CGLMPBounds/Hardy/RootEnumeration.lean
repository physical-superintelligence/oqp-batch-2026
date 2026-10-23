module

public import CGLMPBounds.Hardy.RootFractions

@[expose] public section


/-!
# Finite enumeration of characteristic roots, including multiplicity

The enumeration packages the literal root multiset in a fixed finite product space, where compactness can be
used without a simple-spectrum or diagonalizability assumption.
-/

namespace CGLMPBounds.Hardy
noncomputable section
open Polynomial

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def charpolyRootEquiv (A : Matrix ι ι ℂ) : ι ≃ A.charpoly.roots :=
  Fintype.equivOfCardEq (by
    rw [Multiset.card_coe, charpoly_roots_card])

def charpolyRootVector (A : Matrix ι ι ℂ) (i : ι) : ℂ :=
  (charpolyRootEquiv A i : ℂ)

lemma charpolyRootVector_mem (A : Matrix ι ι ℂ) (i : ι) :
    charpolyRootVector A i ∈ A.charpoly.roots :=
  Multiset.coe_mem

lemma charpolyRootVector_multiset (A : Matrix ι ι ℂ) :
    Finset.univ.val.map (charpolyRootVector A) = A.charpoly.roots := by
  change Finset.univ.val.map
    ((fun a : A.charpoly.roots => (a : ℂ)) ∘ charpolyRootEquiv A) = _
  rw [← Multiset.map_map, Multiset.map_univ_val_equiv, Multiset.map_univ_coe]

def rootVectorPolynomial (v : ι → ℂ) : ℂ[X] :=
  ∏ i, (X - C (v i))

lemma rootVectorPolynomial_roots (v : ι → ℂ) :
    (rootVectorPolynomial v).roots = Finset.univ.val.map v := by
  simpa only [rootVectorPolynomial, Finset.prod, Multiset.map_map, Function.comp_def] using
    (Polynomial.roots_multiset_prod_X_sub_C (Finset.univ.val.map v))

lemma rootVectorPolynomial_eval (v : ι → ℂ) (z : ℂ) :
    (rootVectorPolynomial v).eval z = ∏ i, (z - v i) := by
  simp [rootVectorPolynomial, Polynomial.eval_prod]

lemma charpoly_eq_rootVectorPolynomial (A : Matrix ι ι ℂ) :
    A.charpoly = rootVectorPolynomial (charpolyRootVector A) := by
  rw [(IsAlgClosed.splits A.charpoly).eq_prod_roots_of_monic A.charpoly_monic,
    ← charpolyRootVector_multiset]
  simp only [Multiset.map_map]
  rfl

lemma charpoly_root_sum_eq_vector_sum (A : Matrix ι ι ℂ) (f : ℂ → ℝ) :
    (A.charpoly.roots.map f).sum = ∑ i, f (charpolyRootVector A i) := by
  rw [← charpolyRootVector_multiset]
  simp only [Multiset.map_map]
  rfl

lemma root_sum_eq_vector_sum_of_factorization (A : Matrix ι ι ℂ)
    (v : ι → ℂ) (hv : A.charpoly = rootVectorPolynomial v) (f : ℂ → ℝ) :
    (A.charpoly.roots.map f).sum = ∑ i, f (v i) := by
  rw [hv, rootVectorPolynomial_roots]
  simp only [Multiset.map_map]
  rfl

end
end CGLMPBounds.Hardy
