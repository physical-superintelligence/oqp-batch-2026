module

public import CausalNonpurifiability.Definitions.Purity
public import CausalNonpurifiability.Linear.Unitary

@[expose] public section


/-!
# `CausalNonpurifiability.Purification.Unitary`

Step 1 of the proof of Theorem 6.1 (manuscript Appendix A, `app:purcs`), which is the
implication "pure ⇒ Choi matrix of a unitary" of [AFNB, Theorem 2] recalled there
(`eq:exposed-unitary`).

In the definition of purity the additional systems `A'_I`, `B'_I` are taken to be copies of
`A_O`, `B_O`, the systems `A'_O`, `B'_O` copies of `A_I`, `B_I`, and the local channels are the
unitary channels `|i⟩|o⟩ ↦ |o⟩|i⟩`. The link product with their Choi matrices returns the
operator `S` with its laboratory factors renamed (`link_relabel`). Since `S` is pure, it is the
Choi matrix of a unitary `𝒰 : P ⊗ A_O ⊗ B_O → A_I ⊗ B_I ⊗ F` (`Pure.exists_unitary`); the
future index is written first in the row index of the matrix.

Only the second clause of `Pure` (unitary channels are mapped to unitary channels) is used here.
-/

set_option autoImplicit false

open Matrix
open scoped ComplexOrder Kronecker

namespace CausalNonpurifiability

/-! ### Choi matrices of basis relabellings -/

section Relabel

variable {α β : Type} [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β]

/-- The matrix of the unitary `|x⟩ ↦ |σ x⟩` that relabels the basis along `σ : α ≃ β`. -/
def relabelMatrix (σ : α ≃ β) : Matrix β α ℂ := Matrix.of fun y x => if y = σ x then 1 else 0

theorem relabelMatrix_conjTranspose_mul (σ : α ≃ β) :
    (relabelMatrix σ)ᴴ * relabelMatrix σ = 1 := by
  ext x x'
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, relabelMatrix, Matrix.of_apply,
    Matrix.one_apply]
  rw [Finset.sum_eq_single (σ x)]
  · by_cases h : x = x'
    · subst h
      simp
    · have h' : σ x ≠ σ x' := fun hσ => h (σ.injective hσ)
      simp [h, h']
  · intro y _ hy
    simp [hy]
  · intro h
    exact absurd (Finset.mem_univ _) h

theorem relabelMatrix_mul_conjTranspose (σ : α ≃ β) :
    relabelMatrix σ * (relabelMatrix σ)ᴴ = 1 := by
  ext y y'
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, relabelMatrix, Matrix.of_apply,
    Matrix.one_apply]
  rw [Finset.sum_eq_single (σ.symm y)]
  · by_cases h : y = y'
    · subst h
      simp
    · have h' : ¬ y' = y := fun hy => h hy.symm
      simp [h, h']
  · intro x _ hx
    have h' : ¬ y = σ x := fun hy => hx (by rw [hy, Equiv.symm_apply_apply])
    simp [h']
  · intro h
    exact absurd (Finset.mem_univ _) h

/-- Choi matrix (`eq:choi`, index `(input, output)`) of the unitary channel that relabels the
basis along `σ`. -/
def relabelChoi (σ : α ≃ β) : Op (α × β) :=
  Matrix.of fun x y => if x.2 = σ x.1 ∧ y.2 = σ y.1 then 1 else 0

theorem relabelChoi_unitary (σ : α ≃ β) : UnitaryChoi (relabelChoi σ) := by
  refine ⟨relabelMatrix σ, relabelMatrix_conjTranspose_mul σ, relabelMatrix_mul_conjTranspose σ,
    ?_⟩
  intro i o j o'
  simp only [relabelChoi, relabelMatrix, Matrix.of_apply]
  by_cases h1 : o = σ i <;> by_cases h2 : o' = σ j <;> simp [h1, h2]

theorem relabelChoi_ne_zero (σ : α ≃ β) (x y : α × β) (h : relabelChoi σ x y ≠ 0) :
    x.2 = σ x.1 ∧ y.2 = σ y.1 := by
  by_contra hc
  exact h (by simp [relabelChoi, hc])

end Relabel

/-- The exchange `(i, r) ↦ (e r, e'.symm i)` of a system with an additional system:
`X ⊗ R → Y ⊗ R'` for copies `R ≃ Y` and `R' ≃ X`. -/
def swapEquiv {X Y R R' : Type} (e : R ≃ Y) (e' : R' ≃ X) : (X × R) ≃ (Y × R') where
  toFun x := (e x.2, e'.symm x.1)
  invFun y := (e' y.2, e.symm y.1)
  left_inv := fun ⟨_, _⟩ => by simp
  right_inv := fun ⟨_, _⟩ => by simp

@[simp] theorem swapEquiv_apply {X Y R R' : Type} (e : R ≃ Y) (e' : R' ≃ X) (x : X × R) :
    swapEquiv e e' x = (e x.2, e'.symm x.1) := rfl

/-- A double sum with a single non-zero term. -/
theorem sum_sum_eq_single_of_ne_zero {L : Type} [Fintype L] [DecidableEq L] (g : L → L → ℂ)
    (l₀ l₀' : L) (hg : ∀ l l', g l l' ≠ 0 → l = l₀ ∧ l' = l₀') :
    ∑ l, ∑ l', g l l' = g l₀ l₀' := by
  rw [Finset.sum_eq_single l₀]
  · rw [Finset.sum_eq_single l₀']
    · intro l' _ hl'
      by_contra hne
      exact hl' (hg l₀ l' hne).2
    · intro h
      exact absurd (Finset.mem_univ _) h
  · intro l _ hl
    refine Finset.sum_eq_zero fun l' _ => ?_
    by_contra hne
    exact hl (hg l l' hne).1
  · intro h
    exact absurd (Finset.mem_univ _) h

section Link

variable {D : Ports} {p f a a' b b' : ℕ}

/-- The link product of `S` with the two exchange channels returns `S` with its laboratory
factors renamed (Step 1 of Appendix A: "inserting their Choi matrices in `eq:link` returns the
operator `S`"). -/
theorem link_relabel (S : HigherOp D p f) (eA : Fin (a + 1) ≃ Fin D.d)
    (eA' : Fin (a' + 1) ≃ Fin D.m) (eB : Fin (b + 1) ≃ Fin D.e) (eB' : Fin (b' + 1) ≃ Fin D.n)
    (x x' : Fin (p + 1)) (z z' : Fin (f + 1)) (rA rA₂ : Fin (a + 1)) (rA' rA₂' : Fin (a' + 1))
    (rB rB₂ : Fin (b + 1)) (rB' rB₂' : Fin (b' + 1)) :
    link D S (relabelChoi (swapEquiv eA eA')) (relabelChoi (swapEquiv eB eB'))
        ((x, (rA, rB)), (z, (rA', rB'))) ((x', (rA₂, rB₂)), (z', (rA₂', rB₂'))) =
      S ((x, ((eA' rA', eA rA), (eB' rB', eB rB))), z)
        ((x', ((eA' rA₂', eA rA₂), (eB' rB₂', eB rB₂))), z') := by
  rw [link_apply']
  rw [sum_sum_eq_single_of_ne_zero _ ((eA' rA', eA rA), (eB' rB', eB rB))
    ((eA' rA₂', eA rA₂), (eB' rB₂', eB rB₂))]
  · simp [relabelChoi, swapEquiv_apply]
  · rintro ⟨⟨i, o⟩, ⟨j, t⟩⟩ ⟨⟨i', o'⟩, ⟨j', t'⟩⟩ hne
    have hB := relabelChoi_ne_zero _ _ _ (right_ne_zero_of_mul hne)
    have hA := relabelChoi_ne_zero _ _ _ (right_ne_zero_of_mul (left_ne_zero_of_mul hne))
    simp only [swapEquiv_apply, Prod.mk.injEq] at hA hB
    obtain ⟨⟨hA1, hA2⟩, ⟨hA3, hA4⟩⟩ := hA
    obtain ⟨⟨hB1, hB2⟩, ⟨hB3, hB4⟩⟩ := hB
    subst hA1 hA2 hA3 hA4 hB1 hB2 hB3 hB4
    simp

end Link

/-- **Step 1 of Appendix A** (`eq:exposed-unitary`; the implication of [AFNB, Theorem 2] used
in the manuscript). A pure process `S` with global past `P` and global future `F` is the Choi
matrix `|𝒰⟩⟩⟨⟨𝒰|` of a unitary `𝒰 : P ⊗ A_O ⊗ B_O → A_I ⊗ B_I ⊗ F`. The rows of the matrix `U`
are indexed by `(F, (A_I, B_I))` and its columns by `(P, (A_O, B_O))`. -/
theorem Pure.exists_unitary {D : Ports} {p f : ℕ} {S : HigherOp D p f} (h : Pure D S) :
    ∃ U : Matrix (Fin (f + 1) × (Fin D.m × Fin D.n)) (Fin (p + 1) × (Fin D.d × Fin D.e)) ℂ,
      Uᴴ * U = 1 ∧ U * Uᴴ = 1 ∧
      ∀ (x x' : Fin (p + 1)) (z z' : Fin (f + 1)) (l l' : LabIndex D),
        S ((x, l), z) ((x', l'), z') =
          U (z, (l.1.1, l.2.1)) (x, (l.1.2, l.2.2)) *
            star (U (z', (l'.1.1, l'.2.1)) (x', (l'.1.2, l'.2.2))) := by
  let eA : Fin (D.d - 1 + 1) ≃ Fin D.d := finCongr (Nat.sub_add_cancel D.d_pos)
  let eA' : Fin (D.m - 1 + 1) ≃ Fin D.m := finCongr (Nat.sub_add_cancel D.m_pos)
  let eB : Fin (D.e - 1 + 1) ≃ Fin D.e := finCongr (Nat.sub_add_cancel D.e_pos)
  let eB' : Fin (D.n - 1 + 1) ≃ Fin D.n := finCongr (Nat.sub_add_cancel D.n_pos)
  obtain ⟨V, hV1, hV2, hV⟩ := h.2 (D.d - 1) (D.m - 1) (D.e - 1) (D.n - 1)
    (relabelChoi (swapEquiv eA eA')) (relabelChoi (swapEquiv eB eB'))
    (relabelChoi_unitary _) (relabelChoi_unitary _)
  let eOut : LinkOut f (D.m - 1) (D.n - 1) ≃ Fin (f + 1) × (Fin D.m × Fin D.n) :=
    Equiv.prodCongr (Equiv.refl _) (Equiv.prodCongr eA' eB')
  let eIn : LinkIn p (D.d - 1) (D.e - 1) ≃ Fin (p + 1) × (Fin D.d × Fin D.e) :=
    Equiv.prodCongr (Equiv.refl _) (Equiv.prodCongr eA eB)
  obtain ⟨hU1, hU2⟩ := biunitary_reindex eOut eIn ⟨hV1, hV2⟩
  refine ⟨Matrix.reindex eOut eIn V, hU1, hU2, ?_⟩
  intro x x' z z' l l'
  have key := hV (x, (eA.symm l.1.2, eB.symm l.2.2)) (z, (eA'.symm l.1.1, eB'.symm l.2.1))
    (x', (eA.symm l'.1.2, eB.symm l'.2.2)) (z', (eA'.symm l'.1.1, eB'.symm l'.2.1))
  rw [link_relabel] at key
  simp only [Equiv.apply_symm_apply, Prod.mk.eta] at key
  exact key

end CausalNonpurifiability
