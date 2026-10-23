module

public import CausalNonpurifiability.Definitions.Purity
public import CausalNonpurifiability.Linear.Positive
public import CausalNonpurifiability.Linear.Unitary

@[expose] public section


/-!
# `CausalNonpurifiability.Definitions.LinkAlgebra`

Generic algebra of the link contraction `link` (`eq:link`) and of channel Choi matrices used by
the ordered purification (manuscript §9):

* `link` of rank-one operators is rank one, with the composed Choi vector `linkVec`
  (`link_rank_one`);
* `link` is additive, hence finitely additive, in each local channel argument
  (`link_add_left/right`, `link_sum_left/right`);
* Kraus decomposition of a channel Choi matrix (`kraus_of_channelChoi`) and the output partial
  trace of a sum of rank-one Choi matrices (`ptraceOut_sum_choiVec`).

The definitions `linkVec`, `choiVec` and every statement here are verbatim the ones of
`Boundary/Dilation` §6, so that module can `import CausalNonpurifiability.Definitions.LinkAlgebra` and drop its
local copies.  Conventions: `link` pairs the row laboratory index of `S` with the row laboratory
index of `J_A ⊗ J_B` (`eq:link`, `Definitions/Purity`); Choi vectors are `|K⟩⟩ (i,o) = K o i`
(`eq:choi`, untransposed, so `|K⟩⟩⟨⟨K| (i,o) (j,o') = K o i * star (K o' j)` as in
`UnitaryChoi`).
-/

set_option autoImplicit false

open scoped Kronecker ComplexOrder Matrix

namespace CausalNonpurifiability

noncomputable section

section LinkAlgebra

variable {D : Ports}

/-- The linked Choi vector `T s a b (i,o) = ∑_l s((i_P,l),o_F) a((l_{A_I},i_{E_A}),(l_{A_O},o_{E'_A}))
b((l_{B_I},i_{E_B}),(l_{B_O},o_{E'_B}))` of `eq:link` for rank-one inputs. -/
def linkVec {p f a a' b b' : ℕ} (s : (Fin (p + 1) × LabIndex D) × Fin (f + 1) → ℂ)
    (va : (Fin D.m × Fin (a + 1)) × (Fin D.d × Fin (a' + 1)) → ℂ)
    (vb : (Fin D.n × Fin (b + 1)) × (Fin D.e × Fin (b' + 1)) → ℂ) :
    LinkIn p a b × LinkOut f a' b' → ℂ :=
  fun u => ∑ l : LabIndex D,
    s ((u.1.1, l), u.2.1) * va ((l.1.1, u.1.2.1), (l.1.2, u.2.2.1)) *
      vb ((l.2.1, u.1.2.2), (l.2.2, u.2.2.2))

/-- `eq:link` of rank-one operators is rank one: `|s⟩⟨s| * (|a⟩⟨a| ⊗ |b⟩⟨b|) = |T s a b⟩⟨T s a b|`. -/
theorem link_rank_one {p f a a' b b' : ℕ} (s : (Fin (p + 1) × LabIndex D) × Fin (f + 1) → ℂ)
    (va : (Fin D.m × Fin (a + 1)) × (Fin D.d × Fin (a' + 1)) → ℂ)
    (vb : (Fin D.n × Fin (b + 1)) × (Fin D.e × Fin (b' + 1)) → ℂ) :
    link D (Matrix.vecMulVec s (star s)) (Matrix.vecMulVec va (star va))
        (Matrix.vecMulVec vb (star vb)) =
      Matrix.vecMulVec (linkVec s va vb) (star (linkVec s va vb)) := by
  ext u v
  simp only [link_apply, Matrix.vecMulVec_apply, linkVec, Pi.star_apply, star_sum, star_mul',
    Finset.sum_mul_sum]
  exact Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun l' _ => by ring

/-- `link` is additive in the Alice argument. -/
theorem link_add_left {p f a a' b b' : ℕ} (S : HigherOp D p f) (JA JA' : ExtChoiA D a a')
    (JB : ExtChoiB D b b') : link D S (JA + JA') JB = link D S JA JB + link D S JA' JB := by
  ext u v
  simp only [link_apply, Matrix.add_apply, mul_add, add_mul, Finset.sum_add_distrib]

/-- `link` is additive in the Bob argument. -/
theorem link_add_right {p f a a' b b' : ℕ} (S : HigherOp D p f) (JA : ExtChoiA D a a')
    (JB JB' : ExtChoiB D b b') : link D S JA (JB + JB') = link D S JA JB + link D S JA JB' := by
  ext u v
  simp only [link_apply, Matrix.add_apply, mul_add, Finset.sum_add_distrib]

theorem link_sum_left {ι : Type} [Fintype ι] {p f a a' b b' : ℕ} (S : HigherOp D p f)
    (JA : ι → ExtChoiA D a a') (JB : ExtChoiB D b b') :
    link D S (∑ k, JA k) JB = ∑ k, link D S (JA k) JB :=
  map_sum (AddMonoidHom.mk' (fun J => link D S J JB) (fun J J' => link_add_left S J J' JB)) JA
    Finset.univ

theorem link_sum_right {ι : Type} [Fintype ι] {p f a a' b b' : ℕ} (S : HigherOp D p f)
    (JA : ExtChoiA D a a') (JB : ι → ExtChoiB D b b') :
    link D S JA (∑ k, JB k) = ∑ k, link D S JA (JB k) :=
  map_sum (AddMonoidHom.mk' (fun J => link D S JA J) (fun J J' => link_add_right S JA J J')) JB
    Finset.univ

/-- The Choi vector `vec K (i, o) = K o i` of an operator `K : Matrix O I ℂ`
(`|K⟩⟩`, so that `|K⟩⟩⟨⟨K| (i,o) (j,o') = K o i * star (K o' j)`). -/
def choiVec {I O : Type} (K : Matrix O I ℂ) : I × O → ℂ := fun x => K x.2 x.1

/-- Kraus decomposition of a channel Choi matrix: `J = ∑_k |K_k⟩⟩⟨⟨K_k|` with `∑ K_kᴴ K_k = 1`
(from the Gram factorization `J = B Bᴴ`, Kraus index = the Choi index). -/
theorem kraus_of_channelChoi {I O : Type} [Fintype I] [Fintype O] [DecidableEq I]
    [DecidableEq O] {J : Op (I × O)} (hJ : ChannelChoi J) :
    ∃ K : I × O → Matrix O I ℂ,
      J = ∑ k, Matrix.vecMulVec (choiVec (K k)) (star (choiVec (K k))) ∧
        ∑ k, (K k)ᴴ * K k = 1 := by
  obtain ⟨B, hB⟩ := posSemidef_eq_mul_conjTranspose hJ.1
  refine ⟨fun k => Matrix.of fun o i => B (i, o) k, ?_, ?_⟩
  · ext x y
    rw [hB, Matrix.mul_apply, Matrix.sum_apply]
    simp only [Matrix.vecMulVec_apply, choiVec, Matrix.of_apply, Pi.star_apply,
      Matrix.conjTranspose_apply]
  · ext i j
    have h := congrFun (congrFun hJ.2 j) i
    rw [ptraceOut_apply] at h
    have hcol : ∀ o, ∑ k, star (B (i, o) k) * B (j, o) k = J (j, o) (i, o) := by
      intro o
      rw [hB, Matrix.mul_apply]
      simp only [Matrix.conjTranspose_apply]
      exact Finset.sum_congr rfl fun k _ => mul_comm _ _
    rw [Matrix.sum_apply]
    simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.of_apply]
    rw [Finset.sum_comm]
    simp only [hcol]
    rw [h, Matrix.one_apply, Matrix.one_apply]
    by_cases hij : i = j
    · simp [hij]
    · simp [hij, Ne.symm hij]

/-- `Tr_O ∑_k |K_k⟩⟩⟨⟨K_k| = (∑_k K_kᴴ K_k)ᵀ` (generalizes `UnitaryChoi.channelChoi`). -/
theorem ptraceOut_sum_choiVec {ι I O : Type} [Fintype ι] [Fintype I] [Fintype O]
    (K : ι → Matrix O I ℂ) :
    ptraceOut (∑ k, Matrix.vecMulVec (choiVec (K k)) (star (choiVec (K k)))) =
      (∑ k, (K k)ᴴ * K k)ᵀ := by
  ext i j
  rw [ptraceOut_apply, Matrix.transpose_apply, Matrix.sum_apply]
  simp only [Matrix.sum_apply, Matrix.vecMulVec_apply, choiVec, Pi.star_apply, Matrix.mul_apply,
    Matrix.conjTranspose_apply]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun o _ => mul_comm _ _

end LinkAlgebra

end

end CausalNonpurifiability
