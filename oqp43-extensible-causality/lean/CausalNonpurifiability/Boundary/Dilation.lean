module

public import CausalNonpurifiability.Definitions.Purity
public import CausalNonpurifiability.Definitions.Process
public import CausalNonpurifiability.Linear.Unitary
public import CausalNonpurifiability.Linear.Spectral
public import CausalNonpurifiability.Definitions.LinkAlgebra
public import CausalNonpurifiability.Boundary.Order
public import CausalNonpurifiability.Boundary.Swap

@[expose] public section


/-!
# `CausalNonpurifiability.Boundary.Dilation`

Ordered purification (manuscript §9 `sec:boundary`, Proposition 9.2 and the second half of
`thm:main` (iii)): every valid process of a definite order has a finite
purification, hence every valid process with a one-dimensional port is purifiable.

The construction is the finite sequential dilation `eq:ordered-W`–`eq:sequential-S`:
for `W ∈ O_{A≺B}`, `W = Ŵ ⊗ I_{B_O}` with `Tr_{B_I} Ŵ = ρ ⊗ I_{A_O}`; `R` a copy of the support
of `ρ` (`r = rank ρ`, `suppIso`, `Pσ`); the channel `J_C = (ρ^{-1/2} ⊗ I) Ŵ (ρ^{-1/2} ⊗ I)` on the
support (`eq:ordered-channel`, `Tr_{B_I} J_C = I_R ⊗ I_{A_O}` exactly); its Kraus/isometry form
`V_C` (Kraus index = Choi index, `q = r d n`) padded into `E_1` (`dim E_1 = r d t`, `t ≥ n`);
`dim E_0 = n t`, `dim P = m r n t`; the unitaries `U_0 : P → A_I R E_0`,
`U_1 : R A_O E_0 → B_I E_1`, and the rank-one higher-order operator `S = |s⟩⟨s|` of the comb
`P → A_I ⇝ A_O → B_I ⇝ B_O, F = B_O E_1`.  Complete purity and determinism both follow from
one layer lemma: the link of `S` with rank-one local Choi matrices `|A⟩⟩⟨⟨A|`, `|B⟩⟩⟨⟨B|` is the
rank-one Choi matrix of the four-layer composition `T A B = (B ⊗ 1)(U_1 ⊗ 1)(A ⊗ 1)(U_0 ⊗ 1)`.

The party swap `orderedBA_purifiable` is
`Purifiable.swap (orderedAB_purifiable hW.swap hord.swap)` from `CausalNonpurifiability.Boundary.Swap`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open scoped Kronecker ComplexOrder Matrix

namespace CausalNonpurifiability

noncomputable section

/-! ### 1. Biunitary matrices -/

section Biunitary

variable {α β γ : Type} [Fintype α] [Fintype β] [Fintype γ] [DecidableEq α] [DecidableEq β]
  [DecidableEq γ]

/-- Both unitary equations for a (possibly rectangular) matrix between finite types of equal
cardinality (AFNB Definition 3 requires both). -/
def Biunitary (U : Matrix β α ℂ) : Prop := Uᴴ * U = 1 ∧ U * Uᴴ = 1

theorem Biunitary.one : Biunitary (1 : Matrix α α ℂ) := by
  refine ⟨?_, ?_⟩ <;> simp

theorem Biunitary.mul {V : Matrix γ β ℂ} {U : Matrix β α ℂ} (hV : Biunitary V)
    (hU : Biunitary U) : Biunitary (V * U) := by
  refine ⟨?_, ?_⟩
  · rw [Matrix.conjTranspose_mul, Matrix.mul_assoc, ← Matrix.mul_assoc Vᴴ, hV.1, Matrix.one_mul,
      hU.1]
  · rw [Matrix.conjTranspose_mul, Matrix.mul_assoc, ← Matrix.mul_assoc U, hU.2, Matrix.one_mul,
      hV.2]

/-- `(A ⊗ B)ᴴ = Aᴴ ⊗ Bᴴ`. -/
theorem conjTranspose_kronecker' {l m n p : Type} (A : Matrix l m ℂ) (B : Matrix n p ℂ) :
    (A ⊗ₖ B)ᴴ = Aᴴ ⊗ₖ Bᴴ := by
  ext x y
  simp [Matrix.conjTranspose_apply, Matrix.kroneckerMap_apply, star_mul']

theorem Biunitary.kronecker_one {U : Matrix β α ℂ} (hU : Biunitary U) :
    Biunitary (U ⊗ₖ (1 : Matrix γ γ ℂ)) := by
  refine ⟨?_, ?_⟩
  · rw [conjTranspose_kronecker', ← Matrix.mul_kronecker_mul, hU.1, Matrix.conjTranspose_one,
      Matrix.one_mul, Matrix.one_kronecker_one]
  · rw [conjTranspose_kronecker', ← Matrix.mul_kronecker_mul, hU.2, Matrix.conjTranspose_one,
      Matrix.one_mul, Matrix.one_kronecker_one]

theorem Biunitary.one_kronecker {U : Matrix β α ℂ} (hU : Biunitary U) :
    Biunitary ((1 : Matrix γ γ ℂ) ⊗ₖ U) := by
  refine ⟨?_, ?_⟩
  · rw [conjTranspose_kronecker', ← Matrix.mul_kronecker_mul, hU.1, Matrix.conjTranspose_one,
      Matrix.one_mul, Matrix.one_kronecker_one]
  · rw [conjTranspose_kronecker', ← Matrix.mul_kronecker_mul, hU.2, Matrix.conjTranspose_one,
      Matrix.one_mul, Matrix.one_kronecker_one]

theorem Biunitary.reindex {α' β' : Type} [Fintype α'] [Fintype β'] [DecidableEq α']
    [DecidableEq β'] (eβ : β ≃ β') (eα : α ≃ α') {U : Matrix β α ℂ} (hU : Biunitary U) :
    Biunitary (Matrix.reindex eβ eα U) := by
  refine ⟨?_, ?_⟩
  · rw [Matrix.reindex_apply, Matrix.conjTranspose_submatrix, Matrix.submatrix_mul_equiv, hU.1,
      Matrix.submatrix_one_equiv]
  · rw [Matrix.reindex_apply, Matrix.conjTranspose_submatrix, Matrix.submatrix_mul_equiv, hU.2,
      Matrix.submatrix_one_equiv]

/-- `UnitaryChoi` in terms of `Biunitary`. -/
theorem unitaryChoi_iff_biunitary {I O : Type} [Fintype I] [Fintype O] [DecidableEq I]
    [DecidableEq O] (J : Op (I × O)) :
    UnitaryChoi J ↔ ∃ U : Matrix O I ℂ, Biunitary U ∧
      ∀ i o j o', J (i, o) (j, o') = U o i * star (U o' j) :=
  exists_congr fun _ => and_assoc.symm

end Biunitary

/-! ### 2–3. Spectral calculus and support annihilation: `CausalNonpurifiability.Linear.Spectral`. -/

/-! ### 4. Unitary completion with prescribed columns: `CausalNonpurifiability.Linear.Unitary` -/

/-- An isometry `V : ℂ^α → ℂ^β` (`Vᴴ V = 1`) extends to a biunitary `U : ℂ^{α × γ} → ℂ^β`
(`|β| = |α||γ|`) whose columns `(a, g₀)` are the columns of `V` (orthonormal completion;
manuscript §9: "extends to a unitary"); `exists_biunitary_extension_prod` of
`Linear.Unitary` in the `Biunitary` packaging. -/
theorem exists_biunitary_extension {α β γ : Type} [Fintype α] [Fintype β] [Fintype γ]
    [DecidableEq α] [DecidableEq β] [DecidableEq γ] (g₀ : γ)
    (hcard : Fintype.card β = Fintype.card (α × γ)) (V : Matrix β α ℂ) (hV : Vᴴ * V = 1) :
    ∃ U : Matrix β (α × γ) ℂ, Biunitary U ∧ ∀ b a, U b (a, g₀) = V b a :=
  exists_biunitary_extension_prod g₀ hcard V hV

/-! ### 5. The ordered data of `W ∈ O_{A≺B}` -/

section PartialTraceHelpers

variable {X Y : Type} [Fintype X] [Fintype Y] [DecidableEq X] [DecidableEq Y]

/-- `Tr_Y ((Q ⊗ I) M) = Q · Tr_Y M`. -/
theorem ptraceOut_kron_one_mul (Q : Op X) (M : Op (X × Y)) :
    ptraceOut ((Q ⊗ₖ (1 : Op Y)) * M) = Q * ptraceOut M := by
  ext i j
  simp only [ptraceOut_apply, Matrix.mul_apply, Matrix.kroneckerMap_apply, Matrix.one_apply,
    Fintype.sum_prod_type, mul_ite, mul_one, mul_zero, ite_mul, zero_mul, Finset.sum_ite_eq,
    Finset.mem_univ, if_true, Finset.mul_sum]
  exact Finset.sum_comm

/-- `Tr_Y (M (Q ⊗ I)) = Tr_Y M · Q`. -/
theorem ptraceOut_mul_kron_one (M : Op (X × Y)) (Q : Op X) :
    ptraceOut (M * (Q ⊗ₖ (1 : Op Y))) = ptraceOut M * Q := by
  ext i j
  simp only [ptraceOut_apply, Matrix.mul_apply, Matrix.kroneckerMap_apply, Matrix.one_apply,
    Fintype.sum_prod_type, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ,
    if_true, Finset.sum_mul]
  exact Finset.sum_comm

theorem ptraceOut_kron_one_mul_mul (Q : Op X) (M : Op (X × Y)) (Q' : Op X) :
    ptraceOut ((Q ⊗ₖ (1 : Op Y)) * M * (Q' ⊗ₖ (1 : Op Y))) = Q * ptraceOut M * Q' := by
  rw [Matrix.mul_assoc, ptraceOut_kron_one_mul, ptraceOut_mul_kron_one, Matrix.mul_assoc]

/-- `∑ₖ (M k ⊗ I) = (∑ₖ M k) ⊗ I`. -/
theorem sum_kronecker_one {ι l m n : Type} [Fintype ι] [DecidableEq n] (M : ι → Matrix l m ℂ) :
    ∑ k, (M k ⊗ₖ (1 : Matrix n n ℂ)) = (∑ k, M k) ⊗ₖ (1 : Matrix n n ℂ) := by
  ext x y
  simp [Matrix.sum_apply, Matrix.kroneckerMap_apply, Finset.sum_mul]

/-- `ptraceOut` commutes with finite sums. -/
theorem ptraceOut_sum' {ι : Type} [Fintype ι] (F : ι → Op (X × Y)) :
    ptraceOut (∑ k, F k) = ∑ k, ptraceOut (F k) :=
  map_sum ptraceOutₗ F Finset.univ

/-- Collapse a sum over a pair whose second component is pinned by a delta. -/
theorem sum_ite_snd {α β : Type} [Fintype α] [Fintype β] [DecidableEq β] (c : β) (g : α × β → ℂ) :
    ∑ y : α × β, (if y.2 = c then g y else 0) = ∑ a, g (a, c) := by
  rw [Fintype.sum_prod_type]
  exact Finset.sum_congr rfl fun a _ => by simp [Finset.sum_ite_eq']

/-- Collapse a sum over a pair whose second component is pinned by a delta (other orientation). -/
theorem sum_ite_snd' {α β : Type} [Fintype α] [Fintype β] [DecidableEq β] (c : β) (g : α × β → ℂ) :
    ∑ y : α × β, (if c = y.2 then g y else 0) = ∑ a, g (a, c) := by
  rw [Fintype.sum_prod_type]
  exact Finset.sum_congr rfl fun a _ => by simp [Finset.sum_ite_eq]

/-- Two nested deltas, the inner one pinning the summation variable. -/
theorem sum_ite_ite_eq {β : Type} [Fintype β] [DecidableEq β] (P : β → Prop) [DecidablePred P]
    (c : β) (G : β → ℂ) :
    ∑ x, (if P x then (if c = x then G x else 0) else 0) = if P c then G c else 0 := by
  rw [Finset.sum_eq_single c]
  · simp
  · intro b _ hb
    simp [Ne.symm hb]
  · intro h
    exact absurd (Finset.mem_univ c) h

/-- The sum permutation `(aI, aO, bI, r, e) ↦ (bI, r, aO, e, aI)` used to match the two sides of
the layer/link contraction. -/
theorem sum_perm5 {α β γ δ ε : Type} [Fintype α] [Fintype β] [Fintype γ] [Fintype δ] [Fintype ε]
    (F : α → β → γ → δ → ε → ℂ) :
    ∑ aI, ∑ aO, ∑ bI, ∑ r, ∑ e, F aI aO bI r e = ∑ bI, ∑ r, ∑ aO, ∑ e, ∑ aI, F aI aO bI r e := by
  calc ∑ aI, ∑ aO, ∑ bI, ∑ r, ∑ e, F aI aO bI r e
      = ∑ aI, ∑ bI, ∑ aO, ∑ r, ∑ e, F aI aO bI r e :=
        Finset.sum_congr rfl fun _ _ => Finset.sum_comm
    _ = ∑ bI, ∑ aI, ∑ aO, ∑ r, ∑ e, F aI aO bI r e := Finset.sum_comm
    _ = ∑ bI, ∑ aI, ∑ r, ∑ aO, ∑ e, F aI aO bI r e :=
        Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => Finset.sum_comm
    _ = ∑ bI, ∑ r, ∑ aI, ∑ aO, ∑ e, F aI aO bI r e :=
        Finset.sum_congr rfl fun _ _ => Finset.sum_comm
    _ = ∑ bI, ∑ r, ∑ aO, ∑ aI, ∑ e, F aI aO bI r e :=
        Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => Finset.sum_comm
    _ = ∑ bI, ∑ r, ∑ aO, ∑ e, ∑ aI, F aI aO bI r e :=
        Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ =>
          Finset.sum_congr rfl fun _ _ => Finset.sum_comm

/-- `|v⟩⟨v| = vecMulVec v (star v)` is positive. -/
theorem posSemidef_vecMulVec_star {ι : Type} [Fintype ι] (v : ι → ℂ) :
    (Matrix.vecMulVec v (star v)).PosSemidef := by
  have h : Matrix.vecMulVec v (star v) =
      (Matrix.of fun x (_ : Unit) => v x) * (Matrix.of fun x (_ : Unit) => v x)ᴴ := by
    ext x y
    simp [Matrix.mul_apply, Matrix.vecMulVec_apply]
  rw [h]
  exact Matrix.posSemidef_self_mul_conjTranspose _

end PartialTraceHelpers

section PartialTraceHelpers'

variable {X X' Y : Type} [Fintype X] [Fintype X'] [Fintype Y] [DecidableEq X] [DecidableEq X']
  [DecidableEq Y]

/-- Rectangular congruence commutes with the partial trace: `Tr_Y ((Qᴴ ⊗ I) M (Q ⊗ I)) = Qᴴ (Tr_Y M) Q`. -/
theorem ptraceOut_conj_kron_one (Q : Matrix X X' ℂ) (M : Op (X × Y)) :
    ptraceOut ((Qᴴ ⊗ₖ (1 : Op Y)) * M * (Q ⊗ₖ (1 : Op Y))) = Qᴴ * ptraceOut M * Q := by
  ext i j
  simp only [ptraceOut_apply, Matrix.mul_apply, Matrix.kroneckerMap_apply, Matrix.one_apply,
    Fintype.sum_prod_type, mul_ite, mul_one, mul_zero, ite_mul, zero_mul,
    Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_univ, if_true,
    Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun x _ => Finset.sum_comm

/-- `star (if c then x else 0) = if c then star x else 0`. -/
theorem star_ite' (c : Prop) [Decidable c] (x : ℂ) :
    star (if c then x else 0) = if c then star x else 0 := by
  split_ifs <;> simp

end PartialTraceHelpers'

/-! ### 5a. The support of `ρ = ω_A(W)` (manuscript §9: in an eigenbasis of
`ρ`, `r = rank ρ` and `R` is a copy of the support of `ρ`) -/

section Support

variable {D : Ports} {W : PMat D}

/-- The eigenvector unitary of `ρ` (columns = eigenbasis of `ρ`). -/
def eigU (hρ : (omegaA D W).PosSemidef) : Matrix (Fin D.m) (Fin D.m) ℂ :=
  (hρ.1.eigenvectorUnitary : Matrix (Fin D.m) (Fin D.m) ℂ)

/-- The eigenvalues `λ_i` of `ρ`. -/
def lam (hρ : (omegaA D W).PosSemidef) : Fin D.m → ℝ := hρ.1.eigenvalues

theorem lam_nonneg (hρ : (omegaA D W).PosSemidef) (i : Fin D.m) : 0 ≤ lam hρ i :=
  hρ.eigenvalues_nonneg i

theorem eigU_conjTranspose_mul (hρ : (omegaA D W).PosSemidef) : (eigU hρ)ᴴ * eigU hρ = 1 := by
  have h := Matrix.mem_unitaryGroup_iff'.1 hρ.1.eigenvectorUnitary.2
  simpa [eigU, Matrix.star_eq_conjTranspose] using h

theorem eigU_mul_conjTranspose (hρ : (omegaA D W).PosSemidef) : eigU hρ * (eigU hρ)ᴴ = 1 := by
  have h := Matrix.mem_unitaryGroup_iff.1 hρ.1.eigenvectorUnitary.2
  simpa [eigU, Matrix.star_eq_conjTranspose] using h

/-- Spectral decomposition `ρ = U diag(λ) Uᴴ`. -/
theorem omegaA_spectral (hρ : (omegaA D W).PosSemidef) :
    omegaA D W = eigU hρ * Matrix.diagonal (fun i => ((lam hρ i : ℝ) : ℂ)) * (eigU hρ)ᴴ :=
  (specMap_id hρ.1).symm

/-- `r = rank ρ = #{i | λ_i ≠ 0}`. -/
theorem rank_eq_card (hρ : (omegaA D W).PosSemidef) :
    (omegaA D W).rank = Fintype.card {i : Fin D.m // lam hρ i ≠ 0} := by
  rw [hρ.1.rank_eq_card_non_zero_eigs]
  exact Fintype.card_congr (Equiv.refl _)

/-- Enumeration of the support: `R = Fin r ≃ {i | λ_i ≠ 0}`. -/
def suppEquiv (hρ : (omegaA D W).PosSemidef) :
    Fin (omegaA D W).rank ≃ {i : Fin D.m // lam hρ i ≠ 0} :=
  (finCongr (rank_eq_card hρ)).trans (Fintype.equivFin _).symm

/-- The `k`-th support eigenvector index. -/
def σ (hρ : (omegaA D W).PosSemidef) (k : Fin (omegaA D W).rank) : Fin D.m := (suppEquiv hρ k).1

theorem σ_injective (hρ : (omegaA D W).PosSemidef) : Function.Injective (σ hρ) :=
  fun _ _ h => (suppEquiv hρ).injective (Subtype.ext h)

theorem lam_σ_ne_zero (hρ : (omegaA D W).PosSemidef) (k : Fin (omegaA D W).rank) :
    lam hρ (σ hρ k) ≠ 0 :=
  (suppEquiv hρ k).2

theorem lam_σ_pos (hρ : (omegaA D W).PosSemidef) (k : Fin (omegaA D W).rank) :
    0 < lam hρ (σ hρ k) :=
  lt_of_le_of_ne (lam_nonneg hρ _) (Ne.symm (lam_σ_ne_zero hρ k))

theorem exists_σ_eq (hρ : (omegaA D W).PosSemidef) {i : Fin D.m} (hi : lam hρ i ≠ 0) :
    ∃ k, σ hρ k = i :=
  ⟨(suppEquiv hρ).symm ⟨i, hi⟩, by simp [σ]⟩

/-- The selection matrix `Pσ : ℂ^r → ℂ^m`, `Pσ e_k = e_{σ k}`. -/
def Pσ (hρ : (omegaA D W).PosSemidef) : Matrix (Fin D.m) (Fin (omegaA D W).rank) ℂ :=
  (1 : Matrix (Fin D.m) (Fin D.m) ℂ).submatrix id (σ hρ)

theorem Pσ_apply (hρ : (omegaA D W).PosSemidef) (i : Fin D.m) (k : Fin (omegaA D W).rank) :
    Pσ hρ i k = if i = σ hρ k then 1 else 0 := by
  simp [Pσ, Matrix.submatrix_apply, Matrix.one_apply]

/-- `Pσᴴ diag(d) Pσ = diag(d ∘ σ)`: restriction of a diagonal matrix to the support. -/
theorem Pσ_conj_diag (hρ : (omegaA D W).PosSemidef) (d : Fin D.m → ℂ) :
    (Pσ hρ)ᴴ * Matrix.diagonal d * Pσ hρ = Matrix.diagonal (fun k => d (σ hρ k)) := by
  ext k k'
  rw [Matrix.mul_apply]
  simp only [Matrix.mul_diagonal, Matrix.conjTranspose_apply, Pσ_apply, Matrix.diagonal_apply]
  rw [Finset.sum_eq_single (σ hρ k)]
  · simp only [if_true, star_one, one_mul, (σ_injective hρ).eq_iff]
    by_cases h : k = k'
    · subst h; simp
    · simp [h]
  · intro j _ hj
    simp [hj]
  · intro h
    exact absurd (Finset.mem_univ _) h

theorem Pσ_conjTranspose_mul (hρ : (omegaA D W).PosSemidef) : (Pσ hρ)ᴴ * Pσ hρ = 1 := by
  have h := Pσ_conj_diag hρ (fun _ => (1 : ℂ))
  rwa [Matrix.diagonal_one, Matrix.mul_one, Matrix.diagonal_one] at h

/-- `Pσ diag(g ∘ σ) Pσᴴ = diag(g · 1_{supp})`. -/
theorem Pσ_diag (hρ : (omegaA D W).PosSemidef) (g : Fin D.m → ℂ) :
    Pσ hρ * Matrix.diagonal (fun k => g (σ hρ k)) * (Pσ hρ)ᴴ =
      Matrix.diagonal (fun i => if lam hρ i ≠ 0 then g i else 0) := by
  ext i j
  rw [Matrix.mul_apply]
  simp only [Matrix.mul_diagonal, Matrix.conjTranspose_apply, Pσ_apply, Matrix.diagonal_apply]
  by_cases hi : lam hρ i ≠ 0
  · obtain ⟨k₀, hk₀⟩ := exists_σ_eq hρ hi
    rw [Finset.sum_eq_single k₀]
    · rw [if_pos hk₀.symm, hk₀]
      by_cases hij : i = j
      · subst hij
        simp [hi]
      · have hj : ¬ j = i := fun h => hij h.symm
        simp [hj, hij]
    · intro k _ hk
      have : ¬ i = σ hρ k := fun h => hk (σ_injective hρ (hk₀.trans h)).symm
      simp [this]
    · intro h
      exact absurd (Finset.mem_univ _) h
  · have hz : ∀ k, ¬ i = σ hρ k := fun k h => hi (by rw [h]; exact lam_σ_ne_zero hρ k)
    simp [hz, hi]

/-- The support isometry `suppIso : ℂ^r → ℂ^m` whose columns are the eigenvectors of the
positive eigenvalues ("identify that support with `R`"). -/
def suppIso (hρ : (omegaA D W).PosSemidef) : Matrix (Fin D.m) (Fin (omegaA D W).rank) ℂ :=
  eigU hρ * Pσ hρ

theorem suppIso_isometry (hρ : (omegaA D W).PosSemidef) : (suppIso hρ)ᴴ * suppIso hρ = 1 := by
  rw [suppIso, Matrix.conjTranspose_mul, Matrix.mul_assoc, ← Matrix.mul_assoc (eigU hρ)ᴴ,
    eigU_conjTranspose_mul, Matrix.one_mul, Pσ_conjTranspose_mul]

/-- `suppIso suppIsoᴴ = Π_ρ`, the support projector. -/
theorem suppIso_mul_conjTranspose (hρ : (omegaA D W).PosSemidef) :
    suppIso hρ * (suppIso hρ)ᴴ = suppProj hρ := by
  have h := Pσ_diag hρ (fun _ => (1 : ℂ))
  rw [Matrix.diagonal_one, Matrix.mul_one] at h
  have hdiag : (fun i => if lam hρ i ≠ 0 then (1 : ℂ) else 0) =
      (fun i => (((fun x : ℝ => if x = 0 then (0 : ℝ) else 1) (hρ.1.eigenvalues i) : ℝ) : ℂ)) := by
    funext i
    by_cases hi : hρ.1.eigenvalues i = 0 <;> simp [lam, hi]
  calc suppIso hρ * (suppIso hρ)ᴴ = eigU hρ * (Pσ hρ * (Pσ hρ)ᴴ) * (eigU hρ)ᴴ := by
        rw [suppIso, Matrix.conjTranspose_mul]
        simp only [Matrix.mul_assoc]
    _ = suppProj hρ := by
        rw [h, hdiag, suppProj, specMap, eigU]

/-- `ρ_R = suppIsoᴴ ρ suppIso = diag(λ_{σ k})`, invertible on `R`. -/
theorem rhoR_eq (hρ : (omegaA D W).PosSemidef) :
    (suppIso hρ)ᴴ * omegaA D W * suppIso hρ =
      Matrix.diagonal (fun k => ((lam hρ (σ hρ k) : ℝ) : ℂ)) := by
  have hs := omegaA_spectral hρ
  calc (suppIso hρ)ᴴ * omegaA D W * suppIso hρ
      = (suppIso hρ)ᴴ * (eigU hρ * Matrix.diagonal (fun i => ((lam hρ i : ℝ) : ℂ)) * (eigU hρ)ᴴ) *
          suppIso hρ := by rw [← hs]
    _ = (Pσ hρ)ᴴ * ((eigU hρ)ᴴ * eigU hρ) * Matrix.diagonal (fun i => ((lam hρ i : ℝ) : ℂ)) *
          ((eigU hρ)ᴴ * eigU hρ) * Pσ hρ := by
        rw [suppIso, Matrix.conjTranspose_mul]
        simp only [Matrix.mul_assoc]
    _ = (Pσ hρ)ᴴ * Matrix.diagonal (fun i => ((lam hρ i : ℝ) : ℂ)) * Pσ hρ := by
        rw [eigU_conjTranspose_mul, Matrix.mul_one, Matrix.mul_one]
    _ = Matrix.diagonal (fun k => ((lam hρ (σ hρ k) : ℝ) : ℂ)) := Pσ_conj_diag hρ _

/-- `ρ_R^{1/2} = diag(√λ_{σ k})`. -/
def rhoRsqrt (hρ : (omegaA D W).PosSemidef) : Matrix (Fin (omegaA D W).rank) (Fin (omegaA D W).rank) ℂ :=
  Matrix.diagonal (fun k => ((Real.sqrt (lam hρ (σ hρ k)) : ℝ) : ℂ))

/-- `ρ_R^{-1/2} = diag((√λ_{σ k})⁻¹)`, a genuine inverse on the support ("No inverse on `ker ρ`
has been taken"). -/
def rhoRinvSqrt (hρ : (omegaA D W).PosSemidef) :
    Matrix (Fin (omegaA D W).rank) (Fin (omegaA D W).rank) ℂ :=
  Matrix.diagonal (fun k => (((Real.sqrt (lam hρ (σ hρ k)))⁻¹ : ℝ) : ℂ))

theorem sqrt_lam_ne_zero (hρ : (omegaA D W).PosSemidef) (k : Fin (omegaA D W).rank) :
    Real.sqrt (lam hρ (σ hρ k)) ≠ 0 :=
  Real.sqrt_ne_zero'.2 (lam_σ_pos hρ k)

theorem rhoRsqrt_mul_rhoRinvSqrt (hρ : (omegaA D W).PosSemidef) :
    rhoRsqrt hρ * rhoRinvSqrt hρ = 1 := by
  rw [rhoRsqrt, rhoRinvSqrt, Matrix.diagonal_mul_diagonal]
  convert Matrix.diagonal_one using 2
  funext k
  rw [← Complex.ofReal_mul, mul_inv_cancel₀ (sqrt_lam_ne_zero hρ k), Complex.ofReal_one]

theorem rhoRinvSqrt_mul_rhoRsqrt (hρ : (omegaA D W).PosSemidef) :
    rhoRinvSqrt hρ * rhoRsqrt hρ = 1 := by
  rw [rhoRsqrt, rhoRinvSqrt, Matrix.diagonal_mul_diagonal]
  convert Matrix.diagonal_one using 2
  funext k
  rw [← Complex.ofReal_mul, inv_mul_cancel₀ (sqrt_lam_ne_zero hρ k), Complex.ofReal_one]

theorem rhoRsqrt_mul_self (hρ : (omegaA D W).PosSemidef) :
    rhoRsqrt hρ * rhoRsqrt hρ = Matrix.diagonal (fun k => ((lam hρ (σ hρ k) : ℝ) : ℂ)) := by
  rw [rhoRsqrt, Matrix.diagonal_mul_diagonal]
  congr 1
  funext k
  rw [← Complex.ofReal_mul, Real.mul_self_sqrt (lam_nonneg hρ _)]

theorem rhoRinvSqrt_mul_rhoR_mul (hρ : (omegaA D W).PosSemidef) :
    rhoRinvSqrt hρ * Matrix.diagonal (fun k => ((lam hρ (σ hρ k) : ℝ) : ℂ)) * rhoRinvSqrt hρ = 1 := by
  rw [← rhoRsqrt_mul_self, ← Matrix.mul_assoc, rhoRinvSqrt_mul_rhoRsqrt, Matrix.one_mul,
    rhoRsqrt_mul_rhoRinvSqrt]

theorem rhoRsqrt_conjTranspose (hρ : (omegaA D W).PosSemidef) : (rhoRsqrt hρ)ᴴ = rhoRsqrt hρ := by
  rw [rhoRsqrt, Matrix.diagonal_conjTranspose]
  congr 1
  funext k
  simp

theorem rhoRinvSqrt_conjTranspose (hρ : (omegaA D W).PosSemidef) :
    (rhoRinvSqrt hρ)ᴴ = rhoRinvSqrt hρ := by
  rw [rhoRinvSqrt, Matrix.diagonal_conjTranspose]
  congr 1
  funext k
  simp

/-- The preparation amplitudes `ψ_ρ = ∑_{i<r} √λ_i |u_i⟩^{A_I} |i⟩^R`, as the matrix
`suppIso ρ_R^{1/2} : ℂ^r → ℂ^m` (manuscript equation before `eq:ordered-channel`). -/
def psiR (hρ : (omegaA D W).PosSemidef) : Matrix (Fin D.m) (Fin (omegaA D W).rank) ℂ :=
  suppIso hρ * rhoRsqrt hρ

/-- The reduced state of `|ψ_ρ⟩` on `A_I` is `ρ`. -/
theorem psiR_mul_conjTranspose (hρ : (omegaA D W).PosSemidef) :
    psiR hρ * (psiR hρ)ᴴ = omegaA D W := by
  have hd : Matrix.diagonal (fun i => if lam hρ i ≠ 0 then ((lam hρ i : ℝ) : ℂ) else 0) =
      Matrix.diagonal (fun i => ((lam hρ i : ℝ) : ℂ)) := by
    congr 1
    funext i
    by_cases hi : lam hρ i = 0 <;> simp [hi]
  have h1 : psiR hρ * (psiR hρ)ᴴ =
      eigU hρ * (Pσ hρ * Matrix.diagonal (fun k => ((lam hρ (σ hρ k) : ℝ) : ℂ)) * (Pσ hρ)ᴴ) *
        (eigU hρ)ᴴ := by
    rw [psiR, suppIso, Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, rhoRsqrt_conjTranspose]
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc (rhoRsqrt hρ) (rhoRsqrt hρ), rhoRsqrt_mul_self]
  rw [h1, Pσ_diag hρ (fun i => ((lam hρ i : ℝ) : ℂ)), hd, ← omegaA_spectral hρ]

end Support

/-! ### 5b. The completed channel, its Kraus isometry, and the two unitaries (manuscript §9) -/

section OrderedData

variable {D : Ports} {W : PMat D}

theorem omegaA_posSemidef (hW : W.PosSemidef) : (omegaA D W).PosSemidef := by
  unfold omegaA
  refine Matrix.PosSemidef.smul ?_ ?_
  · rw [Matrix.reindex_apply]
    exact ptraceOut_posSemidef (hW.submatrix _)
  · have h : (0 : ℝ) ≤ ((D.d * D.e : ℕ) : ℝ)⁻¹ := by positivity
    simpa using Complex.zero_le_real.2 h

/-- `Tr ρ = Tr W /(de) = 1` (`eq:ordered-W`). -/
theorem trace_omegaA (hW : Valid D W) : (omegaA D W).trace = 1 := by
  unfold omegaA
  rw [Matrix.trace_smul, trace_ptraceOut, Matrix.reindex_apply, trace_submatrix_equiv', hW.2.2,
    smul_eq_mul]
  exact inv_mul_cancel₀ (Nat.cast_ne_zero.2 (Nat.mul_pos D.d_pos D.e_pos).ne')

theorem hatAB_posSemidef (hW : W.PosSemidef) : (hatAB D W).PosSemidef := by
  unfold hatAB
  refine Matrix.PosSemidef.smul ?_ ?_
  · rw [Matrix.reindex_apply]
    exact ptraceOut_posSemidef (hW.submatrix _)
  · have h : (0 : ℝ) ≤ ((D.e : ℕ) : ℝ)⁻¹ := by positivity
    simp

/-- `r ≥ 1`: a unit-trace positive matrix is nonzero. -/
theorem rank_pos (hW : Valid D W) : 0 < (omegaA D W).rank := by
  have hρ := omegaA_posSemidef hW.2.1
  rw [rank_eq_card hρ, Fintype.card_pos_iff]
  by_contra hne
  rw [not_nonempty_iff] at hne
  have hall : ∀ i, lam hρ i = 0 := fun i => by
    by_contra h
    exact hne.elim ⟨i, h⟩
  have htr := trace_omegaA hW
  rw [hρ.1.trace_eq_sum_eigenvalues] at htr
  simp only [lam] at hall
  simp [hall] at htr

/-- The support-side congruence `Q = (suppIso ρ_R^{-1/2}) ⊗ I_{A_O} ⊗ I_{B_I}`. -/
def Qmat (hρ : (omegaA D W).PosSemidef) :
    Matrix ((Fin D.m × Fin D.d) × Fin D.n) ((Fin (omegaA D W).rank × Fin D.d) × Fin D.n) ℂ :=
  ((suppIso hρ * rhoRinvSqrt hρ) ⊗ₖ (1 : Op (Fin D.d))) ⊗ₖ (1 : Op (Fin D.n))

/-- The channel Choi matrix `J_C = (ρ^{-1/2} ⊗ I_{A_O B_I}) Ŵ (ρ^{-1/2} ⊗ I_{A_O B_I})` on the support
`R` (`eq:ordered-channel`), realized as `Qᴴ Ŵ Q` on `(R × A_O) × B_I`. -/
def choiC (hW : W.PosSemidef) : Op ((Fin (omegaA D W).rank × Fin D.d) × Fin D.n) :=
  (Qmat (omegaA_posSemidef hW))ᴴ * hatAB D W * Qmat (omegaA_posSemidef hW)

/-- "It is positive". -/
theorem choiC_posSemidef (hW : W.PosSemidef) : (choiC hW).PosSemidef :=
  (hatAB_posSemidef hW).conjTranspose_mul_mul_same _

theorem Qmat_conjTranspose (hρ : (omegaA D W).PosSemidef) :
    (Qmat hρ)ᴴ = ((suppIso hρ * rhoRinvSqrt hρ)ᴴ ⊗ₖ (1 : Op (Fin D.d))) ⊗ₖ (1 : Op (Fin D.n)) := by
  rw [Qmat, conjTranspose_kronecker', conjTranspose_kronecker', Matrix.conjTranspose_one,
    Matrix.conjTranspose_one]

/-- "`Tr_{B_I} J_C = I_R ⊗ I_{A_O}`" (`eq:ordered-channel`), exactly. -/
theorem ptraceOut_choiC (hW : Valid D W) (hord : OrderedAB D W) : ptraceOut (choiC hW.2.1) = 1 := by
  have hρ := omegaA_posSemidef hW.2.1
  set X := suppIso hρ * rhoRinvSqrt hρ with hX
  have hQ : (Qmat hρ)ᴴ = ((X ⊗ₖ (1 : Op (Fin D.d)))ᴴ) ⊗ₖ (1 : Op (Fin D.n)) := by
    rw [Qmat, conjTranspose_kronecker', Matrix.conjTranspose_one]
  have hmid : (suppIso hρ)ᴴ * (omegaA D W * (suppIso hρ * rhoRinvSqrt hρ)) =
      Matrix.diagonal (fun k => ((lam hρ (σ hρ k) : ℝ) : ℂ)) * rhoRinvSqrt hρ := by
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, rhoR_eq]
  rw [choiC, hQ, Qmat, ptraceOut_conj_kron_one, ordered_marginal D hord, conjTranspose_kronecker',
    Matrix.conjTranspose_one, ← Matrix.mul_kronecker_mul, ← Matrix.mul_kronecker_mul,
    Matrix.one_mul, Matrix.one_mul, hX, Matrix.conjTranspose_mul, rhoRinvSqrt_conjTranspose]
  simp only [Matrix.mul_assoc]
  rw [hmid, ← Matrix.mul_assoc, rhoRinvSqrt_mul_rhoR_mul, Matrix.one_kronecker_one]

/-- `Ψ = ψ_ρ ⊗ I_{A_O} ⊗ I_{B_I}`. -/
def Psimat (hρ : (omegaA D W).PosSemidef) :
    Matrix ((Fin D.m × Fin D.d) × Fin D.n) ((Fin (omegaA D W).rank × Fin D.d) × Fin D.n) ℂ :=
  (psiR hρ ⊗ₖ (1 : Op (Fin D.d))) ⊗ₖ (1 : Op (Fin D.n))

/-- "Preparation of `|ψ_ρ⟩` followed by `C` produces `Ŵ`": `Ψ J_C Ψᴴ = Ŵ` (support annihilation). -/
theorem psi_choiC_psi (hW : Valid D W) (hord : OrderedAB D W) :
    Psimat (omegaA_posSemidef hW.2.1) * choiC hW.2.1 * (Psimat (omegaA_posSemidef hW.2.1))ᴴ =
      hatAB D W := by
  have hρ := omegaA_posSemidef hW.2.1
  have hŴ := hatAB_posSemidef hW.2.1
  set K : Op ((Fin D.m × Fin D.d) × Fin D.n) :=
    (suppProj hρ ⊗ₖ (1 : Op (Fin D.d))) ⊗ₖ (1 : Op (Fin D.n)) with hK
  -- support annihilation: `K Ŵ = Ŵ = Ŵ K`
  have hann : hatAB D W * (((1 - suppProj hρ) ⊗ₖ (1 : Op (Fin D.d))) ⊗ₖ (1 : Op (Fin D.n))) = 0 := by
    refine psd_mul_kron_eq_zero hŴ (ordered_marginal D hord) ?_
    rw [← Matrix.mul_kronecker_mul, self_mul_one_sub_suppProj, Matrix.one_mul,
      Matrix.zero_kronecker]
  have hKdef : ((1 - suppProj hρ) ⊗ₖ (1 : Op (Fin D.d))) ⊗ₖ (1 : Op (Fin D.n)) = 1 - K := by
    rw [hK, sub_kronecker', sub_kronecker', Matrix.one_kronecker_one, Matrix.one_kronecker_one]
  have hKH : Kᴴ = K := by
    rw [hK, conjTranspose_kronecker', conjTranspose_kronecker', (suppProj_isHermitian _).eq,
      Matrix.conjTranspose_one, Matrix.conjTranspose_one]
  have hright : hatAB D W * K = hatAB D W := by
    rw [hKdef, Matrix.mul_sub, Matrix.mul_one] at hann
    exact (sub_eq_zero.1 hann).symm
  have hleft : K * hatAB D W = hatAB D W := by
    have h := congrArg Matrix.conjTranspose hright
    rwa [Matrix.conjTranspose_mul, hKH, hŴ.1.eq] at h
  -- the two congruence factors collapse to `K`
  have e1 : Psimat hρ * (Qmat hρ)ᴴ = K := by
    rw [Psimat, Qmat_conjTranspose, ← Matrix.mul_kronecker_mul, ← Matrix.mul_kronecker_mul,
      Matrix.one_mul, Matrix.one_mul, hK, psiR, Matrix.conjTranspose_mul,
      rhoRinvSqrt_conjTranspose, Matrix.mul_assoc, ← Matrix.mul_assoc (rhoRsqrt hρ),
      rhoRsqrt_mul_rhoRinvSqrt, Matrix.one_mul, suppIso_mul_conjTranspose]
  have e2 : Qmat hρ * (Psimat hρ)ᴴ = K := by
    rw [Psimat, conjTranspose_kronecker', conjTranspose_kronecker', Matrix.conjTranspose_one,
      Matrix.conjTranspose_one, Qmat, ← Matrix.mul_kronecker_mul, ← Matrix.mul_kronecker_mul,
      Matrix.one_mul, Matrix.one_mul, hK, psiR, Matrix.conjTranspose_mul,
      rhoRsqrt_conjTranspose, Matrix.mul_assoc, ← Matrix.mul_assoc (rhoRinvSqrt hρ),
      rhoRinvSqrt_mul_rhoRsqrt, Matrix.one_mul, suppIso_mul_conjTranspose]
  calc Psimat hρ * choiC hW.2.1 * (Psimat hρ)ᴴ
      = (Psimat hρ * (Qmat hρ)ᴴ) * hatAB D W * (Qmat hρ * (Psimat hρ)ᴴ) := by
        simp only [choiC, Matrix.mul_assoc]
    _ = hatAB D W := by rw [e1, e2, hleft, hright]

/-- `Ŵ` entrywise from `Ψ J_C Ψᴴ = Ŵ`. -/
theorem hatAB_entry (hW : Valid D W) (hord : OrderedAB D W) (aI aI' : Fin D.m) (aO aO' : Fin D.d)
    (bI bI' : Fin D.n) :
    hatAB D W ((aI, aO), bI) ((aI', aO'), bI') =
      ∑ r, ∑ r', psiR (omegaA_posSemidef hW.2.1) aI r * star (psiR (omegaA_posSemidef hW.2.1) aI' r') *
        choiC hW.2.1 ((r, aO), bI) ((r', aO'), bI') := by
  rw [← psi_choiC_psi hW hord, Psimat, conjTranspose_kronecker', conjTranspose_kronecker',
    Matrix.conjTranspose_one, Matrix.conjTranspose_one]
  simp only [Matrix.mul_apply, Matrix.kroneckerMap_apply, Matrix.one_apply,
    Matrix.conjTranspose_apply, mul_ite, mul_one, mul_zero, ite_mul, zero_mul, Finset.sum_mul]
  simp only [sum_ite_snd, sum_ite_snd']
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun r _ => Finset.sum_congr rfl fun r' _ => ?_
  ring

/-! Kraus factorization with the Choi index: `J_C = ∑_{h=1}^{q} |K_h⟩⟩⟨⟨K_h|` where the Kraus index
ranges over the Choi index `(R × A_O) × B_I`, so `q = r·d·n`. -/

/-- Gram factor `J_C = B Bᴴ`. -/
def krausB (hW : W.PosSemidef) :
    Matrix ((Fin (omegaA D W).rank × Fin D.d) × Fin D.n) ((Fin (omegaA D W).rank × Fin D.d) × Fin D.n) ℂ :=
  Classical.choose (psd_eq_mul_conjTranspose (choiC_posSemidef hW))

theorem krausB_spec (hW : W.PosSemidef) : choiC hW = krausB hW * (krausB hW)ᴴ :=
  Classical.choose_spec (psd_eq_mul_conjTranspose (choiC_posSemidef hW))

/-- The Stinespring isometry `V_C = ∑_h K_h ⊗ |h⟩ : R A_O → B_I ⊗ ℂ^q`. -/
def VC (hW : W.PosSemidef) :
    Matrix (Fin D.n × ((Fin (omegaA D W).rank × Fin D.d) × Fin D.n)) (Fin (omegaA D W).rank × Fin D.d) ℂ :=
  Matrix.of fun x y => krausB hW ((y.1, y.2), x.1) x.2

theorem VC_choi (hW : W.PosSemidef) (bI bI' : Fin D.n) (r r' : Fin (omegaA D W).rank)
    (aO aO' : Fin D.d) :
    ∑ h, VC hW (bI, h) (r, aO) * star (VC hW (bI', h) (r', aO')) =
      choiC hW ((r, aO), bI) ((r', aO'), bI') := by
  have h := congrFun (congrFun (krausB_spec hW) ((r, aO), bI)) ((r', aO'), bI')
  rw [Matrix.mul_apply] at h
  simp only [Matrix.conjTranspose_apply] at h
  rw [h]
  rfl

/-- Environments of the manuscript: `E_0` with `dim E_0 = n t`, `E_1` with `dim E_1 = r d t`. -/
abbrev E0t (D : Ports) (t : ℕ) : Type := Fin D.n × Fin t

abbrev E1t (D : Ports) (r t : ℕ) : Type := (Fin r × Fin D.d) × Fin t

/-- "Pad the range environment of `V_C` into `E_1`": the injection of the Choi index `ℂ^q`
(`q = r d n`) into `E_1` (`r d t ≥ q` since `t ≥ n`). -/
def padE {r t : ℕ} (ht : D.n ≤ t) (h : (Fin r × Fin D.d) × Fin D.n) : E1t D r t :=
  (h.1, Fin.castLE ht h.2)

theorem padE_injective {r t : ℕ} (ht : D.n ≤ t) : Function.Injective (padE (D := D) (r := r) ht) := by
  rintro ⟨u, bI⟩ ⟨u', bI'⟩ h
  simp only [padE, Prod.mk.injEq] at h
  exact Prod.ext h.1 (Fin.castLE_injective ht h.2)

/-- The padded isometry `V_C : R A_O → B_I E_1` (zero on the padding). -/
def VCpad (hW : W.PosSemidef) {t : ℕ} (ht : D.n ≤ t) :
    Matrix (Fin D.n × E1t D (omegaA D W).rank t) (Fin (omegaA D W).rank × Fin D.d) ℂ :=
  Matrix.of fun x y => ∑ h₀, if padE ht h₀ = x.2 then VC hW (x.1, h₀) y else 0

/-- Padding by zeros preserves the Gram identity. -/
theorem VCpad_choi (hW : W.PosSemidef) {t : ℕ} (ht : D.n ≤ t) (bI bI' : Fin D.n)
    (r r' : Fin (omegaA D W).rank) (aO aO' : Fin D.d) :
    ∑ h : E1t D (omegaA D W).rank t, VCpad hW ht (bI, h) (r, aO) * star (VCpad hW ht (bI', h) (r', aO')) =
      choiC hW ((r, aO), bI) ((r', aO'), bI') := by
  rw [← VC_choi hW bI bI' r r' aO aO']
  have hinner : ∀ h₀ h₁ : (Fin (omegaA D W).rank × Fin D.d) × Fin D.n,
      (∑ h : E1t D (omegaA D W).rank t,
        (if padE ht h₀ = h then VC hW (bI, h₀) (r, aO) else 0) *
          (if padE ht h₁ = h then star (VC hW (bI', h₁) (r', aO')) else 0)) =
      if h₀ = h₁ then VC hW (bI, h₀) (r, aO) * star (VC hW (bI', h₁) (r', aO')) else 0 := by
    intro h₀ h₁
    rw [Finset.sum_eq_single (padE ht h₀)]
    · rw [if_pos rfl]
      simp only [(padE_injective ht).eq_iff]
      by_cases h : h₀ = h₁
      · subst h
        simp
      · simp [h, Ne.symm h]
    · intro h _ hne
      simp [Ne.symm hne]
    · intro h
      exact absurd (Finset.mem_univ _) h
  simp only [VCpad, Matrix.of_apply, star_sum, star_ite', Finset.sum_mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun h₀ _ => ?_
  rw [Finset.sum_comm]
  simp only [hinner, Finset.sum_ite_eq, Finset.mem_univ, if_true]

/-- "`∑_h K_hᴴ K_h = I_{R A_O}`, so `V_C` is an isometry" (padded form). -/
theorem VCpad_isometry (hW : Valid D W) (hord : OrderedAB D W) {t : ℕ} (ht : D.n ≤ t) :
    (VCpad hW.2.1 ht)ᴴ * VCpad hW.2.1 ht = 1 := by
  ext ⟨r, aO⟩ ⟨r', aO'⟩
  have hpt := congrFun (congrFun (ptraceOut_choiC hW hord) (r', aO')) (r, aO)
  rw [ptraceOut_apply] at hpt
  have hcol : ∀ bI : Fin D.n,
      ∑ h : E1t D (omegaA D W).rank t, star (VCpad hW.2.1 ht (bI, h) (r, aO)) * VCpad hW.2.1 ht (bI, h) (r', aO') =
        choiC hW.2.1 ((r', aO'), bI) ((r, aO), bI) := by
    intro bI
    rw [← VCpad_choi hW.2.1 ht bI bI r' r aO' aO]
    exact Finset.sum_congr rfl fun h _ => mul_comm _ _
  rw [Matrix.mul_apply]
  simp only [Matrix.conjTranspose_apply, Fintype.sum_prod_type, hcol]
  rw [hpt, Matrix.one_apply, Matrix.one_apply]
  by_cases h : (r, aO) = (r', aO')
  · simp [h]
  · simp [h, Ne.symm h]

/-- "Both spaces `R A_O E_0` and `B_I E_1` have dimension `r d n t`." -/
theorem card_BI_E1 (r t : ℕ) :
    Fintype.card (Fin D.n × E1t D r t) = Fintype.card ((Fin r × Fin D.d) × E0t D t) := by
  simp only [Fintype.card_prod, Fintype.card_fin]
  ring

/-- The distinguished `|0⟩ ∈ E_0`. -/
def e0t (t : ℕ) (ht : D.n ≤ t) : E0t D t := (⟨0, D.n_pos⟩, ⟨0, lt_of_lt_of_le D.n_pos ht⟩)

/-- The map `ξ ⊗ |0⟩^{E_0} ↦ V_C ξ` "extends to a unitary `U_1` from `R A_O E_0` to `B_I E_1`"
(manuscript §9). -/
theorem exists_U1 (hW : Valid D W) (hord : OrderedAB D W) {t : ℕ} (ht : D.n ≤ t) :
    ∃ U1 : Matrix (Fin D.n × E1t D (omegaA D W).rank t) ((Fin (omegaA D W).rank × Fin D.d) × E0t D t) ℂ,
      Biunitary U1 ∧ ∀ x y, U1 x (y, e0t t ht) = VCpad hW.2.1 ht x y :=
  exists_biunitary_extension (e0t t ht) (card_BI_E1 _ _) (VCpad hW.2.1 ht) (VCpad_isometry hW hord ht)

/-- `|ψ_ρ⟩ ⊗ |0⟩^{E_0}` as a one-column isometry (`‖ψ_ρ‖² = Tr ρ = 1`). -/
def psi0 (hW : W.PosSemidef) (t : ℕ) (ht : D.n ≤ t) :
    Matrix (Fin D.m × (Fin (omegaA D W).rank × E0t D t)) Unit ℂ :=
  Matrix.of fun x _ => psiR (omegaA_posSemidef hW) x.1 x.2.1 * (if x.2.2 = e0t t ht then 1 else 0)

theorem psi0_isometry (hW : Valid D W) (t : ℕ) (ht : D.n ≤ t) :
    (psi0 hW.2.1 t ht)ᴴ * psi0 hW.2.1 t ht = 1 := by
  have hρ := omegaA_posSemidef hW.2.1
  ext x y
  rw [Matrix.mul_apply]
  have hterm : ∀ z : Fin D.m × (Fin (omegaA D W).rank × E0t D t),
      (psi0 hW.2.1 t ht)ᴴ x z * psi0 hW.2.1 t ht z y =
        if z.2.2 = e0t t ht then psiR hρ z.1 z.2.1 * star (psiR hρ z.1 z.2.1) else 0 := by
    rintro ⟨a, r, e⟩
    simp only [psi0, Matrix.of_apply, Matrix.conjTranspose_apply]
    by_cases h : e = e0t t ht
    · subst h
      simp [mul_comm]
    · simp [h]
  simp only [hterm]
  rw [Fintype.sum_prod_type]
  have hinner : ∀ aI : Fin D.m,
      (∑ w : Fin (omegaA D W).rank × E0t D t,
        if w.2 = e0t t ht then psiR hρ aI w.1 * star (psiR hρ aI w.1) else 0) =
        ∑ r, psiR hρ aI r * star (psiR hρ aI r) := by
    intro aI
    rw [Fintype.sum_prod_type]
    exact Finset.sum_congr rfl fun r _ => by simp [Finset.sum_ite_eq']
  simp only [hinner]
  have htr : ∑ aI : Fin D.m, ∑ r, psiR hρ aI r * star (psiR hρ aI r) =
      (psiR hρ * (psiR hρ)ᴴ).trace := by
    simp only [Matrix.trace, Matrix.diag_apply, Matrix.mul_apply, Matrix.conjTranspose_apply]
  rw [htr, psiR_mul_conjTranspose, trace_omegaA hW]
  simp

/-- Past dimension: `dim P = m r n t` (stated with the `Fin (p+1)` bookkeeping of `HigherOp`). -/
theorem pDim_succ (hW : Valid D W) (t : ℕ) (ht : D.n ≤ t) :
    D.m * (omegaA D W).rank * D.n * t - 1 + 1 =
      Fintype.card (Fin D.m × (Fin (omegaA D W).rank × E0t D t)) := by
  have h1 : 0 < D.m * (omegaA D W).rank * D.n * t :=
    Nat.mul_pos (Nat.mul_pos (Nat.mul_pos D.m_pos (rank_pos hW)) D.n_pos)
      (lt_of_lt_of_le D.n_pos ht)
  rw [Nat.sub_add_cancel h1]
  simp only [Fintype.card_prod, Fintype.card_fin]
  ring

/-- Future dimension: `dim F = dim (B_O E_1) = e r d t`. -/
theorem fDim_succ (hW : Valid D W) (t : ℕ) (ht : D.n ≤ t) :
    D.e * (omegaA D W).rank * D.d * t - 1 + 1 = Fintype.card (Fin D.e × E1t D (omegaA D W).rank t) := by
  have h1 : 0 < D.e * (omegaA D W).rank * D.d * t :=
    Nat.mul_pos (Nat.mul_pos (Nat.mul_pos D.e_pos (rank_pos hW)) D.d_pos)
      (lt_of_lt_of_le D.n_pos ht)
  rw [Nat.sub_add_cancel h1]
  simp only [Fintype.card_prod, Fintype.card_fin]
  ring

/-- Coordinates of the global future `F = B_O ⊗ E_1`. -/
def eqFt (hW : Valid D W) (t : ℕ) (ht : D.n ≤ t) :
    Fin (D.e * (omegaA D W).rank * D.d * t - 1 + 1) ≃ Fin D.e × E1t D (omegaA D W).rank t :=
  Fintype.equivOfCardEq (by rw [Fintype.card_fin, fDim_succ hW t ht])

/-- `dim P = m r n t` and a unitary `U_0` from `P` to `A_I R E_0` that maps `|0⟩^P` to
`|ψ_ρ⟩^{A_I R} |0⟩^{E_0}`. -/
theorem exists_U0 (hW : Valid D W) (t : ℕ) (ht : D.n ≤ t) :
    ∃ U0 : Matrix (Fin D.m × (Fin (omegaA D W).rank × E0t D t))
        (Fin (D.m * (omegaA D W).rank * D.n * t - 1 + 1)) ℂ,
      Biunitary U0 ∧ ∀ x, U0 x 0 = psi0 hW.2.1 t ht x () := by
  have hcard : Fintype.card (Fin D.m × (Fin (omegaA D W).rank × E0t D t)) =
      Fintype.card (Unit × Fin (D.m * (omegaA D W).rank * D.n * t - 1 + 1)) := by
    rw [Fintype.card_prod Unit, Fintype.card_unit, one_mul, Fintype.card_fin, pDim_succ hW t ht]
  obtain ⟨U, hU, hcol⟩ :=
    exists_biunitary_extension (0 : Fin (D.m * (omegaA D W).rank * D.n * t - 1 + 1)) hcard
      (psi0 hW.2.1 t ht) (psi0_isometry hW t ht)
  refine ⟨Matrix.reindex (Equiv.refl _) (Equiv.punitProd _) U, Biunitary.reindex _ _ hU,
    fun x => ?_⟩
  simpa [Matrix.reindex_apply, Matrix.submatrix_apply] using hcol x ()

end OrderedData

/-! ### 6. The rank-one comb and its properties (generic in `R`, `E_0`, `E_1`, `P`, `F`)

The generic link algebra (`linkVec`, `link_rank_one`, `link_add_*`, `link_sum_*`, `choiVec`,
`kraus_of_channelChoi`, `ptraceOut_sum_choiVec`) lives in `CausalNonpurifiability.Definitions.LinkAlgebra`. -/

section Comb

variable {D : Ports} {R E0 E1 : Type} [Fintype R] [Fintype E0] [Fintype E1] [DecidableEq R]
  [DecidableEq E0] [DecidableEq E1] {p f : ℕ}

/-- The comb vector `s(p, (a_I,a_O,b_I,b_O), f)`, `f ↦ (b_O', e_1)`:
`δ_{b_O b_O'} ∑_{r e_0} U_0[(a_I,r,e_0), p] U_1[(b_I,e_1), (r,a_O,e_0)]`
(`eq:sequential-S`: `P → A_I R E_0`, Alice, `R A_O E_0 → B_I E_1`, Bob, `F = B_O E_1`). -/
def combVec (eqF : Fin (f + 1) ≃ Fin D.e × E1)
    (U0 : Matrix (Fin D.m × (R × E0)) (Fin (p + 1)) ℂ)
    (U1 : Matrix (Fin D.n × E1) ((R × Fin D.d) × E0) ℂ) :
    (Fin (p + 1) × LabIndex D) × Fin (f + 1) → ℂ :=
  fun x =>
    if x.1.2.2.2 = (eqF x.2).1 then
      ∑ r : R, ∑ e : E0,
        U0 (x.1.2.1.1, (r, e)) x.1.1 * U1 (x.1.2.2.1, (eqF x.2).2) ((r, x.1.2.1.2), e)
    else 0

/-- The higher-order operator of the comb: `S = |s⟩⟨s|`. -/
def combOp (eqF : Fin (f + 1) ≃ Fin D.e × E1)
    (U0 : Matrix (Fin D.m × (R × E0)) (Fin (p + 1)) ℂ)
    (U1 : Matrix (Fin D.n × E1) ((R × Fin D.d) × E0) ℂ) : HigherOp D p f :=
  Matrix.vecMulVec (combVec eqF U0 U1) (star (combVec eqF U0 U1))

theorem combOp_posSemidef (eqF : Fin (f + 1) ≃ Fin D.e × E1)
    (U0 : Matrix (Fin D.m × (R × E0)) (Fin (p + 1)) ℂ)
    (U1 : Matrix (Fin D.n × E1) ((R × Fin D.d) × E0) ℂ) : (combOp eqF U0 U1).PosSemidef :=
  posSemidef_vecMulVec_star _

/-- `∑ₖ (reindex e id (Xₖ ⊗ I))ᴴ (reindex e id (Xₖ ⊗ I)) = 1` when `∑ₖ Xₖᴴ Xₖ = 1`. -/
theorem sum_conj_mul_layer {ι α β γ β' : Type} [Fintype ι] [Fintype α] [Fintype β] [Fintype γ]
    [Fintype β'] [DecidableEq α] [DecidableEq β] [DecidableEq γ] [DecidableEq β']
    (e : β × γ ≃ β') (X : ι → Matrix β α ℂ) (hX : ∑ k, (X k)ᴴ * X k = 1) :
    ∑ k, (Matrix.reindex e (Equiv.refl (α × γ)) (X k ⊗ₖ (1 : Op γ)))ᴴ *
        Matrix.reindex e (Equiv.refl (α × γ)) (X k ⊗ₖ (1 : Op γ)) = 1 := by
  have h1 : ∀ k, (Matrix.reindex e (Equiv.refl (α × γ)) (X k ⊗ₖ (1 : Op γ)))ᴴ *
      Matrix.reindex e (Equiv.refl (α × γ)) (X k ⊗ₖ (1 : Op γ)) =
        ((X k)ᴴ * X k) ⊗ₖ (1 : Op γ) := by
    intro k
    simp only [Matrix.reindex_apply, Matrix.conjTranspose_submatrix, Matrix.submatrix_mul_equiv,
      Equiv.refl_symm, Equiv.coe_refl, Matrix.submatrix_id_id]
    rw [conjTranspose_kronecker', ← Matrix.mul_kronecker_mul, Matrix.conjTranspose_one,
      Matrix.one_mul]
  simp only [h1]
  rw [sum_kronecker_one, hX, Matrix.one_kronecker_one]

/-- `∑ₖ ∑ₕ (Mₕ Pₖ)ᴴ (Mₕ Pₖ) = ∑ₖ Pₖᴴ (∑ₕ Mₕᴴ Mₕ) Pₖ`. -/
theorem sum_conj_mul_mul {ι κ α β γ : Type} [Fintype ι] [Fintype κ] [Fintype α] [Fintype β]
    [Fintype γ] (M : κ → Matrix γ β ℂ) (P : ι → Matrix β α ℂ) :
    ∑ k, ∑ h, (M h * P k)ᴴ * (M h * P k) = ∑ k, (P k)ᴴ * (∑ h, (M h)ᴴ * M h) * P k := by
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Matrix.mul_sum, Matrix.sum_mul]
  refine Finset.sum_congr rfl fun h _ => ?_
  rw [Matrix.conjTranspose_mul]
  simp only [Matrix.mul_assoc]

section Layers

variable {a a' b b' : ℕ}

/-- Regrouping after `U_0 ⊗ 1`: `((a_I,(r,e_0)),(e_A,e_B)) ↦ ((a_I,e_A),((r,e_0),e_B))`. -/
def eq01 (D : Ports) (R E0 : Type) (a b : ℕ) :
    (Fin D.m × (R × E0)) × (Fin (a + 1) × Fin (b + 1)) ≃
      (Fin D.m × Fin (a + 1)) × ((R × E0) × Fin (b + 1)) where
  toFun x := ((x.1.1, x.2.1), (x.1.2, x.2.2))
  invFun y := ((y.1.1, y.2.1), (y.1.2, y.2.2))
  left_inv := fun ⟨⟨_, _⟩, ⟨_, _⟩⟩ => rfl
  right_inv := fun ⟨⟨_, _⟩, ⟨_, _⟩⟩ => rfl

/-- Regrouping after `A ⊗ 1`: `((a_O,e'_A),((r,e_0),e_B)) ↦ (((r,a_O),e_0),(e'_A,e_B))`. -/
def eq12 (D : Ports) (R E0 : Type) (a' b : ℕ) :
    (Fin D.d × Fin (a' + 1)) × ((R × E0) × Fin (b + 1)) ≃
      ((R × Fin D.d) × E0) × (Fin (a' + 1) × Fin (b + 1)) where
  toFun x := (((x.2.1.1, x.1.1), x.2.1.2), (x.1.2, x.2.2))
  invFun y := ((y.1.1.2, y.2.1), ((y.1.1.1, y.1.2), y.2.2))
  left_inv := fun ⟨⟨_, _⟩, ⟨⟨_, _⟩, _⟩⟩ => rfl
  right_inv := fun ⟨⟨⟨_, _⟩, _⟩, ⟨_, _⟩⟩ => rfl

/-- Regrouping after `U_1 ⊗ 1`: `((b_I,e_1),(e'_A,e_B)) ↦ ((b_I,e_B),(e_1,e'_A))`. -/
def eq23 (D : Ports) (E1 : Type) (a' b : ℕ) :
    (Fin D.n × E1) × (Fin (a' + 1) × Fin (b + 1)) ≃
      (Fin D.n × Fin (b + 1)) × (E1 × Fin (a' + 1)) where
  toFun x := ((x.1.1, x.2.2), (x.1.2, x.2.1))
  invFun y := ((y.1.1, y.2.1), (y.2.2, y.1.2))
  left_inv := fun ⟨⟨_, _⟩, ⟨_, _⟩⟩ => rfl
  right_inv := fun ⟨⟨_, _⟩, ⟨_, _⟩⟩ => rfl

/-- Regrouping after `B ⊗ 1` into the link output `F × (E'_A × E'_B)`, `F ≃ B_O × E_1`:
`((b_O,e'_B),(e_1,e'_A)) ↦ (eqF⁻¹(b_O,e_1),(e'_A,e'_B))`. -/
def eq3out (eqF : Fin (f + 1) ≃ Fin D.e × E1) (a' b' : ℕ) :
    (Fin D.e × Fin (b' + 1)) × (E1 × Fin (a' + 1)) ≃ LinkOut f a' b' :=
  { toFun := fun x => (eqF.symm (x.1.1, x.2.1), (x.2.2, x.1.2))
    invFun := fun y => (((eqF y.1).1, y.2.2), ((eqF y.1).2, y.2.1))
    left_inv := by
      rintro ⟨⟨bO, eB'⟩, ⟨e1, eA'⟩⟩
      simp
    right_inv := by
      rintro ⟨fO, ⟨eA', eB'⟩⟩
      simp }

@[simp] theorem eq01_symm_apply (D : Ports) (R E0 : Type) (a b : ℕ)
    (y : (Fin D.m × Fin (a + 1)) × ((R × E0) × Fin (b + 1))) :
    (eq01 D R E0 a b).symm y = ((y.1.1, y.2.1), (y.1.2, y.2.2)) := rfl
@[simp] theorem eq12_symm_apply (D : Ports) (R E0 : Type) (a' b : ℕ)
    (y : ((R × Fin D.d) × E0) × (Fin (a' + 1) × Fin (b + 1))) :
    (eq12 D R E0 a' b).symm y = ((y.1.1.2, y.2.1), ((y.1.1.1, y.1.2), y.2.2)) := rfl
@[simp] theorem eq23_symm_apply (D : Ports) (E1 : Type) (a' b : ℕ)
    (y : (Fin D.n × Fin (b + 1)) × (E1 × Fin (a' + 1))) :
    (eq23 D E1 a' b).symm y = ((y.1.1, y.2.1), (y.2.2, y.1.2)) := rfl
@[simp] theorem eq3out_symm_apply (eqF : Fin (f + 1) ≃ Fin D.e × E1) (a' b' : ℕ)
    (y : LinkOut f a' b') :
    (eq3out eqF a' b').symm y = (((eqF y.1).1, y.2.2), ((eqF y.1).2, y.2.1)) := rfl

/-- The four-layer composition `T A B = (B ⊗ 1)(U_1 ⊗ 1)(A ⊗ 1)(U_0 ⊗ 1)` from `LinkIn` to
`LinkOut` (`eq:sequential-S` with Alice's and Bob's extended operations inserted). -/
def layerT (eqF : Fin (f + 1) ≃ Fin D.e × E1)
    (U0 : Matrix (Fin D.m × (R × E0)) (Fin (p + 1)) ℂ)
    (U1 : Matrix (Fin D.n × E1) ((R × Fin D.d) × E0) ℂ)
    (A : Matrix (Fin D.d × Fin (a' + 1)) (Fin D.m × Fin (a + 1)) ℂ)
    (B : Matrix (Fin D.e × Fin (b' + 1)) (Fin D.n × Fin (b + 1)) ℂ) :
    Matrix (LinkOut f a' b') (LinkIn p a b) ℂ :=
  Matrix.reindex (eq3out eqF a' b') (Equiv.refl _) (B ⊗ₖ (1 : Op (E1 × Fin (a' + 1)))) *
    Matrix.reindex (eq23 D E1 a' b) (Equiv.refl _) (U1 ⊗ₖ (1 : Op (Fin (a' + 1) × Fin (b + 1)))) *
    Matrix.reindex (eq12 D R E0 a' b) (Equiv.refl _) (A ⊗ₖ (1 : Op ((R × E0) × Fin (b + 1)))) *
    Matrix.reindex (eq01 D R E0 a b) (Equiv.refl _) (U0 ⊗ₖ (1 : Op (Fin (a + 1) × Fin (b + 1))))

variable (eqF : Fin (f + 1) ≃ Fin D.e × E1)
  (U0 : Matrix (Fin D.m × (R × E0)) (Fin (p + 1)) ℂ)
  (U1 : Matrix (Fin D.n × E1) ((R × Fin D.d) × E0) ℂ)
  (A : Matrix (Fin D.d × Fin (a' + 1)) (Fin D.m × Fin (a + 1)) ℂ)
  (B : Matrix (Fin D.e × Fin (b' + 1)) (Fin D.n × Fin (b + 1)) ℂ)

theorem layerT_biunitary {U0 : Matrix (Fin D.m × (R × E0)) (Fin (p + 1)) ℂ}
    {U1 : Matrix (Fin D.n × E1) ((R × Fin D.d) × E0) ℂ}
    {A : Matrix (Fin D.d × Fin (a' + 1)) (Fin D.m × Fin (a + 1)) ℂ}
    {B : Matrix (Fin D.e × Fin (b' + 1)) (Fin D.n × Fin (b + 1)) ℂ}
    (hU0 : Biunitary U0) (hU1 : Biunitary U1) (hA : Biunitary A) (hB : Biunitary B) :
    Biunitary (layerT eqF U0 U1 A B) := by
  unfold layerT
  exact (((hB.kronecker_one.reindex _ _).mul (hU1.kronecker_one.reindex _ _)).mul
    (hA.kronecker_one.reindex _ _)).mul (hU0.kronecker_one.reindex _ _)

/-- Kraus-sum identity: `∑_{k,h} (T A_k B_h)ᴴ (T A_k B_h) = 1` when `∑ A_kᴴ A_k = 1`,
`∑ B_hᴴ B_h = 1` (trace preservation of the linked channel). -/
theorem layerT_kraus_sum {ι κ : Type} [Fintype ι] [Fintype κ]
    {U0 : Matrix (Fin D.m × (R × E0)) (Fin (p + 1)) ℂ}
    {U1 : Matrix (Fin D.n × E1) ((R × Fin D.d) × E0) ℂ}
    (hU0 : Biunitary U0) (hU1 : Biunitary U1)
    {A : ι → Matrix (Fin D.d × Fin (a' + 1)) (Fin D.m × Fin (a + 1)) ℂ}
    {B : κ → Matrix (Fin D.e × Fin (b' + 1)) (Fin D.n × Fin (b + 1)) ℂ}
    (hA : ∑ k, (A k)ᴴ * A k = 1) (hB : ∑ h, (B h)ᴴ * B h = 1) :
    ∑ k, ∑ h, (layerT eqF U0 U1 (A k) (B h))ᴴ * layerT eqF U0 U1 (A k) (B h) = 1 := by
  set L0 := Matrix.reindex (eq01 D R E0 a b) (Equiv.refl _)
    (U0 ⊗ₖ (1 : Op (Fin (a + 1) × Fin (b + 1)))) with hL0def
  set L2 := Matrix.reindex (eq23 D E1 a' b) (Equiv.refl _)
    (U1 ⊗ₖ (1 : Op (Fin (a' + 1) × Fin (b + 1)))) with hL2def
  have hL0 : L0ᴴ * L0 = 1 := (hU0.kronecker_one.reindex _ _).1
  have hL2 : L2ᴴ * L2 = 1 := (hU1.kronecker_one.reindex _ _).1
  have hA' := sum_conj_mul_layer (eq12 D R E0 a' b) A hA
  have hB' := sum_conj_mul_layer (eq3out eqF a' b') B hB
  have hT : ∀ k h, layerT eqF U0 U1 (A k) (B h) =
      Matrix.reindex (eq3out eqF a' b') (Equiv.refl _) (B h ⊗ₖ (1 : Op (E1 × Fin (a' + 1)))) *
        (L2 * (Matrix.reindex (eq12 D R E0 a' b) (Equiv.refl _)
          (A k ⊗ₖ (1 : Op ((R × E0) × Fin (b + 1)))) * L0)) := by
    intro k h
    simp only [layerT, hL0def, hL2def, Matrix.mul_assoc]
  simp only [hT]
  rw [sum_conj_mul_mul, hB']
  simp only [Matrix.mul_one]
  have h2 : ∀ k, (L2 * (Matrix.reindex (eq12 D R E0 a' b) (Equiv.refl _)
      (A k ⊗ₖ (1 : Op ((R × E0) × Fin (b + 1)))) * L0))ᴴ *
      (L2 * (Matrix.reindex (eq12 D R E0 a' b) (Equiv.refl _)
      (A k ⊗ₖ (1 : Op ((R × E0) × Fin (b + 1)))) * L0)) =
      (Matrix.reindex (eq12 D R E0 a' b) (Equiv.refl _)
      (A k ⊗ₖ (1 : Op ((R × E0) × Fin (b + 1)))) * L0)ᴴ *
      (Matrix.reindex (eq12 D R E0 a' b) (Equiv.refl _)
      (A k ⊗ₖ (1 : Op ((R × E0) × Fin (b + 1)))) * L0) := by
    intro k
    rw [Matrix.conjTranspose_mul, Matrix.mul_assoc, ← Matrix.mul_assoc L2ᴴ, hL2, Matrix.one_mul]
  simp only [h2]
  have h3 : ∀ k, (Matrix.reindex (eq12 D R E0 a' b) (Equiv.refl _)
      (A k ⊗ₖ (1 : Op ((R × E0) × Fin (b + 1)))) * L0)ᴴ *
      (Matrix.reindex (eq12 D R E0 a' b) (Equiv.refl _)
      (A k ⊗ₖ (1 : Op ((R × E0) × Fin (b + 1)))) * L0) =
      L0ᴴ * ((Matrix.reindex (eq12 D R E0 a' b) (Equiv.refl _)
      (A k ⊗ₖ (1 : Op ((R × E0) × Fin (b + 1)))))ᴴ *
      Matrix.reindex (eq12 D R E0 a' b) (Equiv.refl _)
      (A k ⊗ₖ (1 : Op ((R × E0) × Fin (b + 1))))) * L0 := by
    intro k
    rw [Matrix.conjTranspose_mul]
    simp only [Matrix.mul_assoc]
  simp only [h3]
  rw [← Matrix.sum_mul, ← Matrix.mul_sum, hA', Matrix.mul_one, hL0]

section Stages

/-- Layer 0 entries: `U_0 ⊗ I_{E_A E_B}` after regrouping. -/
theorem L0_apply (x : (Fin D.m × Fin (a + 1)) × ((R × E0) × Fin (b + 1))) (i : LinkIn p a b) :
    Matrix.reindex (eq01 D R E0 a b) (Equiv.refl _) (U0 ⊗ₖ (1 : Op (Fin (a + 1) × Fin (b + 1)))) x i =
      U0 (x.1.1, x.2.1) i.1 * (if (x.1.2, x.2.2) = i.2 then 1 else 0) := by
  simp only [Matrix.reindex_apply, Matrix.submatrix_apply, Equiv.refl_symm, Equiv.coe_refl, id_eq,
    eq01_symm_apply, Matrix.kroneckerMap_apply, Matrix.one_apply]

/-- Layer 1 entries: `A ⊗ I` after regrouping. -/
theorem L1_apply (y : ((R × Fin D.d) × E0) × (Fin (a' + 1) × Fin (b + 1)))
    (x : (Fin D.m × Fin (a + 1)) × ((R × E0) × Fin (b + 1))) :
    Matrix.reindex (eq12 D R E0 a' b) (Equiv.refl _)
        (A ⊗ₖ (1 : Op ((R × E0) × Fin (b + 1)))) y x =
      A (y.1.1.2, y.2.1) x.1 * (if ((y.1.1.1, y.1.2), y.2.2) = x.2 then 1 else 0) := by
  simp only [Matrix.reindex_apply, Matrix.submatrix_apply, Equiv.refl_symm, Equiv.coe_refl, id_eq,
    eq12_symm_apply, Matrix.kroneckerMap_apply, Matrix.one_apply]

/-- Layer 2 entries: `U_1 ⊗ I` after regrouping. -/
theorem L2_apply (z : (Fin D.n × Fin (b + 1)) × (E1 × Fin (a' + 1)))
    (y : ((R × Fin D.d) × E0) × (Fin (a' + 1) × Fin (b + 1))) :
    Matrix.reindex (eq23 D E1 a' b) (Equiv.refl _)
        (U1 ⊗ₖ (1 : Op (Fin (a' + 1) × Fin (b + 1)))) z y =
      U1 (z.1.1, z.2.1) y.1 * (if (z.2.2, z.1.2) = y.2 then 1 else 0) := by
  simp only [Matrix.reindex_apply, Matrix.submatrix_apply, Equiv.refl_symm, Equiv.coe_refl, id_eq,
    eq23_symm_apply, Matrix.kroneckerMap_apply, Matrix.one_apply]

/-- Layer 3 entries: `B ⊗ I` into the link output. -/
theorem L3_apply (o : LinkOut f a' b') (z : (Fin D.n × Fin (b + 1)) × (E1 × Fin (a' + 1))) :
    Matrix.reindex (eq3out eqF a' b') (Equiv.refl _) (B ⊗ₖ (1 : Op (E1 × Fin (a' + 1)))) o z =
      B ((eqF o.1).1, o.2.2) z.1 * (if ((eqF o.1).2, o.2.1) = z.2 then 1 else 0) := by
  simp only [Matrix.reindex_apply, Matrix.submatrix_apply, Equiv.refl_symm, Equiv.coe_refl, id_eq,
    eq3out_symm_apply, Matrix.kroneckerMap_apply, Matrix.one_apply]

/-- Stage 1: `L₁ L₀`. -/
theorem M1_apply (y : ((R × Fin D.d) × E0) × (Fin (a' + 1) × Fin (b + 1)))
    (pI : Fin (p + 1)) (eA₀ : Fin (a + 1)) (eB₀ : Fin (b + 1)) :
    (Matrix.reindex (eq12 D R E0 a' b) (Equiv.refl _)
        (A ⊗ₖ (1 : Op ((R × E0) × Fin (b + 1)))) *
      Matrix.reindex (eq01 D R E0 a b) (Equiv.refl _)
        (U0 ⊗ₖ (1 : Op (Fin (a + 1) × Fin (b + 1))))) y (pI, (eA₀, eB₀)) =
      if y.2.2 = eB₀ then
        ∑ aI, A (y.1.1.2, y.2.1) (aI, eA₀) * U0 (aI, (y.1.1.1, y.1.2)) pI
      else 0 := by
  rw [Matrix.mul_apply, Fintype.sum_prod_type]
  simp only [L1_apply, L0_apply, mul_ite, mul_one, mul_zero, ite_mul, zero_mul]
  rw [Fintype.sum_prod_type]
  simp only [Prod.mk.injEq, ite_and, Finset.sum_ite_eq', Finset.mem_univ, if_true,
    sum_ite_ite_eq, Finset.sum_ite_irrel, Finset.sum_const_zero]

/-- Stage 2: `L₂ (L₁ L₀)`. -/
theorem M2_apply (z : (Fin D.n × Fin (b + 1)) × (E1 × Fin (a' + 1)))
    (pI : Fin (p + 1)) (eA₀ : Fin (a + 1)) (eB₀ : Fin (b + 1)) :
    (Matrix.reindex (eq23 D E1 a' b) (Equiv.refl _)
        (U1 ⊗ₖ (1 : Op (Fin (a' + 1) × Fin (b + 1)))) *
      (Matrix.reindex (eq12 D R E0 a' b) (Equiv.refl _)
        (A ⊗ₖ (1 : Op ((R × E0) × Fin (b + 1)))) *
      Matrix.reindex (eq01 D R E0 a b) (Equiv.refl _)
        (U0 ⊗ₖ (1 : Op (Fin (a + 1) × Fin (b + 1)))))) z (pI, (eA₀, eB₀)) =
      if z.1.2 = eB₀ then
        ∑ w : (R × Fin D.d) × E0, U1 (z.1.1, z.2.1) w *
          ∑ aI, A (w.1.2, z.2.2) (aI, eA₀) * U0 (aI, (w.1.1, w.2)) pI
      else 0 := by
  rw [Matrix.mul_apply, Fintype.sum_prod_type]
  simp only [L2_apply, M1_apply, mul_ite, mul_one, mul_zero, ite_mul, zero_mul, sum_ite_ite_eq,
    Finset.sum_ite_irrel, Finset.sum_const_zero]

/-- Stage 3: the full composition `T = L₃ (L₂ (L₁ L₀))`, all identity deltas removed. -/
theorem T_apply (fO : Fin (f + 1)) (eA₁ : Fin (a' + 1)) (eB₁ : Fin (b' + 1))
    (pI : Fin (p + 1)) (eA₀ : Fin (a + 1)) (eB₀ : Fin (b + 1)) :
    layerT eqF U0 U1 A B (fO, (eA₁, eB₁)) (pI, (eA₀, eB₀)) =
      ∑ bI, B ((eqF fO).1, eB₁) (bI, eB₀) *
        ∑ w : (R × Fin D.d) × E0, U1 (bI, (eqF fO).2) w *
          ∑ aI, A (w.1.2, eA₁) (aI, eA₀) * U0 (aI, (w.1.1, w.2)) pI := by
  unfold layerT
  simp only [Matrix.mul_assoc]
  rw [Matrix.mul_apply, Fintype.sum_prod_type]
  simp only [L3_apply, M2_apply, mul_ite, mul_one, mul_zero, ite_mul, zero_mul,
    Finset.sum_ite_irrel, Finset.sum_const_zero, Finset.sum_ite_eq, Finset.mem_univ, if_true]
  rw [Fintype.sum_prod_type]
  simp only [Finset.sum_ite_eq', Finset.mem_univ, if_true]

/-- The linked Choi vector of the comb with rank-one local vectors, as an explicit nested sum. -/
theorem linkVec_comb (fO : Fin (f + 1)) (eA₁ : Fin (a' + 1)) (eB₁ : Fin (b' + 1))
    (pI : Fin (p + 1)) (eA₀ : Fin (a + 1)) (eB₀ : Fin (b + 1)) :
    linkVec (combVec eqF U0 U1) (choiVec A) (choiVec B) ((pI, (eA₀, eB₀)), (fO, (eA₁, eB₁))) =
      ∑ aI, ∑ aO, ∑ bI,
        (∑ r : R, ∑ e : E0, U0 (aI, (r, e)) pI * U1 (bI, (eqF fO).2) ((r, aO), e)) *
          A (aO, eA₁) (aI, eA₀) * B ((eqF fO).1, eB₁) (bI, eB₀) := by
  simp only [linkVec, combVec, choiVec, ite_mul, zero_mul]
  rw [Fintype.sum_prod_type]
  simp only [sum_ite_snd]
  rw [Fintype.sum_prod_type]

end Stages

/-- **Matching lemma**: the entries of the four-layer composition are the linked Choi vector of
the comb with the rank-one local vectors (`eq:link` contraction ↔ operator composition). -/
theorem layerT_entry (i : LinkIn p a b) (o : LinkOut f a' b') :
    layerT eqF U0 U1 A B o i = linkVec (combVec eqF U0 U1) (choiVec A) (choiVec B) (i, o) := by
  obtain ⟨pI, eA₀, eB₀⟩ := i
  obtain ⟨fO, eA₁, eB₁⟩ := o
  rw [T_apply, linkVec_comb]
  simp only [Finset.mul_sum, Finset.sum_mul]
  rw [sum_perm5]
  refine Finset.sum_congr rfl fun bI _ => ?_
  rw [Fintype.sum_prod_type, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun r _ => Finset.sum_congr rfl fun aO _ =>
    Finset.sum_congr rfl fun e _ => Finset.sum_congr rfl fun aI _ => ?_
  ring

end Layers

/-- The comb is deterministic: channels in, channel out (AFNB Definition 1). -/
theorem combOp_deterministic (eqF : Fin (f + 1) ≃ Fin D.e × E1)
    {U0 : Matrix (Fin D.m × (R × E0)) (Fin (p + 1)) ℂ}
    {U1 : Matrix (Fin D.n × E1) ((R × Fin D.d) × E0) ℂ}
    (hU0 : Biunitary U0) (hU1 : Biunitary U1) : Deterministic D (combOp eqF U0 U1) := by
  refine ⟨combOp_posSemidef eqF U0 U1, fun a a' b b' JA JB hJA hJB => ?_⟩
  obtain ⟨KA, hJAeq, hKA⟩ := kraus_of_channelChoi hJA
  obtain ⟨KB, hJBeq, hKB⟩ := kraus_of_channelChoi hJB
  have hvec : ∀ (A : Matrix (Fin D.d × Fin (a' + 1)) (Fin D.m × Fin (a + 1)) ℂ)
      (B : Matrix (Fin D.e × Fin (b' + 1)) (Fin D.n × Fin (b + 1)) ℂ),
      linkVec (combVec eqF U0 U1) (choiVec A) (choiVec B) = choiVec (layerT eqF U0 U1 A B) :=
    fun A B => funext fun u => (layerT_entry eqF U0 U1 A B u.1 u.2).symm
  have hlink : link D (combOp eqF U0 U1) JA JB =
      ∑ k, ∑ h, Matrix.vecMulVec (choiVec (layerT eqF U0 U1 (KA k) (KB h)))
        (star (choiVec (layerT eqF U0 U1 (KA k) (KB h)))) := by
    rw [hJAeq, hJBeq, link_sum_left]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [link_sum_right]
    refine Finset.sum_congr rfl fun h _ => ?_
    rw [combOp, link_rank_one, hvec]
  rw [hlink]
  refine ⟨?_, ?_⟩
  · exact Finset.sum_induction _ _ (fun _ _ h1 h2 => h1.add h2) Matrix.PosSemidef.zero
      fun k _ => Finset.sum_induction _ _ (fun _ _ h1 h2 => h1.add h2) Matrix.PosSemidef.zero
        fun h _ => posSemidef_vecMulVec_star _
  · have hpt : ∀ k, ptraceOut (∑ h, Matrix.vecMulVec (choiVec (layerT eqF U0 U1 (KA k) (KB h)))
        (star (choiVec (layerT eqF U0 U1 (KA k) (KB h))))) =
        (∑ h, (layerT eqF U0 U1 (KA k) (KB h))ᴴ * layerT eqF U0 U1 (KA k) (KB h))ᵀ :=
      fun k => ptraceOut_sum_choiVec _
    rw [ptraceOut_sum']
    simp only [hpt]
    rw [← Matrix.transpose_sum, layerT_kraus_sum eqF hU0 hU1 hKA hKB, Matrix.transpose_one]

/-- The comb is completely pure: unitaries in, unitary out (AFNB Definition 3; manuscript §9: "If the channels of Alice and Bob are unitary, the composition is unitary"). -/
theorem combOp_pure (eqF : Fin (f + 1) ≃ Fin D.e × E1)
    {U0 : Matrix (Fin D.m × (R × E0)) (Fin (p + 1)) ℂ}
    {U1 : Matrix (Fin D.n × E1) ((R × Fin D.d) × E0) ℂ}
    (hU0 : Biunitary U0) (hU1 : Biunitary U1) : Pure D (combOp eqF U0 U1) := by
  refine ⟨combOp_deterministic eqF hU0 hU1, fun a a' b b' JA JB hJA hJB => ?_⟩
  obtain ⟨A, hA, hJAeq⟩ := (unitaryChoi_iff_biunitary JA).1 hJA
  obtain ⟨B, hB, hJBeq⟩ := (unitaryChoi_iff_biunitary JB).1 hJB
  have hJA' : JA = Matrix.vecMulVec (choiVec A) (star (choiVec A)) := by
    ext ⟨i, o⟩ ⟨j, o'⟩
    simp [hJAeq, Matrix.vecMulVec_apply, choiVec]
  have hJB' : JB = Matrix.vecMulVec (choiVec B) (star (choiVec B)) := by
    ext ⟨i, o⟩ ⟨j, o'⟩
    simp [hJBeq, Matrix.vecMulVec_apply, choiVec]
  refine (unitaryChoi_iff_biunitary _).2
    ⟨layerT eqF U0 U1 A B, layerT_biunitary eqF hU0 hU1 hA hB, ?_⟩
  intro i o j o'
  rw [hJA', hJB', combOp, link_rank_one, Matrix.vecMulVec_apply, Pi.star_apply, layerT_entry,
    layerT_entry]

section Recovery

variable {W : PMat D}

/-- `W = Ŵ ⊗ I_{B_O}` entrywise (`eq_hatAB_kronecker`). -/
theorem W_entry (hord : OrderedAB D W) (aI aI' : Fin D.m) (aO aO' : Fin D.d) (bI bI' : Fin D.n)
    (bO bO' : Fin D.e) :
    W ((aI, aO), (bI, bO)) ((aI', aO'), (bI', bO')) =
      hatAB D W ((aI, aO), bI) ((aI', aO'), bI') * (if bO = bO' then 1 else 0) := by
  conv_lhs => rw [eq_hatAB_kronecker D hord.2.2]
  simp only [Matrix.reindex_apply, Matrix.submatrix_apply, Equiv.symm_symm, eqBO_apply,
    Matrix.kroneckerMap_apply, Matrix.one_apply]

/-- Column `0` of the comb vector with the prescribed columns of `U_0`, `U_1`:
`s(0, (a_I,a_O,b_I,b_O), f) = δ_{b_O, f_{B_O}} ∑_r ψ_{a_I r} V_C[(b_I, f_{E_1}), (r, a_O)]`. -/
theorem combVec_zero (eqF : Fin (f + 1) ≃ Fin D.e × E1) (ψ : Matrix (Fin D.m) R ℂ)
    (V : Matrix (Fin D.n × E1) (R × Fin D.d) ℂ) (e₀ : E0)
    {U0 : Matrix (Fin D.m × (R × E0)) (Fin (p + 1)) ℂ}
    {U1 : Matrix (Fin D.n × E1) ((R × Fin D.d) × E0) ℂ}
    (hU0 : ∀ x, U0 x 0 = ψ x.1 x.2.1 * (if x.2.2 = e₀ then 1 else 0))
    (hU1 : ∀ x y, U1 x (y, e₀) = V x y)
    (aI : Fin D.m) (aO : Fin D.d) (bI : Fin D.n) (bO : Fin D.e) (z : Fin (f + 1)) :
    combVec eqF U0 U1 ((0, ((aI, aO), (bI, bO))), z) =
      if bO = (eqF z).1 then ∑ r, ψ aI r * V (bI, (eqF z).2) (r, aO) else 0 := by
  simp only [combVec, hU0]
  refine if_congr Iff.rfl ?_ rfl
  refine Finset.sum_congr rfl fun r _ => ?_
  rw [Finset.sum_eq_single e₀]
  · simp [hU1]
  · intro e _ he
    simp [he]
  · intro h
    exact absurd (Finset.mem_univ _) h

/-- Recovery `eq:purification`: fixing `|0⟩_P` and tracing out `F` gives back `W`, given the
prescribed columns of `U_0`, `U_1`, the Gram identity of `V` and the recovery identity
`Ŵ = ∑ ψ ψ̄ J` (manuscript: "Fixing `|0⟩^P` and discarding `F` recovers `W`"). -/
theorem reducePastFuture_combOp (hord : OrderedAB D W) (eqF : Fin (f + 1) ≃ Fin D.e × E1)
    (ψ : Matrix (Fin D.m) R ℂ) (J : Op ((R × Fin D.d) × Fin D.n))
    (V : Matrix (Fin D.n × E1) (R × Fin D.d) ℂ) (e₀ : E0)
    (hV : ∀ bI bI' r r' aO aO',
      ∑ h, V (bI, h) (r, aO) * star (V (bI', h) (r', aO')) = J ((r, aO), bI) ((r', aO'), bI'))
    (hrec : ∀ aI aI' aO aO' bI bI', hatAB D W ((aI, aO), bI) ((aI', aO'), bI') =
      ∑ r, ∑ r', ψ aI r * star (ψ aI' r') * J ((r, aO), bI) ((r', aO'), bI'))
    {U0 : Matrix (Fin D.m × (R × E0)) (Fin (p + 1)) ℂ}
    {U1 : Matrix (Fin D.n × E1) ((R × Fin D.d) × E0) ℂ}
    (hU0 : ∀ x, U0 x 0 = ψ x.1 x.2.1 * (if x.2.2 = e₀ then 1 else 0))
    (hU1 : ∀ x y, U1 x (y, e₀) = V x y) :
    reducePastFuture D (combOp eqF U0 U1) = W := by
  ext ⟨⟨aI, aO⟩, ⟨bI, bO⟩⟩ ⟨⟨aI', aO'⟩, ⟨bI', bO'⟩⟩
  rw [reducePastFuture_apply, W_entry hord, hrec]
  simp only [combOp, Matrix.vecMulVec_apply, Pi.star_apply, combVec_zero eqF ψ V e₀ hU0 hU1]
  refine (Fintype.sum_equiv eqF _ (fun q : Fin D.e × E1 =>
    (if bO = q.1 then ∑ r, ψ aI r * V (bI, q.2) (r, aO) else 0) *
      star (if bO' = q.1 then ∑ r, ψ aI' r * V (bI', q.2) (r, aO') else 0))
    (fun z => rfl)).trans ?_
  rw [Fintype.sum_prod_type]
  by_cases hb : bO = bO'
  · subst hb
    have hterm : ∀ (bO'' : Fin D.e) (e1 : E1),
        (if bO = bO'' then ∑ r, ψ aI r * V (bI, e1) (r, aO) else 0) *
          star (if bO = bO'' then ∑ r, ψ aI' r * V (bI', e1) (r, aO') else 0) =
        if bO = bO'' then
          (∑ r, ψ aI r * V (bI, e1) (r, aO)) * star (∑ r, ψ aI' r * V (bI', e1) (r, aO'))
        else 0 := by
      intro bO'' e1
      split_ifs <;> simp
    simp only [hterm, Finset.sum_ite_irrel, Finset.sum_const_zero, Finset.sum_ite_eq,
      Finset.mem_univ, if_true, mul_one]
    simp only [star_sum, star_mul', Finset.sum_mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun r _ => ?_
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun r' _ => ?_
    rw [← hV bI bI' r r' aO aO', Finset.mul_sum]
    exact Finset.sum_congr rfl fun e1 _ => by ring
  · simp only [hb, if_false, mul_zero]
    refine Finset.sum_eq_zero fun bO'' _ => Finset.sum_eq_zero fun e1 _ => ?_
    by_cases h1 : bO = bO''
    · have h2 : ¬ bO' = bO'' := fun h2 => hb (h1.trans h2.symm)
      simp [h1, h2]
    · simp [h1]

end Recovery

end Comb

/-! ### 7. Assembly (manuscript §9, `eq:sequential-S`) -/

section Assembly

variable {D : Ports} {W : PMat D}

/-- **Ordered purification with the manuscript's dimensions** (`thm:main` (iii), §9): for
`W ∈ O_{A≺B}` valid, `r = rank ρ_{A_I}`, and any `t ≥ n` (so that `r d t ≥ q = r d n`), there is a
completely pure process with `dim P = m r n t`, `dim F = dim (B_O E_1) = e r d t` recovering `W`. -/
theorem ordered_purifiable_dims (hW : Valid D W) (hord : OrderedAB D W) (t : ℕ) (ht : D.n ≤ t) :
    ∃ S : HigherOp D (D.m * (omegaA D W).rank * D.n * t - 1) (D.e * (omegaA D W).rank * D.d * t - 1),
      Pure D S ∧ reducePastFuture D S = W := by
  obtain ⟨U0, hU0, hU0col⟩ := exists_U0 hW t ht
  obtain ⟨U1, hU1, hU1col⟩ := exists_U1 hW hord ht
  refine ⟨combOp (eqFt hW t ht) U0 U1, combOp_pure _ hU0 hU1, ?_⟩
  refine reducePastFuture_combOp hord (eqFt hW t ht) (psiR (omegaA_posSemidef hW.2.1))
    (choiC hW.2.1) (VCpad hW.2.1 ht) (e0t t ht) (VCpad_choi hW.2.1 ht)
    (hatAB_entry hW hord) ?_ hU1col
  intro x
  rw [hU0col]
  rfl

/-- `W ∈ O_{A≺B}` valid ⇒ purifiable (take `t = n`). -/
theorem orderedAB_purifiable (hW : Valid D W) (hord : OrderedAB D W) : Purifiable D W := by
  obtain ⟨S, hS, hred⟩ := ordered_purifiable_dims hW hord D.n le_rfl
  exact ⟨_, _, S, hS, hred⟩

/-- `W ∈ O_{B≺A}` valid ⇒ purifiable ("For a process in `O_{B≺A}` we exchange the two
parties"; `Boundary/Swap`). -/
theorem orderedBA_purifiable (hW : Valid D W) (hord : OrderedBA D W) : Purifiable D W :=
  Purifiable.swap D (orderedAB_purifiable hW.swap hord.swap)

/-- **Ordered valid processes are purifiable** (§9, `thm:main` (iii) second half). -/
theorem ordered_purifiable (hW : Valid D W) (hord : OrderedAB D W ∨ OrderedBA D W) :
    Purifiable D W := by
  rcases hord with h | h
  · exact orderedAB_purifiable hW h
  · exact orderedBA_purifiable hW h

/-- **Every valid process with a one-dimensional port is purifiable** (§9). -/
theorem one_dimensional_purifiable (h1 : D.m = 1 ∨ D.d = 1 ∨ D.n = 1 ∨ D.e = 1)
    (hW : Valid D W) : Purifiable D W :=
  ordered_purifiable hW (one_dimensional_ordered h1 hW)

end Assembly

end

end CausalNonpurifiability
