module

public import Mathlib
public import CausalNonpurifiability.Linear.Positive
public import CausalNonpurifiability.EC.SOS
public import CausalNonpurifiability.Definitions.Instruments
public import CausalNonpurifiability.Data.Local

@[expose] public section


/-!
# `CausalNonpurifiability.EC.Compression`

Compression of coarse-grained effects to the distinguished input bases and the signed-input
contraction identity `D_C(E, H) ≥ 0` (`eq:DC`), using only the diagonal support of `C`.
This is the audit's hand-check item H1 (`AUDIT_INDEPENDENT.md` §6): the passage
`Tr[(C ⊗ σ)(E + H − 2EH)] = (1/160) Tr[σ (37 D₀₀ + 7 D₀₁ + 7 D₁₀ − 3 D₁₁)]` is an *exact*
block-diagonal identity, not a dephasing approximation.

Everything here is definition-independent and stated for plain matrices over explicit
product index types:

* `block`, `compress` — the `(k, k')` block and the principal submatrix
  `E_k(r, r') = T((k, r), (k, r'))` (`E_i = ⟨i|^{A_I} E |i⟩`, `H_j = ⟨j|^{B_I} H |j⟩` of `eq:DC`);
  effects compress to effects (`effect_compress`, via `effect_submatrix`).
* `trace_diagonal_kronecker_mul` — the diagonal pairing identity
  `Tr[(diag c ⊗ σ) T] = ∑ k, c k · Tr[σ · compress T k]`.
* `regroup`, `sideA`, `sideB` — the regrouping
  `(A_I × B_I) × (R_A × R_B) ≃ (A_I × R_A) × (B_I × R_B)` and the one-sided operators
  `E' = E ⊗ 1`, `H' = 1 ⊗ H` on the party-grouped joint space; their compressions are
  `compress E i ⊗ₖ 1`, `1 ⊗ₖ compress H j`, and blocks multiply:
  `compress (E' H') (i, j) = compress E i ⊗ₖ compress H j`.
* `dc_pairing_abstract` — `Tr[(diag c ⊗ σ)(E' + H' − 2E'H')]
  = ∑ (i,j), c (i,j) · Tr[σ · D_{ij}]` with `D_{ij} = dXor (compress E i ⊗ₖ 1) (1 ⊗ₖ compress H j)`.
* `cDC`, `dc_nonneg_abstract` — with the manuscript's diagonal `(37, 7, 7, −3)/160` on the four
  distinguished input pairs, the pairing is `(1/160) Tr[σ · SOS]`, hence `≥ 0` for PSD `σ` and
  effects `E`, `H` (`sos_matrix_psd` + `trace_mul_nonneg`).

Manuscript anchors: `eq:DC`, `eq:operator-SOS`, `eq:C` (diagonal of `C`).
-/

set_option autoImplicit false

open Matrix
open scoped ComplexOrder Kronecker MatrixOrder

namespace CausalNonpurifiability

/-! ### Blocks and compression -/

section Blocks

variable {K R : Type}

/-- The `(k, k')` block of `T : Matrix (K × R) (K × R) ℂ`:
`block T k k' r r' = T (k, r) (k', r')` (submatrix along `Prod.mk k`, `Prod.mk k'`). -/
def block (T : Matrix (K × R) (K × R) ℂ) (k k' : K) : Matrix R R ℂ :=
  T.submatrix (Prod.mk k) (Prod.mk k')

/-- Compression to the distinguished input `k`: the principal submatrix
`compress T k r r' = T (k, r) (k, r')`, i.e. `⟨k| T |k⟩` on the first factor
(`E_i = ⟨i|^{A_I} E |i⟩^{A_I}`, `H_j = ⟨j|^{B_I} H |j⟩^{B_I}` of `eq:DC`). -/
def compress (T : Matrix (K × R) (K × R) ℂ) (k : K) : Matrix R R ℂ :=
  block T k k

@[simp] theorem block_apply (T : Matrix (K × R) (K × R) ℂ) (k k' : K) (r r' : R) :
    block T k k' r r' = T (k, r) (k', r') := rfl

@[simp] theorem compress_apply (T : Matrix (K × R) (K × R) ℂ) (k : K) (r r' : R) :
    compress T k r r' = T (k, r) (k, r') := rfl

/-- A principal submatrix of a PSD matrix is PSD. -/
theorem posSemidef_compress {T : Matrix (K × R) (K × R) ℂ} (hT : T.PosSemidef) (k : K) :
    (compress T k).PosSemidef :=
  hT.submatrix (Prod.mk k)

/-- Compressions of effects are effects ("they are effects on `R_A`, `R_B`", `eq:DC`). -/
theorem effect_compress [DecidableEq K] [DecidableEq R] {T : Matrix (K × R) (K × R) ℂ}
    (hT : Effect T) (k : K) : Effect (compress T k) :=
  effect_submatrix hT (fun _ _ h => (Prod.mk.inj h).2)

theorem compress_add (S T : Matrix (K × R) (K × R) ℂ) (k : K) :
    compress (S + T) k = compress S k + compress T k :=
  Matrix.ext fun _ _ => rfl

theorem compress_sub (S T : Matrix (K × R) (K × R) ℂ) (k : K) :
    compress (S - T) k = compress S k - compress T k :=
  Matrix.ext fun _ _ => rfl

theorem compress_two_mul [Fintype K] [DecidableEq K] [Fintype R] [DecidableEq R]
    (T : Matrix (K × R) (K × R) ℂ) (k : K) : compress (2 * T) k = 2 * compress T k := by
  rw [two_mul, compress_add, two_mul]

/-- **Diagonal pairing identity.**  For `c : K → ℂ`, `σ : Matrix R R ℂ` and any
`T : Matrix (K × R) (K × R) ℂ`,
`Tr[(diag c ⊗ σ) T] = ∑ k, c k · Tr[σ · compress T k]`:
only the diagonal blocks of `T` in the distinguished basis of `K` contribute
("since `C` is diagonal", `eq:DC`).  Kronecker convention: `(A ⊗ₖ B) (k, r) (k', r') = A k k' * B r r'`. -/
theorem trace_diagonal_kronecker_mul [Fintype K] [DecidableEq K] [Fintype R] (c : K → ℂ)
    (σ : Matrix R R ℂ) (T : Matrix (K × R) (K × R) ℂ) :
    ((Matrix.diagonal c ⊗ₖ σ) * T).trace = ∑ k, c k * (σ * compress T k).trace := by
  simp only [Matrix.trace, Matrix.diag_apply, Matrix.mul_apply, Fintype.sum_prod_type,
    Matrix.kroneckerMap_apply, Matrix.diagonal_apply, compress_apply, ite_mul, zero_mul,
    Finset.mul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  refine Finset.sum_congr rfl fun r _ => ?_
  rw [Finset.sum_comm]
  simp [Finset.sum_ite_eq, mul_assoc]

end Blocks

/-! ### Two parties with ancillas: regrouping and one-sided operators -/

section TwoParty

variable {I J RA RB : Type}

/-- Regrouping `((A_I × B_I) × (R_A × R_B)) ≃ ((A_I × R_A) × (B_I × R_B))` between the
party-grouped order of the joint input space and the ancilla-grouped order in which one-sided
operators are literal Kronecker products (this is `Equiv.prodProdProdComm`). -/
def regroup (I J RA RB : Type) : (I × J) × (RA × RB) ≃ (I × RA) × (J × RB) where
  toFun x := ((x.1.1, x.2.1), (x.1.2, x.2.2))
  invFun y := ((y.1.1, y.2.1), (y.1.2, y.2.2))
  left_inv _ := rfl
  right_inv _ := rfl

@[simp] theorem regroup_apply (i : I) (j : J) (a : RA) (b : RB) :
    regroup I J RA RB ((i, j), (a, b)) = ((i, a), (j, b)) := rfl

@[simp] theorem regroup_symm_apply (i : I) (a : RA) (j : J) (b : RB) :
    (regroup I J RA RB).symm ((i, a), (j, b)) = ((i, j), (a, b)) := rfl

/-- Alice's operator `E ⊗ 1_{B_I R_B}` on the party-grouped joint space
(`E' = reindex (E ⊗ₖ 1)`; "extended by opposite-side identities", `eq:operator-SOS`). -/
def sideA [DecidableEq J] [DecidableEq RB] (E : Matrix (I × RA) (I × RA) ℂ) :
    Matrix ((I × J) × (RA × RB)) ((I × J) × (RA × RB)) ℂ :=
  (E ⊗ₖ (1 : Matrix (J × RB) (J × RB) ℂ)).submatrix (regroup I J RA RB) (regroup I J RA RB)

/-- Bob's operator `1_{A_I R_A} ⊗ H` on the party-grouped joint space (`H' = reindex (1 ⊗ₖ H)`). -/
def sideB [DecidableEq I] [DecidableEq RA] (H : Matrix (J × RB) (J × RB) ℂ) :
    Matrix ((I × J) × (RA × RB)) ((I × J) × (RA × RB)) ℂ :=
  ((1 : Matrix (I × RA) (I × RA) ℂ) ⊗ₖ H).submatrix (regroup I J RA RB) (regroup I J RA RB)

theorem sideA_eq_reindex [DecidableEq J] [DecidableEq RB] (E : Matrix (I × RA) (I × RA) ℂ) :
    sideA (J := J) (RB := RB) E
      = Matrix.reindex (regroup I J RA RB).symm (regroup I J RA RB).symm
          (E ⊗ₖ (1 : Matrix (J × RB) (J × RB) ℂ)) := rfl

theorem sideB_eq_reindex [DecidableEq I] [DecidableEq RA] (H : Matrix (J × RB) (J × RB) ℂ) :
    sideB (I := I) (RA := RA) H
      = Matrix.reindex (regroup I J RA RB).symm (regroup I J RA RB).symm
          ((1 : Matrix (I × RA) (I × RA) ℂ) ⊗ₖ H) := rfl

@[simp] theorem sideA_apply [DecidableEq J] [DecidableEq RB] (E : Matrix (I × RA) (I × RA) ℂ)
    (i i' : I) (j j' : J) (a a' : RA) (b b' : RB) :
    sideA (J := J) (RB := RB) E ((i, j), (a, b)) ((i', j'), (a', b'))
      = E (i, a) (i', a') * (1 : Matrix (J × RB) (J × RB) ℂ) (j, b) (j', b') := rfl

@[simp] theorem sideB_apply [DecidableEq I] [DecidableEq RA] (H : Matrix (J × RB) (J × RB) ℂ)
    (i i' : I) (j j' : J) (a a' : RA) (b b' : RB) :
    sideB (I := I) (RA := RA) H ((i, j), (a, b)) ((i', j'), (a', b'))
      = (1 : Matrix (I × RA) (I × RA) ℂ) (i, a) (i', a') * H (j, b) (j', b') := rfl

/-- Compressing Alice's extended operator: `compress E' (i, j) = compress E i ⊗ₖ 1_{R_B}`. -/
theorem compress_sideA [DecidableEq J] [DecidableEq RB] (E : Matrix (I × RA) (I × RA) ℂ)
    (i : I) (j : J) :
    compress (sideA (J := J) (RB := RB) E) (i, j) = compress E i ⊗ₖ (1 : Matrix RB RB ℂ) := by
  ext ⟨a, b⟩ ⟨a', b'⟩
  simp [Matrix.one_apply]

/-- Compressing Bob's extended operator: `compress H' (i, j) = 1_{R_A} ⊗ₖ compress H j`. -/
theorem compress_sideB [DecidableEq I] [DecidableEq RA] (H : Matrix (J × RB) (J × RB) ℂ)
    (i : I) (j : J) :
    compress (sideB (I := I) (RA := RA) H) (i, j) = (1 : Matrix RA RA ℂ) ⊗ₖ compress H j := by
  ext ⟨a, b⟩ ⟨a', b'⟩
  simp [Matrix.one_apply]

/-- Compressing a regrouped Kronecker product: `compress (E ⊗ H)' (i, j) = compress E i ⊗ₖ compress H j`. -/
theorem compress_kronecker_regroup (E : Matrix (I × RA) (I × RA) ℂ)
    (H : Matrix (J × RB) (J × RB) ℂ) (i : I) (j : J) :
    compress ((E ⊗ₖ H).submatrix (regroup I J RA RB) (regroup I J RA RB)) (i, j)
      = compress E i ⊗ₖ compress H j := by
  ext ⟨a, b⟩ ⟨a', b'⟩
  simp

/-- The diagonal of `C` (`eq:C`, `eq:DC`): `(37, 7, 7, −3)/160` on the four distinguished input
pairs `(i₀,j₀), (i₀,j₁), (i₁,j₀), (i₁,j₁)` and `0` on every other input pair (additional input
dimensions contribute isolated zero vertices, `eq:K`). -/
noncomputable def cDC [DecidableEq I] [DecidableEq J] (i0 i1 : I) (j0 j1 : J) :
    I × J → ℂ := fun p =>
  37 / 160 * (if p = (i0, j0) then 1 else 0) + 7 / 160 * (if p = (i0, j1) then 1 else 0)
    + 7 / 160 * (if p = (i1, j0) then 1 else 0) - 3 / 160 * (if p = (i1, j1) then 1 else 0)

variable [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]
  [Fintype RA] [DecidableEq RA] [Fintype RB] [DecidableEq RB]

/-- `E' H' = (E ⊗ H)'`: Alice's operator is block-diagonal in `B_I R_B`, Bob's in `A_I R_A`. -/
theorem sideA_mul_sideB (E : Matrix (I × RA) (I × RA) ℂ) (H : Matrix (J × RB) (J × RB) ℂ) :
    sideA (J := J) (RB := RB) E * sideB (I := I) (RA := RA) H
      = (E ⊗ₖ H).submatrix (regroup I J RA RB) (regroup I J RA RB) := by
  unfold sideA sideB
  rw [Matrix.submatrix_mul_equiv, ← Matrix.mul_kronecker_mul, Matrix.mul_one, Matrix.one_mul]

/-- `H' E' = (E ⊗ H)'`. -/
theorem sideB_mul_sideA (E : Matrix (I × RA) (I × RA) ℂ) (H : Matrix (J × RB) (J × RB) ℂ) :
    sideB (I := I) (RA := RA) H * sideA (J := J) (RB := RB) E
      = (E ⊗ₖ H).submatrix (regroup I J RA RB) (regroup I J RA RB) := by
  unfold sideA sideB
  rw [Matrix.submatrix_mul_equiv, ← Matrix.mul_kronecker_mul, Matrix.mul_one, Matrix.one_mul]

/-- Cross-party commutation `[E', H'] = 0` on the party-grouped joint space. -/
theorem commute_sideA_sideB (E : Matrix (I × RA) (I × RA) ℂ) (H : Matrix (J × RB) (J × RB) ℂ) :
    Commute (sideA (J := J) (RB := RB) E) (sideB (I := I) (RA := RA) H) :=
  (sideA_mul_sideB E H).trans (sideB_mul_sideA E H).symm

/-- Blocks multiply: `compress (E' H') (i, j) = compress E i ⊗ₖ compress H j`. -/
theorem compress_sideA_mul_sideB (E : Matrix (I × RA) (I × RA) ℂ)
    (H : Matrix (J × RB) (J × RB) ℂ) (i : I) (j : J) :
    compress (sideA (J := J) (RB := RB) E * sideB (I := I) (RA := RA) H) (i, j)
      = compress E i ⊗ₖ compress H j := by
  rw [sideA_mul_sideB]
  exact compress_kronecker_regroup E H i j

/-- One-sided extensions of effects are effects. -/
theorem effect_sideA {E : Matrix (I × RA) (I × RA) ℂ} (hE : Effect E) :
    Effect (sideA (J := J) (RB := RB) E) :=
  effect_submatrix (effect_kronecker_one hE) (regroup I J RA RB).injective

theorem effect_sideB {H : Matrix (J × RB) (J × RB) ℂ} (hH : Effect H) :
    Effect (sideB (I := I) (RA := RA) H) :=
  effect_submatrix (effect_one_kronecker hH) (regroup I J RA RB).injective

/-- Compression of the signed-input operator `E' + H' − 2 E' H'`:
`compress (E' + H' − 2E'H') (i, j) = D_{ij} := dXor (compress E i ⊗ₖ 1) (1 ⊗ₖ compress H j)`
(`eq:DC`; the identity factors in `E + H − 2EH` are implicit). -/
theorem compress_dXor_side (E : Matrix (I × RA) (I × RA) ℂ) (H : Matrix (J × RB) (J × RB) ℂ)
    (i : I) (j : J) :
    compress (sideA (J := J) (RB := RB) E + sideB (I := I) (RA := RA) H
        - 2 * sideA (J := J) (RB := RB) E * sideB (I := I) (RA := RA) H) (i, j)
      = dXor (compress E i ⊗ₖ (1 : Matrix RB RB ℂ)) ((1 : Matrix RA RA ℂ) ⊗ₖ compress H j) := by
  rw [dXor, compress_sub, compress_add, mul_assoc, compress_two_mul, compress_sideA,
    compress_sideB, compress_sideA_mul_sideB, mul_assoc, ← Matrix.mul_kronecker_mul,
    Matrix.mul_one, Matrix.one_mul]

/-- **Compression identity for the signed input term** (`eq:DC`, first equality, abstract form):
`Tr[(diag c ⊗ σ)(E' + H' − 2E'H')] = ∑ (i,j), c (i,j) · Tr[σ · D_{ij}]`,
`D_{ij} = dXor (compress E i ⊗ₖ 1) (1 ⊗ₖ compress H j)`.  Exact; nothing is dephased. -/
theorem dc_pairing_abstract (c : I × J → ℂ) (σ : Matrix (RA × RB) (RA × RB) ℂ)
    (E : Matrix (I × RA) (I × RA) ℂ) (H : Matrix (J × RB) (J × RB) ℂ) :
    ((Matrix.diagonal c ⊗ₖ σ) * (sideA (J := J) (RB := RB) E + sideB (I := I) (RA := RA) H
        - 2 * sideA (J := J) (RB := RB) E * sideB (I := I) (RA := RA) H)).trace
      = ∑ p : I × J, c p * (σ * dXor (compress E p.1 ⊗ₖ (1 : Matrix RB RB ℂ))
          ((1 : Matrix RA RA ℂ) ⊗ₖ compress H p.2)).trace := by
  rw [trace_diagonal_kronecker_mul]
  refine Finset.sum_congr rfl fun p _ => ?_
  obtain ⟨i, j⟩ := p
  rw [compress_dXor_side]

/-- Double-sum form of `dc_pairing_abstract`. -/
theorem dc_pairing_abstract' (c : I × J → ℂ) (σ : Matrix (RA × RB) (RA × RB) ℂ)
    (E : Matrix (I × RA) (I × RA) ℂ) (H : Matrix (J × RB) (J × RB) ℂ) :
    ((Matrix.diagonal c ⊗ₖ σ) * (sideA (J := J) (RB := RB) E + sideB (I := I) (RA := RA) H
        - 2 * sideA (J := J) (RB := RB) E * sideB (I := I) (RA := RA) H)).trace
      = ∑ i : I, ∑ j : J, c (i, j) * (σ * dXor (compress E i ⊗ₖ (1 : Matrix RB RB ℂ))
          ((1 : Matrix RA RA ℂ) ⊗ₖ compress H j)).trace := by
  rw [dc_pairing_abstract, Fintype.sum_prod_type]

/-! ### The manuscript's diagonal coefficients and positivity -/

theorem sum_cDC_mul (i0 i1 : I) (j0 j1 : J) (f : I × J → ℂ) :
    ∑ p : I × J, cDC i0 i1 j0 j1 p * f p
      = 37 / 160 * f (i0, j0) + 7 / 160 * f (i0, j1) + 7 / 160 * f (i1, j0)
          - 3 / 160 * f (i1, j1) := by
  have h : ∀ q : I × J, ∑ p : I × J, (if p = q then (1 : ℂ) else 0) * f p = f q := fun q => by
    simp [Finset.sum_ite_eq']
  simp only [cDC, add_mul, sub_mul, Finset.sum_add_distrib, Finset.sum_sub_distrib, mul_assoc,
    ← Finset.mul_sum, h]

theorem nsmul_eq_complex_smul {m : Type} (n : ℕ) (A : Matrix m m ℂ) : n • A = (n : ℂ) • A :=
  (Nat.cast_smul_eq_nsmul ℂ n A).symm

/-- **`eq:DC` as an exact identity**: with the manuscript's diagonal coefficients,
`Tr[(C ⊗ σ)(E' + H' − 2E'H')] = Tr[σ · (1/160)(37 D₀₀ + 7 D₀₁ + 7 D₁₀ − 3 D₁₁)]`. -/
theorem dc_trace_eq (σ : Matrix (RA × RB) (RA × RB) ℂ) (E : Matrix (I × RA) (I × RA) ℂ)
    (H : Matrix (J × RB) (J × RB) ℂ) (i0 i1 : I) (j0 j1 : J) :
    ((Matrix.diagonal (cDC i0 i1 j0 j1) ⊗ₖ σ) * (sideA (J := J) (RB := RB) E
        + sideB (I := I) (RA := RA) H
        - 2 * sideA (J := J) (RB := RB) E * sideB (I := I) (RA := RA) H)).trace
      = (σ * ((1 / 160 : ℝ) •
          ((37 : ℕ) • dXor (compress E i0 ⊗ₖ (1 : Matrix RB RB ℂ))
              ((1 : Matrix RA RA ℂ) ⊗ₖ compress H j0)
            + (7 : ℕ) • dXor (compress E i0 ⊗ₖ (1 : Matrix RB RB ℂ))
              ((1 : Matrix RA RA ℂ) ⊗ₖ compress H j1)
            + (7 : ℕ) • dXor (compress E i1 ⊗ₖ (1 : Matrix RB RB ℂ))
              ((1 : Matrix RA RA ℂ) ⊗ₖ compress H j0)
            - (3 : ℕ) • dXor (compress E i1 ⊗ₖ (1 : Matrix RB RB ℂ))
              ((1 : Matrix RA RA ℂ) ⊗ₖ compress H j1)))).trace := by
  rw [dc_pairing_abstract, sum_cDC_mul]
  simp only [nsmul_eq_complex_smul, Matrix.mul_smul, mul_add, mul_sub, Matrix.trace_smul,
    Matrix.trace_add, Matrix.trace_sub, smul_eq_mul, Complex.real_smul]
  push_cast
  ring

/-- **`eq:DC` positivity** (audit item H1): for a PSD `σ` on `R_A R_B` and effects `E` on
`A_I R_A`, `H` on `B_I R_B`, `Tr[(C ⊗ σ)(E' + H' − 2E'H')] ≥ 0` in the `ComplexOrder`.
The trace equals `(1/160) Tr[σ · (37D₀₀ + 7D₀₁ + 7D₁₀ − 3D₁₁)]` exactly (`dc_trace_eq`), and the
operator is PSD by the dimension-free SOS `sos_matrix_psd` (`eq:operator-SOS`). -/
theorem dc_nonneg_abstract {σ : Matrix (RA × RB) (RA × RB) ℂ} (hσ : σ.PosSemidef)
    {E : Matrix (I × RA) (I × RA) ℂ} (hE : Effect E) {H : Matrix (J × RB) (J × RB) ℂ}
    (hH : Effect H) (i0 i1 : I) (j0 j1 : J) :
    0 ≤ ((Matrix.diagonal (cDC i0 i1 j0 j1) ⊗ₖ σ) * (sideA (J := J) (RB := RB) E
        + sideB (I := I) (RA := RA) H
        - 2 * sideA (J := J) (RB := RB) E * sideB (I := I) (RA := RA) H)).trace := by
  rw [dc_trace_eq]
  exact trace_mul_nonneg hσ (posSemidef_real_smul
    (sos_matrix_psd (effect_compress hE i0) (effect_compress hE i1)
      (effect_compress hH j0) (effect_compress hH j1)) (by norm_num))

/-- Real-part form of `dc_nonneg_abstract`: `0 ≤ re Tr[(C ⊗ σ)(E' + H' − 2E'H')]`. -/
theorem dc_re_nonneg_abstract {σ : Matrix (RA × RB) (RA × RB) ℂ} (hσ : σ.PosSemidef)
    {E : Matrix (I × RA) (I × RA) ℂ} (hE : Effect E) {H : Matrix (J × RB) (J × RB) ℂ}
    (hH : Effect H) (i0 i1 : I) (j0 j1 : J) :
    0 ≤ (((Matrix.diagonal (cDC i0 i1 j0 j1) ⊗ₖ σ) * (sideA (J := J) (RB := RB) E
        + sideB (I := I) (RA := RA) H
        - 2 * sideA (J := J) (RB := RB) E * sideB (I := I) (RA := RA) H)).trace).re :=
  (Complex.nonneg_iff.mp (dc_nonneg_abstract hσ hE hH i0 i1 j0 j1)).1

/-- The `eq:DC` pairing is real. -/
theorem dc_im_zero_abstract {σ : Matrix (RA × RB) (RA × RB) ℂ} (hσ : σ.PosSemidef)
    {E : Matrix (I × RA) (I × RA) ℂ} (hE : Effect E) {H : Matrix (J × RB) (J × RB) ℂ}
    (hH : Effect H) (i0 i1 : I) (j0 j1 : J) :
    (((Matrix.diagonal (cDC i0 i1 j0 j1) ⊗ₖ σ) * (sideA (J := J) (RB := RB) E
        + sideB (I := I) (RA := RA) H
        - 2 * sideA (J := J) (RB := RB) E * sideB (I := I) (RA := RA) H)).trace).im = 0 :=
  ((Complex.nonneg_iff.mp (dc_nonneg_abstract hσ hE hH i0 i1 j0 j1)).2).symm

end TwoParty

/-! ### `eq:DC` for coarse-grained instruments -/

section Wiring

variable (D : Ports) {RA RB X Y A B : Type} [Fintype RA] [DecidableEq RA] [Fintype RB]
  [DecidableEq RB] [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]

/-- **`eq:DC` in the manuscript's variables.**  For a PSD ancilla state `σ` on `R_A R_B`,
extended instruments `M`, `N`, settings `x`, `y` and outcome subsets `S`, `T`, put
`E = Tr_{A_O} ∑_{a∈S} M_{a|x}`, `H = Tr_{B_O} ∑_{b∈T} N_{b|y}` (effects on `A_I R_A`, `B_I R_B`).
Then `D_C(E,H) = Tr[(C ⊗ σ)(E + H − 2EH)] ≥ 0`, with `C = diag (37,7,7,−3)/160` on the
distinguished input pairs `(i₀,j₀),(i₀,j₁),(i₁,j₀),(i₁,j₁)` (`cDC`), the identity factors on
the opposite party implicit (`sideA`, `sideB`).  Exact block-diagonal identity + `sos_matrix_psd`;
nothing is dephased (audit item H1). -/
theorem dc_compression {σ : Op (RA × RB)} (hσ : σ.PosSemidef)
    (M : Instrument (Fin D.m × RA) (Fin D.d) X A) (N : Instrument (Fin D.n × RB) (Fin D.e) Y B)
    (x : X) (y : Y) (S : Finset A) (T : Finset B) (i0 i1 : Fin D.m) (j0 j1 : Fin D.n) :
    0 ≤ (((Matrix.diagonal (cDC i0 i1 j0 j1) ⊗ₖ σ)
        * (sideA (J := Fin D.n) (RB := RB) (ptraceOut (∑ a ∈ S, M.elem x a))
          + sideB (I := Fin D.m) (RA := RA) (ptraceOut (∑ b ∈ T, N.elem y b))
          - 2 * sideA (J := Fin D.n) (RB := RB) (ptraceOut (∑ a ∈ S, M.elem x a))
            * sideB (I := Fin D.m) (RA := RA) (ptraceOut (∑ b ∈ T, N.elem y b)))).trace).re :=
  dc_re_nonneg_abstract hσ (M.effect_ptraceOut x S) (N.effect_ptraceOut y T) i0 i1 j0 j1

/-- `eq:DC` with the manuscript's distinguished inputs `0, 1` (needs `m, n ≥ 2`, `AllPortsGE2`). -/
theorem dc_compression_std (h : AllPortsGE2 D) {σ : Op (RA × RB)} (hσ : σ.PosSemidef)
    (M : Instrument (Fin D.m × RA) (Fin D.d) X A) (N : Instrument (Fin D.n × RB) (Fin D.e) Y B)
    (x : X) (y : Y) (S : Finset A) (T : Finset B) :
    0 ≤ (((Matrix.diagonal (cDC (⟨0, by have := h.1; omega⟩ : Fin D.m) ⟨1, by have := h.1; omega⟩
          (⟨0, by have := h.2.2.1; omega⟩ : Fin D.n) ⟨1, by have := h.2.2.1; omega⟩) ⊗ₖ σ)
        * (sideA (J := Fin D.n) (RB := RB) (ptraceOut (∑ a ∈ S, M.elem x a))
          + sideB (I := Fin D.m) (RA := RA) (ptraceOut (∑ b ∈ T, N.elem y b))
          - 2 * sideA (J := Fin D.n) (RB := RB) (ptraceOut (∑ a ∈ S, M.elem x a))
            * sideB (I := Fin D.m) (RA := RA) (ptraceOut (∑ b ∈ T, N.elem y b)))).trace).re :=
  dc_compression D hσ M N x y S T _ _ _ _

end Wiring

/-! ### Pairing lemmas for the rectangle slack identity (`eq:rectangle-slack`)

`rectangle_slack` is assembled from: `qc_pairing` (the `Q_C` part of `W₀` pairs with the
output-traced effects `E = Tr_{A_O} F`, `H = Tr_{B_O} G`), `cA_pairing`/`cB_pairing` (the reference
terms `Tr[(C_A ⊗ σ_{R_A}) E]`, `Tr[(C_B ⊗ σ_{R_B}) H]`), `signed_pairing` (linearity), and the
`toC` bridges `toC_Qembed_eq_QC`, `toC_C_eq_diagonal_cDC` to the rational data. -/

section TraceReindex

variable {ι κ : Type} [Fintype ι] [Fintype κ]

/-- `Tr[(A∘e) B] = Tr[A (B∘e⁻¹)]`: reindexing one factor of a trace pairing. -/
theorem trace_submatrix_mul (e : ι ≃ κ) (A : Op κ) (B : Op ι) :
    (A.submatrix e e * B).trace = (A * B.submatrix e.symm e.symm).trace := by
  have hB : B = (B.submatrix e.symm e.symm).submatrix e e := by
    ext i j
    simp
  rw [show A.submatrix e e * B = A.submatrix e e * (B.submatrix e.symm e.symm).submatrix e e by
      rw [← hB],
    Matrix.submatrix_mul_equiv, trace_submatrix_equiv_eq]

/-- `Tr[A (B∘e)] = Tr[(A∘e⁻¹) B]`. -/
theorem trace_mul_submatrix (e : ι ≃ κ) (A : Op ι) (B : Op κ) :
    (A * B.submatrix e e).trace = (A.submatrix e.symm e.symm * B).trace := by
  have h := trace_submatrix_mul e.symm A B
  rw [Equiv.symm_symm] at h
  exact h.symm

end TraceReindex


section Pairing

variable {I J RA RB O T : Type}

/-- Regrouping of the extended laboratory index with the outputs last:
`(((a,ra),o),((b,rb),t)) ↦ (((a,b),(ra,rb)),(o,t))` (inputs, ancillas, outputs). -/
def regroupOut (I J RA RB O T : Type) :
    ((I × RA) × O) × ((J × RB) × T) ≃ ((I × J) × (RA × RB)) × (O × T) where
  toFun x := (((x.1.1.1, x.2.1.1), (x.1.1.2, x.2.1.2)), (x.1.2, x.2.2))
  invFun y := (((y.1.1.1, y.1.2.1), y.2.1), ((y.1.1.2, y.1.2.2), y.2.2))
  left_inv _ := rfl
  right_inv _ := rfl

@[simp] theorem regroupOut_apply (a : I) (b : J) (ra : RA) (rb : RB) (o : O) (t : T) :
    regroupOut I J RA RB O T (((a, ra), o), ((b, rb), t)) = (((a, b), (ra, rb)), (o, t)) := rfl

@[simp] theorem regroupOut_symm_apply (a : I) (b : J) (ra : RA) (rb : RB) (o : O) (t : T) :
    (regroupOut I J RA RB O T).symm (((a, b), (ra, rb)), (o, t)) = (((a, ra), o), ((b, rb), t)) :=
  rfl

/-- Output partial trace of a regrouped `F ⊗ G` is the regrouped `Tr_{A_O} F ⊗ Tr_{B_O} G`. -/
theorem ptraceOut_kron_regroupOut [Fintype O] [Fintype T] (F : Op ((I × RA) × O))
    (G : Op ((J × RB) × T)) :
    ptraceOut ((F ⊗ₖ G).submatrix (regroupOut I J RA RB O T).symm (regroupOut I J RA RB O T).symm)
      = (ptraceOut F ⊗ₖ ptraceOut G).submatrix (regroup I J RA RB) (regroup I J RA RB) := by
  ext ⟨⟨a, b⟩, ⟨ra, rb⟩⟩ ⟨⟨a', b'⟩, ⟨ra', rb'⟩⟩
  simp [ptraceOut_apply, Fintype.sum_prod_type, Finset.sum_mul_sum]

/-- `Tr_{B_I R_B}` of the regrouped `C ⊗ σ` is `C_A ⊗ σ_{R_A} = Tr_{B_I} C ⊗ Tr_{R_B} σ`. -/
theorem ptraceOut_kron_regroup_symm [Fintype J] [Fintype RB] (C : Op (I × J)) (σ : Op (RA × RB)) :
    ptraceOut ((C ⊗ₖ σ).submatrix (regroup I J RA RB).symm (regroup I J RA RB).symm)
      = ptraceOut C ⊗ₖ ptraceOut σ := by
  ext ⟨a, ra⟩ ⟨a', ra'⟩
  simp [ptraceOut_apply, Fintype.sum_prod_type, Finset.sum_mul_sum]

/-- `Tr_{A_I R_A}` of the regrouped `C ⊗ σ` is `C_B ⊗ σ_{R_B} = Tr_{A_I} C ⊗ Tr_{R_A} σ`. -/
theorem ptraceFst_kron_regroup_symm [Fintype I] [Fintype RA] (C : Op (I × J)) (σ : Op (RA × RB)) :
    ptraceFst ((C ⊗ₖ σ).submatrix (regroup I J RA RB).symm (regroup I J RA RB).symm)
      = ptraceFst C ⊗ₖ ptraceFst σ := by
  ext ⟨b, rb⟩ ⟨b', rb'⟩
  simp [ptraceFst_apply, Fintype.sum_prod_type, Finset.sum_mul_sum]

/-- **Reference pairing, Alice** (`eq:endpoints` / `eq:reference-states`):
`Tr[(C_A ⊗ σ_{R_A}) E] = Tr[(C ⊗ σ)(E ⊗ I_{B_I R_B})]` with `C_A = Tr_{B_I} C`, `σ_{R_A} = Tr_{R_B} σ`. -/
theorem cA_pairing [Fintype I] [Fintype J] [DecidableEq J] [Fintype RA] [Fintype RB]
    [DecidableEq RB] (C : Op (I × J)) (σ : Op (RA × RB)) (E : Op (I × RA)) :
    ((ptraceOut C ⊗ₖ ptraceOut σ) * E).trace = ((C ⊗ₖ σ) * sideA (J := J) (RB := RB) E).trace := by
  rw [Matrix.trace_mul_comm (C ⊗ₖ σ) (sideA (J := J) (RB := RB) E), sideA, trace_submatrix_mul,
    trace_kronecker_one_mul, ptraceOut_kron_regroup_symm, Matrix.trace_mul_comm]

/-- **Reference pairing, Bob**: `Tr[(C_B ⊗ σ_{R_B}) H] = Tr[(C ⊗ σ)(I_{A_I R_A} ⊗ H)]` with
`C_B = Tr_{A_I} C`, `σ_{R_B} = Tr_{R_A} σ`. -/
theorem cB_pairing [Fintype I] [DecidableEq I] [Fintype J] [Fintype RA] [DecidableEq RA]
    [Fintype RB] (C : Op (I × J)) (σ : Op (RA × RB)) (H : Op (J × RB)) :
    ((ptraceFst C ⊗ₖ ptraceFst σ) * H).trace = ((C ⊗ₖ σ) * sideB (I := I) (RA := RA) H).trace := by
  rw [Matrix.trace_mul_comm (C ⊗ₖ σ) (sideB (I := I) (RA := RA) H), sideB, trace_submatrix_mul,
    trace_one_kronecker_mul, ptraceFst_kron_regroup_symm, Matrix.trace_mul_comm]

/-- **Signed pairing** (linearity): `Tr[A X] + Tr[A Y] − 2 Tr[A (X Y)] = Tr[A (X + Y − 2 X Y)]`;
with `A = C ⊗ σ`, `X = E'`, `Y = H'` this is the right-hand side fed to `dc_pairing_abstract`. -/
theorem signed_pairing {ι : Type} [Fintype ι] [DecidableEq ι] (A X Y : Op ι) :
    (A * X).trace + (A * Y).trace - 2 * (A * (X * Y)).trace = (A * (X + Y - 2 * X * Y)).trace := by
  have h2 : (2 : Op ι) * X * Y = X * Y + X * Y := by rw [mul_assoc, two_mul]
  rw [h2, mul_sub, mul_add, mul_add, Matrix.trace_sub, Matrix.trace_add, Matrix.trace_add, two_mul]

end Pairing

section QCPairing

variable (D : Ports) {RA RB : Type}

/-- `(Q_C ⊗ σ)` extended is `(C ⊗ σ) ⊗ I_{A_O B_O}` in the outputs-last regrouping. -/
theorem extended_QC_eq (C : Op (Fin D.m × Fin D.n)) (σ : Op (RA × RB)) :
    extended (QC D C) σ
      = ((C ⊗ₖ σ) ⊗ₖ (1 : Op (Fin D.d × Fin D.e))).submatrix
          (regroupOut (Fin D.m) (Fin D.n) RA RB (Fin D.d) (Fin D.e))
          (regroupOut (Fin D.m) (Fin D.n) RA RB (Fin D.d) (Fin D.e)) := by
  ext ⟨⟨⟨a, ra⟩, o⟩, ⟨⟨b, rb⟩, t⟩⟩ ⟨⟨⟨a', ra'⟩, o'⟩, ⟨⟨b', rb'⟩, t'⟩⟩
  simp only [extended_apply', QC_apply, Matrix.submatrix_apply, regroupOut_apply,
    Matrix.kroneckerMap_apply, Matrix.one_apply, Prod.mk.injEq]
  split_ifs <;> ring

/-- **`Q_C` pairing** (`eq:QC` inside `eq:born`): `Q_C` carries the identity on `A_O B_O`, so the
outputs of `F`, `G` are traced: `Tr[(Q_C ⊗ σ)(F ⊗ G)] = Tr[(C ⊗ σ)(E ⊗ H)']` with
`E = Tr_{A_O} F`, `H = Tr_{B_O} G` and `(E ⊗ H)'` regrouped onto `(A_I B_I) × (R_A R_B)`. -/
theorem qc_pairing [Fintype RA] [Fintype RB] (C : Op (Fin D.m × Fin D.n)) (σ : Op (RA × RB))
    (F : Op ((Fin D.m × RA) × Fin D.d)) (G : Op ((Fin D.n × RB) × Fin D.e)) :
    (extended (QC D C) σ * (F ⊗ₖ G)).trace
      = ((C ⊗ₖ σ) * (ptraceOut F ⊗ₖ ptraceOut G).submatrix (regroup (Fin D.m) (Fin D.n) RA RB)
          (regroup (Fin D.m) (Fin D.n) RA RB)).trace := by
  rw [extended_QC_eq, trace_submatrix_mul, trace_kronecker_one_mul, ptraceOut_kron_regroupOut]

variable [Fintype RA] [DecidableEq RA] [Fintype RB] [DecidableEq RB]

/-- `qc_pairing` with the right side written as `Tr[(C ⊗ σ)(E' H')]`, `E' = sideA E`, `H' = sideB H`
(matches `sideA_mul_sideB`). -/
theorem qc_pairing_side (C : Op (Fin D.m × Fin D.n)) (σ : Op (RA × RB))
    (F : Op ((Fin D.m × RA) × Fin D.d)) (G : Op ((Fin D.n × RB) × Fin D.e)) :
    (extended (QC D C) σ * (F ⊗ₖ G)).trace
      = ((C ⊗ₖ σ) * (sideA (J := Fin D.n) (RB := RB) (ptraceOut F)
          * sideB (I := Fin D.m) (RA := RA) (ptraceOut G))).trace := by
  rw [qc_pairing, sideA_mul_sideB]

/-- `qc_pairing` in the `extendInput` spelling. -/
theorem qc_pairing_extendInput (C : Op (Fin D.m × Fin D.n)) (σ : Op (RA × RB))
    (F : Op ((Fin D.m × RA) × Fin D.d)) (G : Op ((Fin D.n × RB) × Fin D.e)) :
    (extendInput D (QC D C) σ * (F ⊗ₖ G)).trace
      = ((C ⊗ₖ σ) * (sideA (J := Fin D.n) (RB := RB) (ptraceOut F)
          * sideB (I := Fin D.m) (RA := RA) (ptraceOut G))).trace :=
  qc_pairing_side D C σ F G

end QCPairing

/-! ### Bridges to the rational data (`Data/Local`) -/

section RationalBridges

/-- The rational `Qembed` and the complex `QC` are the same entry rule (Appendix C). -/
theorem toC_Qembed_eq_QC (D : Ports) (C : Matrix (Fin D.m × Fin D.n) (Fin D.m × Fin D.n) ℚ) :
    toC (Qembed D.d D.e C) = QC D (toC C) := by
  ext ⟨⟨a, o⟩, ⟨b, t⟩⟩ ⟨⟨a', o'⟩, ⟨b', t'⟩⟩
  simp only [toC_apply, Qembed, Matrix.of_apply, QC_apply]
  split_ifs <;> simp_all

/-- `C m n` (`eq:C`) is the diagonal `cDC 0 1 0 1` (`(37, 7, 7, −3)/160` on the four
distinguished input pairs) after lifting to `ℂ`. -/
theorem toC_C_eq_diagonal_cDC {m n : ℕ} (hm : 2 ≤ m) (hn : 2 ≤ n) :
    toC (C m n) = Matrix.diagonal (cDC (⟨0, by omega⟩ : Fin m) ⟨1, by omega⟩
      (⟨0, by omega⟩ : Fin n) ⟨1, by omega⟩) := by
  ext ⟨a, b⟩ ⟨a', b'⟩
  simp only [toC_apply, C, proj_eq, Matrix.smul_apply, Matrix.add_apply, Matrix.sub_apply,
    Matrix.kroneckerMap_apply, Matrix.diagonal_apply, cDC, Prod.mk.injEq, Fin.ext_iff,
    smul_eq_mul]
  split_ifs <;> first | omega | norm_num

end RationalBridges



end CausalNonpurifiability
