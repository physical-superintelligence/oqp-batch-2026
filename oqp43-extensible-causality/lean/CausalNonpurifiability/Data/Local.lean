module

public import Mathlib

@[expose] public section


/-!
# `CausalNonpurifiability.Data.Local`

Rational data of the construction in every port dimension: the local matrices
$P_r, Z_r, X_r, Z_r^+, θ_r$ (`eq:local-data`), the directions $Π, G_A, G_B$
(`eq:directions`), the centers $W_0, W_c$ (`eq:centers`), the ordered operators
$U, V$ (`eq:UV`), the signed input $C$ (`eq:C`), the input embedding $Q_C$
(`eq:QC`) and the witness $S_0$ (`eq:witness`), all as
Kronecker products on party-grouped indices `(Fin m × Fin d) × (Fin n × Fin e)`
in physical order `A_I, A_O, B_I, B_O`.

Design choices.
* Every local matrix is defined on `Fin r` for **every** `r` by value tests on the
  index (`i.val = 0`, `i.val = 1`); the manuscript's standing hypothesis `r ≥ 2`
  appears only on the lemmas that need it (traces of `Z_r`, `X_r^2 = P_r`, …).
  This avoids `Fin (k+2)` casts and matches `Ports` directly.
* Rational partial traces / replacement maps (`ptrA`, `ptrB`, `omegaAq`, `omegaBq`,
  `RAOq`, `RBOq`) are implemented entrywise (sum over the common basis index) from
  `eq:replacement` and `eq:ordered-marginal`; the manuscript states no entry rule for them. They are the
  rational shadows of the complex-linear maps; the bridge lemmas
  `toC (RBOq T) = R_BO (toC T)` are `toC_RBOq`, `toC_RAOq` (`Certificates/Qubit.lean`).
* `toC` is the entrywise rational-to-complex image.
-/

set_option autoImplicit false

namespace CausalNonpurifiability

open Matrix
open scoped Kronecker

/-! ### Index type and complex image -/

/-- Party-grouped lab index in physical order `A_I, A_O, B_I, B_O` with explicit port
dimensions `(m, d, n, e)`; definitionally `LabIndex D`. -/
abbrev Lab (m d n e : ℕ) : Type := (Fin m × Fin d) × (Fin n × Fin e)

/-- Entrywise rational-to-complex image `A ↦ A.map (algebraMap ℚ ℂ)`. -/
noncomputable abbrev toC {ι κ : Type*} (A : Matrix ι κ ℚ) : Matrix ι κ ℂ := A.map (algebraMap ℚ ℂ)

@[simp] lemma toC_apply {ι κ : Type*} (A : Matrix ι κ ℚ) (i : ι) (j : κ) :
    toC A i j = ((A i j : ℚ) : ℂ) := by
  simp [toC]

lemma toC_add {ι κ : Type*} (A B : Matrix ι κ ℚ) : toC (A + B) = toC A + toC B := by
  ext i j; simp

lemma toC_sub {ι κ : Type*} (A B : Matrix ι κ ℚ) : toC (A - B) = toC A - toC B := by
  ext i j; simp

lemma toC_smul {ι κ : Type*} (c : ℚ) (A : Matrix ι κ ℚ) : toC (c • A) = ((c : ℚ) : ℂ) • toC A := by
  ext i j; simp

lemma toC_one {ι : Type*} [DecidableEq ι] : toC (1 : Matrix ι ι ℚ) = 1 := by
  ext i j; simp only [toC_apply, Matrix.one_apply]; split_ifs <;> simp

lemma toC_diagonal {ι : Type*} [DecidableEq ι] (f : ι → ℚ) :
    toC (diagonal f) = diagonal fun i => ((f i : ℚ) : ℂ) := by
  ext i j; simp only [toC_apply, diagonal_apply]; split_ifs <;> simp

/-! ### Local rational data (`eq:local-data`, `eq:witness`) -/

/-- Matrix unit `|k⟩⟨k|` on `Fin r` (zero when `k ≥ r`). -/
def proj (r k : ℕ) : Matrix (Fin r) (Fin r) ℚ :=
  diagonal fun i => if i.val = k then 1 else 0

/-- Matrix unit `|k⟩⟨l|` on `Fin r` (zero when `k ≥ r` or `l ≥ r`). -/
def unit (r k l : ℕ) : Matrix (Fin r) (Fin r) ℚ :=
  of fun i j => if i.val = k ∧ j.val = l then 1 else 0

/-- `P_r = |0⟩⟨0| + |1⟩⟨1|` (`eq:local-data`). -/
def P (r : ℕ) : Matrix (Fin r) (Fin r) ℚ := proj r 0 + proj r 1

/-- `Z_r = |0⟩⟨0| - |1⟩⟨1|` (`eq:local-data`), supported on `P_r`. -/
def Z (r : ℕ) : Matrix (Fin r) (Fin r) ℚ := proj r 0 - proj r 1

/-- `X_r = |0⟩⟨1| + |1⟩⟨0|` (`eq:local-data`). -/
def X (r : ℕ) : Matrix (Fin r) (Fin r) ℚ := unit r 0 1 + unit r 1 0

/-- `Z_r^+ = I_r - 2|1⟩⟨1|` (`eq:local-data`), an involution on the whole space. -/
def Zplus (r : ℕ) : Matrix (Fin r) (Fin r) ℚ := 1 - (2 : ℚ) • proj r 1

/-- `θ_r = (3|0⟩⟨0| + |1⟩⟨1|)/4` (`eq:local-data`). -/
def theta (r : ℕ) : Matrix (Fin r) (Fin r) ℚ := (1 / 4 : ℚ) • ((3 : ℚ) • proj r 0 + proj r 1)

/-- `D_n = I_n + 8|1⟩⟨1|` (`eq:witness`). -/
def Dw (r : ℕ) : Matrix (Fin r) (Fin r) ℚ := 1 + (8 : ℚ) • proj r 1

/-! #### Diagonal normal forms -/

lemma proj_eq (r k : ℕ) : proj r k = diagonal fun i => if i.val = k then 1 else 0 := rfl

lemma P_eq (r : ℕ) :
    P r = diagonal fun i => if i.val = 0 ∨ i.val = 1 then 1 else 0 := by
  ext i j
  simp only [P, proj, Matrix.add_apply, diagonal_apply]
  split_ifs <;> first | omega | norm_num

lemma Z_eq (r : ℕ) :
    Z r = diagonal fun i => if i.val = 0 then 1 else if i.val = 1 then -1 else 0 := by
  ext i j
  simp only [Z, proj, Matrix.sub_apply, diagonal_apply]
  split_ifs <;> first | omega | norm_num

lemma Zplus_eq (r : ℕ) : Zplus r = diagonal fun i => if i.val = 1 then -1 else 1 := by
  ext i j
  simp only [Zplus, proj, Matrix.sub_apply, Matrix.smul_apply, one_apply, diagonal_apply, smul_eq_mul]
  split_ifs <;> first | omega | norm_num

lemma theta_eq (r : ℕ) :
    theta r = diagonal fun i => if i.val = 0 then 3 / 4 else if i.val = 1 then 1 / 4 else 0 := by
  ext i j
  simp only [theta, proj, Matrix.smul_apply, Matrix.add_apply, diagonal_apply, smul_eq_mul]
  split_ifs <;> first | omega | norm_num

lemma Dw_eq (r : ℕ) : Dw r = diagonal fun i => if i.val = 1 then 9 else 1 := by
  ext i j
  simp only [Dw, proj, Matrix.add_apply, Matrix.smul_apply, one_apply, diagonal_apply, smul_eq_mul]
  split_ifs <;> first | omega | norm_num

@[simp] lemma X_apply (r : ℕ) (i j : Fin r) :
    X r i j = if (i.val = 0 ∧ j.val = 1) ∨ (i.val = 1 ∧ j.val = 0) then 1 else 0 := by
  simp only [X, unit, Matrix.add_apply, of_apply]
  split_ifs <;> first | omega | norm_num

lemma X_transpose (r : ℕ) : (X r)ᵀ = X r := by
  ext i j
  simp only [transpose_apply, X_apply]
  split_ifs <;> first | omega | norm_num

lemma P_transpose (r : ℕ) : (P r)ᵀ = P r := by rw [P_eq, diagonal_transpose]
lemma Z_transpose (r : ℕ) : (Z r)ᵀ = Z r := by rw [Z_eq, diagonal_transpose]
lemma Zplus_transpose (r : ℕ) : (Zplus r)ᵀ = Zplus r := by rw [Zplus_eq, diagonal_transpose]
lemma theta_transpose (r : ℕ) : (theta r)ᵀ = theta r := by rw [theta_eq, diagonal_transpose]
lemma proj_transpose (r k : ℕ) : (proj r k)ᵀ = proj r k := by rw [proj_eq, diagonal_transpose]
lemma Dw_transpose (r : ℕ) : (Dw r)ᵀ = Dw r := by rw [Dw_eq, diagonal_transpose]

/-! #### Sums over `Fin r` supported on the two distinguished basis vectors -/

/-- A sum over `Fin r`, `r ≥ 2`, of a function vanishing above index `1` has two terms. -/
lemma sum_fin_of_two_le {r : ℕ} (hr : 2 ≤ r) (f : Fin r → ℚ)
    (hf : ∀ i : Fin r, 2 ≤ i.val → f i = 0) :
    ∑ i, f i = f ⟨0, by omega⟩ + f ⟨1, by omega⟩ := by
  obtain ⟨k, rfl⟩ : ∃ k, r = k + 2 := ⟨r - 2, by omega⟩
  rw [Fin.sum_univ_succ, Fin.sum_univ_succ,
    Finset.sum_eq_zero (fun i _ => hf _ (by simp [Fin.val_succ]))]
  have h0 : (⟨0, by omega⟩ : Fin (k + 2)) = 0 := Fin.ext (by simp)
  have h1 : (⟨1, by omega⟩ : Fin (k + 2)) = 1 := Fin.ext (by simp)
  rw [h0, h1, Fin.succ_zero_eq_one, add_zero]

/-! #### Local algebra (products) -/

section LocalAlgebra
variable {r : ℕ}

lemma P_mul_P : P r * P r = P r := by
  rw [P_eq, diagonal_mul_diagonal]; congr 1; funext i; split_ifs <;> first | omega | norm_num

lemma Z_mul_Z : Z r * Z r = P r := by
  rw [Z_eq, P_eq, diagonal_mul_diagonal]; congr 1; funext i
  split_ifs <;> first | omega | norm_num

lemma Zplus_mul_Zplus : Zplus r * Zplus r = 1 := by
  rw [Zplus_eq, diagonal_mul_diagonal, ← diagonal_one]; congr 1; funext i
  split_ifs <;> first | omega | norm_num

lemma P_mul_Z : P r * Z r = Z r := by
  rw [P_eq, Z_eq, diagonal_mul_diagonal]; congr 1; funext i
  split_ifs <;> first | omega | norm_num

lemma Z_mul_P : Z r * P r = Z r := by
  rw [P_eq, Z_eq, diagonal_mul_diagonal]; congr 1; funext i
  split_ifs <;> first | omega | norm_num

lemma P_mul_X : P r * X r = X r := by
  ext i j
  rw [P_eq, diagonal_mul, X_apply]
  split_ifs <;> first | omega | norm_num

lemma X_mul_P : X r * P r = X r := by
  ext i j
  rw [P_eq, mul_diagonal, X_apply]
  split_ifs <;> first | omega | norm_num

lemma X_mul_X (hr : 2 ≤ r) : X r * X r = P r := by
  obtain ⟨k, rfl⟩ : ∃ k, r = k + 2 := ⟨r - 2, by omega⟩
  ext i j
  rw [P_eq, mul_apply, Fin.sum_univ_succ, Fin.sum_univ_succ, Finset.sum_eq_zero]
  · simp only [X_apply, diagonal_apply, Fin.val_zero, Fin.val_one, Fin.succ_zero_eq_one,
      add_zero, Nat.zero_ne_one, Nat.one_ne_zero, true_and, and_true, false_and, and_false,
      or_false, false_or]
    split_ifs <;> (try simp only [Fin.ext_iff] at *) <;> first | omega | norm_num
  · intro x _
    simp [X_apply, Fin.val_succ]

/-- `D_n (I_n - Z_n^+) = 18|1⟩⟨1|` (block of `eq:witness-replacements`). -/
lemma Dw_mul_one_sub_Zplus : Dw r * (1 - Zplus r) = (18 : ℚ) • proj r 1 := by
  ext i j
  rw [Dw_eq, diagonal_mul]
  simp only [Zplus_eq, proj_eq, Matrix.sub_apply, one_apply, diagonal_apply, Matrix.smul_apply,
    smul_eq_mul]
  split_ifs <;> first | omega | norm_num

/-- `D_n (I_n + Z_n^+) = 2(I_n - |1⟩⟨1|)` (block of `eq:witness-replacements`). -/
lemma Dw_mul_one_add_Zplus : Dw r * (1 + Zplus r) = (2 : ℚ) • (1 - proj r 1) := by
  ext i j
  rw [Dw_eq, diagonal_mul]
  simp only [Zplus_eq, proj_eq, Matrix.add_apply, Matrix.sub_apply, one_apply, diagonal_apply,
    Matrix.smul_apply, smul_eq_mul]
  split_ifs <;> first | omega | norm_num

end LocalAlgebra

/-! #### Local traces (all with the standing hypothesis `r ≥ 2`) -/

section LocalTraces
variable {r : ℕ}

lemma trace_P (hr : 2 ≤ r) : trace (P r) = 2 := by
  rw [P_eq, trace_diagonal, sum_fin_of_two_le hr]
  · norm_num
  · intro i hi; split_ifs <;> first | omega | norm_num

lemma trace_Z (hr : 2 ≤ r) : trace (Z r) = 0 := by
  rw [Z_eq, trace_diagonal, sum_fin_of_two_le hr]
  · norm_num
  · intro i hi; split_ifs <;> first | omega | norm_num

lemma trace_theta (hr : 2 ≤ r) : trace (theta r) = 1 := by
  rw [theta_eq, trace_diagonal, sum_fin_of_two_le hr]
  · norm_num
  · intro i hi; split_ifs <;> first | omega | norm_num

lemma trace_proj1_mul_theta (hr : 2 ≤ r) : trace (proj r 1 * theta r) = 1 / 4 := by
  rw [proj_eq, theta_eq, diagonal_mul_diagonal, trace_diagonal,
    sum_fin_of_two_le hr]
  · norm_num
  · intro i hi; split_ifs <;> first | omega | norm_num

lemma trace_Dw_mul_theta (hr : 2 ≤ r) : trace (Dw r * theta r) = 3 := by
  rw [Dw_eq, theta_eq, diagonal_mul_diagonal, trace_diagonal,
    sum_fin_of_two_le hr]
  · norm_num
  · intro i hi; split_ifs <;> first | omega | norm_num

lemma trace_proj1_mul_P (hr : 2 ≤ r) : trace (proj r 1 * P r) = 1 := by
  rw [proj_eq, P_eq, diagonal_mul_diagonal, trace_diagonal,
    sum_fin_of_two_le hr]
  · norm_num
  · intro i hi; split_ifs <;> first | omega | norm_num

lemma trace_proj1_mul_Z (hr : 2 ≤ r) : trace (proj r 1 * Z r) = -1 := by
  rw [proj_eq, Z_eq, diagonal_mul_diagonal, trace_diagonal,
    sum_fin_of_two_le hr]
  · norm_num
  · intro i hi; split_ifs <;> first | omega | norm_num

lemma trace_P_mul_Zplus (hr : 2 ≤ r) : trace (P r * Zplus r) = 0 := by
  rw [P_eq, Zplus_eq, diagonal_mul_diagonal, trace_diagonal,
    sum_fin_of_two_le hr]
  · norm_num
  · intro i hi; split_ifs <;> first | omega | norm_num

lemma trace_Z_mul_Zplus (hr : 2 ≤ r) : trace (Z r * Zplus r) = 2 := by
  rw [Z_eq, Zplus_eq, diagonal_mul_diagonal, trace_diagonal,
    sum_fin_of_two_le hr]
  · norm_num
  · intro i hi; split_ifs <;> first | omega | norm_num

lemma trace_Dw_mul_Zplus_mul_Z (hr : 2 ≤ r) : trace (Dw r * Zplus r * Z r) = 10 := by
  rw [Dw_eq, Zplus_eq, Z_eq, diagonal_mul_diagonal, diagonal_mul_diagonal, trace_diagonal,
    sum_fin_of_two_le hr]
  · norm_num
  · intro i hi; split_ifs <;> first | omega | norm_num

lemma trace_Dw_mul_X : trace (Dw r * X r) = 0 := by
  rw [Dw_eq]
  simp only [trace, diag_apply, diagonal_mul, X_apply]
  exact Finset.sum_eq_zero fun i _ => by split_ifs <;> first | omega | norm_num

lemma trace_X : trace (X r) = 0 := by
  simp only [trace, diag_apply, X_apply]
  exact Finset.sum_eq_zero fun i _ => by split_ifs <;> first | omega | norm_num

lemma trace_X_mul_X (hr : 2 ≤ r) : trace (X r * X r) = 2 := by
  rw [X_mul_X hr, trace_P hr]

lemma trace_one_fin : trace (1 : Matrix (Fin r) (Fin r) ℚ) = r := by
  simp [trace_one]

end LocalTraces

/-! ### Four-factor Kronecker products on party-grouped indices -/

/-- `A ⊗ B ⊗ C ⊗ D` in port order `A_I, A_O, B_I, B_O`, grouped as `(A ⊗ B) ⊗ (C ⊗ D)`. -/
def kron4 {m d n e : ℕ} (A : Matrix (Fin m) (Fin m) ℚ) (B : Matrix (Fin d) (Fin d) ℚ)
    (C : Matrix (Fin n) (Fin n) ℚ) (D : Matrix (Fin e) (Fin e) ℚ) :
    Matrix (Lab m d n e) (Lab m d n e) ℚ :=
  (A ⊗ₖ B) ⊗ₖ (C ⊗ₖ D)

section Kron4
variable {m d n e : ℕ}

@[simp] lemma kron4_apply (A : Matrix (Fin m) (Fin m) ℚ) (B : Matrix (Fin d) (Fin d) ℚ)
    (C : Matrix (Fin n) (Fin n) ℚ) (D : Matrix (Fin e) (Fin e) ℚ) (x y : Lab m d n e) :
    kron4 A B C D x y = (A x.1.1 y.1.1 * B x.1.2 y.1.2) * (C x.2.1 y.2.1 * D x.2.2 y.2.2) := rfl

lemma kron4_mul_kron4 (A A' : Matrix (Fin m) (Fin m) ℚ) (B B' : Matrix (Fin d) (Fin d) ℚ)
    (C C' : Matrix (Fin n) (Fin n) ℚ) (D D' : Matrix (Fin e) (Fin e) ℚ) :
    kron4 A B C D * kron4 A' B' C' D' = kron4 (A * A') (B * B') (C * C') (D * D') := by
  simp only [kron4, ← mul_kronecker_mul]

lemma trace_kron4 (A : Matrix (Fin m) (Fin m) ℚ) (B : Matrix (Fin d) (Fin d) ℚ)
    (C : Matrix (Fin n) (Fin n) ℚ) (D : Matrix (Fin e) (Fin e) ℚ) :
    trace (kron4 A B C D) = trace A * trace B * (trace C * trace D) := by
  simp only [kron4, trace_kronecker]

lemma kron4_transpose (A : Matrix (Fin m) (Fin m) ℚ) (B : Matrix (Fin d) (Fin d) ℚ)
    (C : Matrix (Fin n) (Fin n) ℚ) (D : Matrix (Fin e) (Fin e) ℚ) :
    (kron4 A B C D)ᵀ = kron4 Aᵀ Bᵀ Cᵀ Dᵀ := by
  simp only [kron4, kroneckerMap_transpose]

lemma toC_kron4 (A : Matrix (Fin m) (Fin m) ℚ) (B : Matrix (Fin d) (Fin d) ℚ)
    (C : Matrix (Fin n) (Fin n) ℚ) (D : Matrix (Fin e) (Fin e) ℚ) :
    toC (kron4 A B C D) = (toC A ⊗ₖ toC B) ⊗ₖ (toC C ⊗ₖ toC D) := by
  ext x y
  simp [kroneckerMap_apply]

lemma kron4_add₂ (A : Matrix (Fin m) (Fin m) ℚ) (B B' : Matrix (Fin d) (Fin d) ℚ)
    (C : Matrix (Fin n) (Fin n) ℚ) (D : Matrix (Fin e) (Fin e) ℚ) :
    kron4 A (B + B') C D = kron4 A B C D + kron4 A B' C D := by
  ext x y; simp [kron4_apply]; ring

lemma kron4_sub₂ (A : Matrix (Fin m) (Fin m) ℚ) (B B' : Matrix (Fin d) (Fin d) ℚ)
    (C : Matrix (Fin n) (Fin n) ℚ) (D : Matrix (Fin e) (Fin e) ℚ) :
    kron4 A (B - B') C D = kron4 A B C D - kron4 A B' C D := by
  ext x y; simp [kron4_apply]; ring

lemma kron4_add₃ (A : Matrix (Fin m) (Fin m) ℚ) (B : Matrix (Fin d) (Fin d) ℚ)
    (C C' : Matrix (Fin n) (Fin n) ℚ) (D : Matrix (Fin e) (Fin e) ℚ) :
    kron4 A B (C + C') D = kron4 A B C D + kron4 A B C' D := by
  ext x y; simp [kron4_apply]; ring

lemma kron4_sub₃ (A : Matrix (Fin m) (Fin m) ℚ) (B : Matrix (Fin d) (Fin d) ℚ)
    (C C' : Matrix (Fin n) (Fin n) ℚ) (D : Matrix (Fin e) (Fin e) ℚ) :
    kron4 A B (C - C') D = kron4 A B C D - kron4 A B C' D := by
  ext x y; simp [kron4_apply]; ring

lemma kron4_add₄ (A : Matrix (Fin m) (Fin m) ℚ) (B : Matrix (Fin d) (Fin d) ℚ)
    (C : Matrix (Fin n) (Fin n) ℚ) (D D' : Matrix (Fin e) (Fin e) ℚ) :
    kron4 A B C (D + D') = kron4 A B C D + kron4 A B C D' := by
  ext x y; simp [kron4_apply]; ring

lemma kron4_sub₄ (A : Matrix (Fin m) (Fin m) ℚ) (B : Matrix (Fin d) (Fin d) ℚ)
    (C : Matrix (Fin n) (Fin n) ℚ) (D D' : Matrix (Fin e) (Fin e) ℚ) :
    kron4 A B C (D - D') = kron4 A B C D - kron4 A B C D' := by
  ext x y; simp [kron4_apply]; ring

lemma kron4_smul₁ (c : ℚ) (A : Matrix (Fin m) (Fin m) ℚ) (B : Matrix (Fin d) (Fin d) ℚ)
    (C : Matrix (Fin n) (Fin n) ℚ) (D : Matrix (Fin e) (Fin e) ℚ) :
    kron4 (c • A) B C D = c • kron4 A B C D := by
  ext x y; simp [kron4_apply]; ring

lemma kron4_smul₃ (c : ℚ) (A : Matrix (Fin m) (Fin m) ℚ) (B : Matrix (Fin d) (Fin d) ℚ)
    (C : Matrix (Fin n) (Fin n) ℚ) (D : Matrix (Fin e) (Fin e) ℚ) :
    kron4 A B (c • C) D = c • kron4 A B C D := by
  ext x y; simp [kron4_apply]; ring

end Kron4

/-! ### Directions, centers, ordered operators, signed input, witness -/

section Construction
variable (m d n e : ℕ)

/-- `Π = P_m ⊗ I_d ⊗ P_n ⊗ I_e` (`eq:directions`). -/
def Pi : Matrix (Lab m d n e) (Lab m d n e) ℚ := kron4 (P m) 1 (P n) 1

/-- `G_A = P_m ⊗ Z_d^+ ⊗ Z_n ⊗ I_e` (`eq:directions`). -/
def GA : Matrix (Lab m d n e) (Lab m d n e) ℚ := kron4 (P m) (Zplus d) (Z n) 1

/-- `G_B = Z_m ⊗ I_d ⊗ X_n ⊗ Z_e^+` (`eq:directions`). -/
def GB : Matrix (Lab m d n e) (Lab m d n e) ℚ := kron4 (Z m) 1 (X n) (Zplus e)

variable {m n}

/-- Input embedding `Q_C = C^{A_I B_I} ⊗ I^{A_O B_O}` (`eq:QC`) with the literal entry rule
`(Q_C)_{(a,o,b,t),(a',o',b',t')} = C_{(a,b),(a',b')} δ_{oo'} δ_{tt'}` (Appendix C). -/
def Qembed (C : Matrix (Fin m × Fin n) (Fin m × Fin n) ℚ) :
    Matrix (Lab m d n e) (Lab m d n e) ℚ :=
  of fun x y =>
    C (x.1.1, x.2.1) (y.1.1, y.2.1) * (if x.1.2 = y.1.2 then 1 else 0) *
      (if x.2.2 = y.2.2 then 1 else 0)

variable (m n)

/-- `Q_{θ_m ⊗ θ_n}` (`eq:centers`). -/
def Qtheta : Matrix (Lab m d n e) (Lab m d n e) ℚ := Qembed d e (theta m ⊗ₖ theta n)

/-- `W_0 = Q_{θ_m⊗θ_n} + (G_A + G_B)/20` (`eq:centers`). -/
def W0 : Matrix (Lab m d n e) (Lab m d n e) ℚ :=
  Qtheta m d n e + (1 / 20 : ℚ) • (GA m d n e + GB m d n e)

/-- `W_c = (99/100) W_0 + (1/100) I_{mdne}/(mn)` (`eq:centers`). -/
def Wc : Matrix (Lab m d n e) (Lab m d n e) ℚ :=
  (99 / 100 : ℚ) • W0 m d n e + (1 / 100 : ℚ) • ((1 : ℚ) / ((m : ℚ) * n)) • 1

/-- `U = (Π + G_A)/20` (`eq:UV`). -/
def U : Matrix (Lab m d n e) (Lab m d n e) ℚ := (1 / 20 : ℚ) • (Pi m d n e + GA m d n e)

/-- `V = (Π + G_B)/20` (`eq:UV`). -/
def V : Matrix (Lab m d n e) (Lab m d n e) ℚ := (1 / 20 : ℚ) • (Pi m d n e + GB m d n e)

/-- `C = (37|00⟩⟨00| + 7|01⟩⟨01| + 7|10⟩⟨10| - 3|11⟩⟨11|)/160` on `A_I B_I` (`eq:C`). -/
def C : Matrix (Fin m × Fin n) (Fin m × Fin n) ℚ :=
  (1 / 160 : ℚ) • ((37 : ℚ) • (proj m 0 ⊗ₖ proj n 0) + (7 : ℚ) • (proj m 0 ⊗ₖ proj n 1)
    + (7 : ℚ) • (proj m 1 ⊗ₖ proj n 0) - (3 : ℚ) • (proj m 1 ⊗ₖ proj n 1))

/-- The witness
`S_0 = P_1 ⊗ P_d ⊗ D_n ⊗ P_e - P_1 ⊗ Z_d ⊗ D_n Z_n^+ ⊗ P_e + 3 P_1 ⊗ P_d ⊗ X_n ⊗ Z_e`
(`eq:witness`), with `P_1 = |1⟩⟨1|` on `A_I` and `D_n = I_n + 8|1⟩⟨1|`. -/
def S0 : Matrix (Lab m d n e) (Lab m d n e) ℚ :=
  kron4 (proj m 1) (P d) (Dw n) (P e) - kron4 (proj m 1) (Z d) (Dw n * Zplus n) (P e)
    + (3 : ℚ) • kron4 (proj m 1) (P d) (X n) (Z e)

end Construction

/-! ### Rational partial traces and replacement maps (entrywise, in the basis `|i,o,j,t⟩` of Appendix C; the formulas are `eq:replacement` and `eq:ordered-marginal`; the manuscript states no
entry rule for them) -/

section PartialTraces
variable {m d n e : ℕ}

/-- `C_A = Tr_{B_I} C` on `A_I B_I` (entry rule: sum over the common `B_I` index). -/
def ptrB (C : Matrix (Fin m × Fin n) (Fin m × Fin n) ℚ) : Matrix (Fin m) (Fin m) ℚ :=
  of fun a a' => ∑ b, C (a, b) (a', b)

/-- `C_B = Tr_{A_I} C` on `A_I B_I`. -/
def ptrA (C : Matrix (Fin m × Fin n) (Fin m × Fin n) ℚ) : Matrix (Fin n) (Fin n) ℚ :=
  of fun b b' => ∑ a, C (a, b) (a, b')

/-- `ω_A(T) = Tr_{A_O B_I B_O} T / (de)` (`eq:ordered-marginal`), rational coordinates. -/
def omegaAq (T : Matrix (Lab m d n e) (Lab m d n e) ℚ) : Matrix (Fin m) (Fin m) ℚ :=
  (1 / ((d : ℚ) * e)) • of fun a a' => ∑ o, ∑ b, ∑ t, T ((a, o), (b, t)) ((a', o), (b, t))

/-- `ω_B(T) = Tr_{A_I A_O B_O} T / (de)` (`eq:ordered-marginal`), rational coordinates. -/
def omegaBq (T : Matrix (Lab m d n e) (Lab m d n e) ℚ) : Matrix (Fin n) (Fin n) ℚ :=
  (1 / ((d : ℚ) * e)) • of fun b b' => ∑ a, ∑ o, ∑ t, T ((a, o), (b, t)) ((a, o), (b', t))

/-- Rational replacement of `B_O`: `R_{B_O}(T)_{(x,t),(y,t')} = δ_{tt'} (Tr_{B_O} T)_{xy}/e`
(`eq:replacement`). -/
def RBOq (T : Matrix (Lab m d n e) (Lab m d n e) ℚ) : Matrix (Lab m d n e) (Lab m d n e) ℚ :=
  of fun x y =>
    (if x.2.2 = y.2.2 then 1 else 0) *
      (∑ s, T ((x.1.1, x.1.2), (x.2.1, s)) ((y.1.1, y.1.2), (y.2.1, s))) / e

/-- Rational replacement of `A_O`: `R_{A_O}(T)_{(a,o,z),(a',o',z')} = δ_{oo'} (Tr_{A_O} T)/d`
(`eq:replacement`). -/
def RAOq (T : Matrix (Lab m d n e) (Lab m d n e) ℚ) : Matrix (Lab m d n e) (Lab m d n e) ℚ :=
  of fun x y =>
    (if x.1.2 = y.1.2 then 1 else 0) *
      (∑ s, T ((x.1.1, s), (x.2.1, x.2.2)) ((y.1.1, s), (y.2.1, y.2.2))) / d

/-- Rational replacement of `B_I B_O`: `R_{B_IB_O}(T)_{(x,z),(y,z')} = δ_{zz'} (Tr_{B_IB_O} T)_{xy}/(ne)`
(`eq:replacement`). -/
def RBIBOq (T : Matrix (Lab m d n e) (Lab m d n e) ℚ) : Matrix (Lab m d n e) (Lab m d n e) ℚ :=
  of fun x y =>
    (if x.2 = y.2 then 1 else 0) * (∑ z : Fin n × Fin e, T (x.1, z) (y.1, z)) / ((n : ℚ) * e)

/-- Rational replacement of `A_I A_O`: `R_{A_IA_O}(T)_{(z,x),(z',y)} = δ_{zz'} (Tr_{A_IA_O} T)_{xy}/(md)`
(`eq:replacement`). -/
def RAIAOq (T : Matrix (Lab m d n e) (Lab m d n e) ℚ) : Matrix (Lab m d n e) (Lab m d n e) ℚ :=
  of fun x y =>
    (if x.1 = y.1 then 1 else 0) * (∑ z : Fin m × Fin d, T (z, x.2) (z, y.2)) / ((m : ℚ) * d)

/-- Triple sums of products factor. -/
lemma sum3_factor {d n e : ℕ} (x : ℚ) (f : Fin d → ℚ) (g : Fin n → ℚ) (h : Fin e → ℚ) :
    ∑ o, ∑ b, ∑ t, (x * f o) * (g b * h t) = x * ((∑ o, f o) * ((∑ b, g b) * (∑ t, h t))) := by
  rw [Finset.sum_mul_sum, Finset.sum_mul_sum]
  simp only [Finset.mul_sum, mul_assoc]

lemma omegaAq_kron4 (A : Matrix (Fin m) (Fin m) ℚ) (B : Matrix (Fin d) (Fin d) ℚ)
    (C : Matrix (Fin n) (Fin n) ℚ) (D : Matrix (Fin e) (Fin e) ℚ) :
    omegaAq (kron4 A B C D) = ((trace B * (trace C * trace D)) / ((d : ℚ) * e)) • A := by
  ext a a'
  simp only [omegaAq, Matrix.smul_apply, of_apply, kron4_apply, smul_eq_mul, trace, diag_apply]
  rw [sum3_factor]
  ring

lemma omegaBq_kron4 (A : Matrix (Fin m) (Fin m) ℚ) (B : Matrix (Fin d) (Fin d) ℚ)
    (C : Matrix (Fin n) (Fin n) ℚ) (D : Matrix (Fin e) (Fin e) ℚ) :
    omegaBq (kron4 A B C D) = ((trace A * (trace B * trace D)) / ((d : ℚ) * e)) • C := by
  ext b b'
  simp only [omegaBq, Matrix.smul_apply, of_apply, kron4_apply, smul_eq_mul, trace, diag_apply]
  have : ∀ (a : Fin m) (o : Fin d) (t : Fin e),
      A a a * B o o * (C b b' * D t t) = (C b b' * A a a) * (B o o * D t t) := by
    intro a o t; ring
  simp only [this, sum3_factor]
  ring

lemma omegaAq_add (T T' : Matrix (Lab m d n e) (Lab m d n e) ℚ) :
    omegaAq (T + T') = omegaAq T + omegaAq T' := by
  ext a a'
  simp only [omegaAq, Matrix.smul_apply, of_apply, Matrix.add_apply, Finset.sum_add_distrib, smul_eq_mul]
  ring

lemma omegaAq_smul (c : ℚ) (T : Matrix (Lab m d n e) (Lab m d n e) ℚ) :
    omegaAq (c • T) = c • omegaAq T := by
  ext a a'
  simp only [omegaAq, Matrix.smul_apply, of_apply, smul_eq_mul, ← Finset.mul_sum]
  ring

lemma omegaBq_add (T T' : Matrix (Lab m d n e) (Lab m d n e) ℚ) :
    omegaBq (T + T') = omegaBq T + omegaBq T' := by
  ext b b'
  simp only [omegaBq, Matrix.smul_apply, of_apply, Matrix.add_apply, Finset.sum_add_distrib, smul_eq_mul]
  ring

lemma omegaBq_smul (c : ℚ) (T : Matrix (Lab m d n e) (Lab m d n e) ℚ) :
    omegaBq (c • T) = c • omegaBq T := by
  ext b b'
  simp only [omegaBq, Matrix.smul_apply, of_apply, smul_eq_mul, ← Finset.mul_sum]
  ring

lemma RBOq_kron4 (A : Matrix (Fin m) (Fin m) ℚ) (B : Matrix (Fin d) (Fin d) ℚ)
    (C : Matrix (Fin n) (Fin n) ℚ) (D : Matrix (Fin e) (Fin e) ℚ) :
    RBOq (kron4 A B C D) = (trace D / e) • kron4 A B C 1 := by
  ext x y
  simp only [RBOq, of_apply, kron4_apply, Matrix.smul_apply, smul_eq_mul, trace, diag_apply,
    one_apply, ← Finset.mul_sum]
  split_ifs <;> ring

lemma RAOq_kron4 (A : Matrix (Fin m) (Fin m) ℚ) (B : Matrix (Fin d) (Fin d) ℚ)
    (C : Matrix (Fin n) (Fin n) ℚ) (D : Matrix (Fin e) (Fin e) ℚ) :
    RAOq (kron4 A B C D) = (trace B / d) • kron4 A 1 C D := by
  ext x y
  simp only [RAOq, of_apply, kron4_apply, Matrix.smul_apply, smul_eq_mul, trace, diag_apply,
    one_apply, ← Finset.sum_mul, ← Finset.mul_sum]
  split_ifs <;> ring

lemma RBOq_add (T T' : Matrix (Lab m d n e) (Lab m d n e) ℚ) :
    RBOq (T + T') = RBOq T + RBOq T' := by
  ext x y
  simp only [RBOq, of_apply, Matrix.add_apply, Finset.sum_add_distrib]
  ring

lemma RBOq_sub (T T' : Matrix (Lab m d n e) (Lab m d n e) ℚ) :
    RBOq (T - T') = RBOq T - RBOq T' := by
  ext x y
  simp only [RBOq, of_apply, Matrix.sub_apply, Finset.sum_sub_distrib]
  ring

lemma RBOq_smul (c : ℚ) (T : Matrix (Lab m d n e) (Lab m d n e) ℚ) :
    RBOq (c • T) = c • RBOq T := by
  ext x y
  simp only [RBOq, of_apply, Matrix.smul_apply, smul_eq_mul, ← Finset.mul_sum]
  ring

lemma RAOq_add (T T' : Matrix (Lab m d n e) (Lab m d n e) ℚ) :
    RAOq (T + T') = RAOq T + RAOq T' := by
  ext x y
  simp only [RAOq, of_apply, Matrix.add_apply, Finset.sum_add_distrib]
  ring

lemma RAOq_sub (T T' : Matrix (Lab m d n e) (Lab m d n e) ℚ) :
    RAOq (T - T') = RAOq T - RAOq T' := by
  ext x y
  simp only [RAOq, of_apply, Matrix.sub_apply, Finset.sum_sub_distrib]
  ring

lemma RAOq_smul (c : ℚ) (T : Matrix (Lab m d n e) (Lab m d n e) ℚ) :
    RAOq (c • T) = c • RAOq T := by
  ext x y
  simp only [RAOq, of_apply, Matrix.smul_apply, smul_eq_mul, ← Finset.mul_sum]
  ring

lemma RBIBOq_kron4 (A : Matrix (Fin m) (Fin m) ℚ) (B : Matrix (Fin d) (Fin d) ℚ)
    (C : Matrix (Fin n) (Fin n) ℚ) (D : Matrix (Fin e) (Fin e) ℚ) :
    RBIBOq (kron4 A B C D) = ((trace C * trace D) / ((n : ℚ) * e)) • kron4 A B 1 1 := by
  ext ⟨⟨a, o⟩, ⟨b, t⟩⟩ ⟨⟨a', o'⟩, ⟨b', t'⟩⟩
  simp only [RBIBOq, of_apply, kron4_apply, Matrix.smul_apply, smul_eq_mul, trace, diag_apply,
    one_apply, Fintype.sum_prod_type, ← Finset.mul_sum, ← Finset.sum_mul, Prod.mk.injEq]
  split_ifs <;> first | ring1 | (simp only [Fin.ext_iff] at *; omega)

lemma RAIAOq_kron4 (A : Matrix (Fin m) (Fin m) ℚ) (B : Matrix (Fin d) (Fin d) ℚ)
    (C : Matrix (Fin n) (Fin n) ℚ) (D : Matrix (Fin e) (Fin e) ℚ) :
    RAIAOq (kron4 A B C D) = ((trace A * trace B) / ((m : ℚ) * d)) • kron4 1 1 C D := by
  ext ⟨⟨a, o⟩, ⟨b, t⟩⟩ ⟨⟨a', o'⟩, ⟨b', t'⟩⟩
  simp only [RAIAOq, of_apply, kron4_apply, Matrix.smul_apply, smul_eq_mul, trace, diag_apply,
    one_apply, Fintype.sum_prod_type, ← Finset.sum_mul, ← Finset.mul_sum, Prod.mk.injEq]
  split_ifs <;> first | ring1 | (simp only [Fin.ext_iff] at *; omega)

lemma RBIBOq_add (T T' : Matrix (Lab m d n e) (Lab m d n e) ℚ) :
    RBIBOq (T + T') = RBIBOq T + RBIBOq T' := by
  ext x y
  simp only [RBIBOq, of_apply, Matrix.add_apply, Finset.sum_add_distrib]
  ring

lemma RBIBOq_smul (c : ℚ) (T : Matrix (Lab m d n e) (Lab m d n e) ℚ) :
    RBIBOq (c • T) = c • RBIBOq T := by
  ext x y
  simp only [RBIBOq, of_apply, Matrix.smul_apply, smul_eq_mul, ← Finset.mul_sum]
  ring

lemma RAIAOq_add (T T' : Matrix (Lab m d n e) (Lab m d n e) ℚ) :
    RAIAOq (T + T') = RAIAOq T + RAIAOq T' := by
  ext x y
  simp only [RAIAOq, of_apply, Matrix.add_apply, Finset.sum_add_distrib]
  ring

lemma RAIAOq_smul (c : ℚ) (T : Matrix (Lab m d n e) (Lab m d n e) ℚ) :
    RAIAOq (c • T) = c • RAIAOq T := by
  ext x y
  simp only [RAIAOq, of_apply, Matrix.smul_apply, smul_eq_mul, ← Finset.mul_sum]
  ring

lemma RBOq_zero : RBOq (0 : Matrix (Lab m d n e) (Lab m d n e) ℚ) = 0 := by
  ext x y; simp [RBOq]

lemma RAOq_zero : RAOq (0 : Matrix (Lab m d n e) (Lab m d n e) ℚ) = 0 := by
  ext x y; simp [RAOq]

end PartialTraces

/-! ### Structural identities for the directions and the embedding -/

section Structure
variable {m d n e : ℕ}

lemma Qembed_add (C C' : Matrix (Fin m × Fin n) (Fin m × Fin n) ℚ) :
    Qembed d e (C + C') = Qembed d e C + Qembed d e C' := by
  ext x y; simp only [Qembed, of_apply, Matrix.add_apply]; ring

lemma Qembed_sub (C C' : Matrix (Fin m × Fin n) (Fin m × Fin n) ℚ) :
    Qembed d e (C - C') = Qembed d e C - Qembed d e C' := by
  ext x y; simp only [Qembed, of_apply, Matrix.sub_apply]; ring

lemma Qembed_smul (c : ℚ) (C : Matrix (Fin m × Fin n) (Fin m × Fin n) ℚ) :
    Qembed d e (c • C) = c • Qembed d e C := by
  ext x y; simp only [Qembed, of_apply, Matrix.smul_apply, smul_eq_mul]; ring

/-- `Q_{A ⊗ B}` is the Kronecker product `A ⊗ I_d ⊗ B ⊗ I_e`. -/
lemma Qembed_kronecker (A : Matrix (Fin m) (Fin m) ℚ) (B : Matrix (Fin n) (Fin n) ℚ) :
    Qembed d e (A ⊗ₖ B) = kron4 A 1 B 1 := by
  ext x y
  simp only [Qembed, of_apply, kron4_apply, kroneckerMap_apply, one_apply]
  ring

lemma Pi_eq_Qembed : Pi m d n e = Qembed d e (P m ⊗ₖ P n) := by
  rw [Qembed_kronecker]; rfl

lemma Qtheta_eq_kron4 : Qtheta m d n e = kron4 (theta m) 1 (theta n) 1 := by
  rw [Qtheta, Qembed_kronecker]

lemma Pi_mul_Pi : Pi m d n e * Pi m d n e = Pi m d n e := by
  simp only [Pi, kron4_mul_kron4, P_mul_P, Matrix.one_mul]

lemma GA_mul_GA : GA m d n e * GA m d n e = Pi m d n e := by
  simp only [GA, Pi, kron4_mul_kron4, P_mul_P, Zplus_mul_Zplus, Z_mul_Z, Matrix.one_mul]

lemma Pi_mul_GA : Pi m d n e * GA m d n e = GA m d n e := by
  simp only [GA, Pi, kron4_mul_kron4, P_mul_P, P_mul_Z, Matrix.one_mul]

lemma GA_mul_Pi : GA m d n e * Pi m d n e = GA m d n e := by
  simp only [GA, Pi, kron4_mul_kron4, P_mul_P, Z_mul_P, Matrix.mul_one]

lemma GB_mul_GB (hn : 2 ≤ n) : GB m d n e * GB m d n e = Pi m d n e := by
  simp only [GB, Pi, kron4_mul_kron4, Z_mul_Z, X_mul_X hn, Zplus_mul_Zplus, Matrix.one_mul]

lemma Pi_mul_GB : Pi m d n e * GB m d n e = GB m d n e := by
  simp only [GB, Pi, kron4_mul_kron4, P_mul_Z, P_mul_X, Matrix.one_mul]

lemma GB_mul_Pi : GB m d n e * Pi m d n e = GB m d n e := by
  simp only [GB, Pi, kron4_mul_kron4, Z_mul_P, X_mul_P, Matrix.mul_one]

lemma Pi_transpose : (Pi m d n e)ᵀ = Pi m d n e := by
  simp only [Pi, kron4_transpose, P_transpose, transpose_one]

lemma GA_transpose : (GA m d n e)ᵀ = GA m d n e := by
  simp only [GA, kron4_transpose, P_transpose, Zplus_transpose, Z_transpose, transpose_one]

lemma GB_transpose : (GB m d n e)ᵀ = GB m d n e := by
  simp only [GB, kron4_transpose, Z_transpose, X_transpose, Zplus_transpose, transpose_one]

/-- `(Π + G_A)ᵀ (Π + G_A) = 2 (Π + G_A)`: the Hermitian-square form of `U`. -/
lemma Pi_add_GA_sq :
    (Pi m d n e + GA m d n e)ᵀ * (Pi m d n e + GA m d n e) = (2 : ℚ) • (Pi m d n e + GA m d n e) := by
  rw [transpose_add, Pi_transpose, GA_transpose, Matrix.add_mul, Matrix.mul_add, Matrix.mul_add,
    Pi_mul_Pi, Pi_mul_GA, GA_mul_Pi, GA_mul_GA, two_smul]
  abel

/-- `(Π + G_B)ᵀ (Π + G_B) = 2 (Π + G_B)` for `n ≥ 2`. -/
lemma Pi_add_GB_sq (hn : 2 ≤ n) :
    (Pi m d n e + GB m d n e)ᵀ * (Pi m d n e + GB m d n e) = (2 : ℚ) • (Pi m d n e + GB m d n e) := by
  rw [transpose_add, Pi_transpose, GB_transpose, Matrix.add_mul, Matrix.mul_add, Matrix.mul_add,
    Pi_mul_Pi, Pi_mul_GB, GB_mul_Pi, GB_mul_GB hn, two_smul]
  abel

end Structure

end CausalNonpurifiability
