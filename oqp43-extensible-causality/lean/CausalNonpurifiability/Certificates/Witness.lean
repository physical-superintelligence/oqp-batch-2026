module

public import CausalNonpurifiability.Data.Local
public import CausalNonpurifiability.Certificates.Soundness
public import CausalNonpurifiability.Certificates.Qubit

@[expose] public section


/-!
# `CausalNonpurifiability.Certificates.Witness`

The exact witness `S_0` (`eq:witness`) in every port dimension `m, d, n, e ≥ 2`:

* `RBOq_S0`, `RAOq_S0` — closed forms of the two replacements: apart from the positive
  factors `2/e`, `2/d`, the `A_O`-blocks of `R_{B_O} S_0` are `18|1⟩⟨1|` and
  `2(I - |1⟩⟨1|)`, the `B_O`-blocks of `R_{A_O} S_0` are `D_n ± 3X_n`, whose distinguished
  parts are the rank-one squares `(1, ±3)(1, ±3)ᵀ` (`eq:witness-replacements`,
  `eq:witness-rankone`);
* `RBOq_S0_psd`, `RAOq_S0_psd`, `witness_replacements_psd` — positivity of both images;
* `witness_trace_Qtheta`, `witness_trace_GA`, `witness_trace_GB`, `witness_traces` —
  `Tr(S_0 Q_{θ⊗θ}) = 3`, `Tr(S_0 G_A) = -40`, `Tr(S_0 G_B) = -24` (`eq:witness-traces`);
* `witness_negative` — `Tr(S_0 W_0) = -1/5` (`eq:negative`), and `Tr S_0 = 4(n+8)`
  (`eq:witness-size`).

Positivity transport helpers (`psd_toC_kron4`, `psd_toC_proj`, …) and the bridge lemmas
`toC (R•q T) = R_• (toC T)` live in `CausalNonpurifiability.Certificates.Qubit`. The endpoint statements
`witness_nonneg_on_cs : CausallySeparable D W → 0 ≤ Tr(S_0 W)` and
`wq_not_causallySeparable : ¬ CausallySeparable qubits (toC (W0 2 2 2 2))` are at the end.
-/

set_option autoImplicit false

namespace CausalNonpurifiability

open Matrix
open scoped Kronecker ComplexOrder

section Witness
variable {m d n e : ℕ}

/-! ### `R_{B_O} S_0` (`eq:witness-replacements`, first replacement) -/

/-- `(2/e) D_n (I - Z_n^+) = (36/e)|1⟩⟨1|` as a diagonal. -/
lemma block18 : (2 / e : ℚ) • (Dw n * (1 - Zplus n))
    = diagonal fun i => if i.val = 1 then (36 / e : ℚ) else 0 := by
  rw [Dw_mul_one_sub_Zplus, proj_eq, smul_smul, ← diagonal_smul]
  congr 1; funext i
  simp only [Pi.smul_apply, smul_eq_mul]
  split_ifs <;> ring

/-- `(2/e) D_n (I + Z_n^+) = (4/e)(I - |1⟩⟨1|)` as a diagonal. -/
lemma block2 : (2 / e : ℚ) • (Dw n * (1 + Zplus n))
    = diagonal fun i => if i.val = 1 then 0 else (4 / e : ℚ) := by
  rw [Dw_mul_one_add_Zplus, proj_eq, ← diagonal_one, diagonal_sub, smul_smul, ← diagonal_smul]
  congr 1; funext i
  simp only [Pi.smul_apply, smul_eq_mul]
  split_ifs <;> ring

/-- **First replacement.** `R_{B_O} S_0 = P_1 ⊗ |0⟩⟨0| ⊗ (36/e)|1⟩⟨1| ⊗ I
+ P_1 ⊗ |1⟩⟨1| ⊗ (4/e)(I - |1⟩⟨1|) ⊗ I` (`eq:witness-replacements`, blocks `18|1⟩⟨1|`,
`2(I - |1⟩⟨1|)`, factor `2/e`). -/
theorem RBOq_S0 (he : 2 ≤ e) :
    RBOq (S0 m d n e)
      = kron4 (proj m 1) (proj d 0) (diagonal fun i => if i.val = 1 then (36 / e : ℚ) else 0) 1
        + kron4 (proj m 1) (proj d 1) (diagonal fun i => if i.val = 1 then 0 else (4 / e : ℚ)) 1 := by
  rw [← block18, ← block2, S0, RBOq_add, RBOq_sub, RBOq_smul, RBOq_kron4, RBOq_kron4, RBOq_kron4,
    trace_P he, trace_Z he]
  simp only [Matrix.mul_sub, Matrix.mul_add, Matrix.mul_one, kron4_sub₃, kron4_add₃, kron4_smul₃,
    P, Z, kron4_add₂, kron4_sub₂, zero_div, zero_smul, smul_zero, add_zero]
  module

/-- `R_{B_O} S_0 ≥ 0`. -/
theorem RBOq_S0_psd (he : 2 ≤ e) : (toC (RBOq (S0 m d n e))).PosSemidef := by
  have he' : (0 : ℚ) ≤ 36 / e := by positivity
  have he'' : (0 : ℚ) ≤ 4 / e := by positivity
  rw [RBOq_S0 he, toC_add]
  refine PosSemidef.add ?_ ?_
  · refine psd_toC_kron4 (psd_toC_proj _ _) (psd_toC_proj _ _) ?_ (psd_toC_one _)
    exact diagonal_nonneg_sound _ fun i => by split_ifs <;> simp [he']
  · refine psd_toC_kron4 (psd_toC_proj _ _) (psd_toC_proj _ _) ?_ (psd_toC_one _)
    exact diagonal_nonneg_sound _ fun i => by split_ifs <;> simp [he'']

/-! ### `R_{A_O} S_0` (`eq:witness-replacements`, second replacement) -/

/-- `(1, 3, 0, …)` on `B_I`. -/
def wplus (n : ℕ) : Fin n → ℚ := fun i => if i.val = 0 then 1 else if i.val = 1 then 3 else 0

/-- `(1, -3, 0, …)` on `B_I`. -/
def wminus (n : ℕ) : Fin n → ℚ := fun i => if i.val = 0 then 1 else if i.val = 1 then -3 else 0

/-- `D_n + 3X_n = (I - P_n) + (1,3)(1,3)ᵀ` (`eq:witness-rankone`). -/
lemma Dw_add_X : Dw n + (3 : ℚ) • X n
    = diagonal (fun i => if i.val = 0 ∨ i.val = 1 then 0 else 1) + vecMulVec (wplus n) (wplus n) := by
  ext i j
  simp only [Dw_eq, X_apply, wplus, Matrix.add_apply, Matrix.smul_apply, diagonal_apply,
    vecMulVec_apply, smul_eq_mul]
  split_ifs <;> first | omega | norm_num

/-- `D_n - 3X_n = (I - P_n) + (1,-3)(1,-3)ᵀ` (`eq:witness-rankone`). -/
lemma Dw_sub_X : Dw n - (3 : ℚ) • X n
    = diagonal (fun i => if i.val = 0 ∨ i.val = 1 then 0 else 1) + vecMulVec (wminus n) (wminus n) := by
  ext i j
  simp only [Dw_eq, X_apply, wminus, Matrix.sub_apply, Matrix.add_apply, Matrix.smul_apply,
    diagonal_apply, vecMulVec_apply, smul_eq_mul]
  split_ifs <;> first | omega | norm_num

lemma psd_toC_Dw_add_X : (toC (Dw n + (3 : ℚ) • X n)).PosSemidef := by
  rw [Dw_add_X, toC_add]
  exact (diagonal_nonneg_sound _ fun i => by split_ifs <;> norm_num).add (vecMulVec_self_sound _)

lemma psd_toC_Dw_sub_X : (toC (Dw n - (3 : ℚ) • X n)).PosSemidef := by
  rw [Dw_sub_X, toC_add]
  exact (diagonal_nonneg_sound _ fun i => by split_ifs <;> norm_num).add (vecMulVec_self_sound _)

/-- **Second replacement.** `R_{A_O} S_0 = (2/d)[P_1 ⊗ I ⊗ (D_n + 3X_n) ⊗ |0⟩⟨0|
+ P_1 ⊗ I ⊗ (D_n - 3X_n) ⊗ |1⟩⟨1|]` (`eq:witness-replacements`, factor `2/d`). -/
theorem RAOq_S0 (hd : 2 ≤ d) :
    RAOq (S0 m d n e)
      = kron4 ((2 / d : ℚ) • proj m 1) 1 (Dw n + (3 : ℚ) • X n) (proj e 0)
        + kron4 ((2 / d : ℚ) • proj m 1) 1 (Dw n - (3 : ℚ) • X n) (proj e 1) := by
  rw [S0, RAOq_add, RAOq_sub, RAOq_smul, RAOq_kron4, RAOq_kron4, RAOq_kron4, trace_P hd,
    trace_Z hd]
  simp only [kron4_smul₁, kron4_add₃, kron4_sub₃, kron4_smul₃, P, Z, kron4_add₄, kron4_sub₄,
    zero_div, zero_smul, sub_zero]
  module

/-- `R_{A_O} S_0 ≥ 0`. -/
theorem RAOq_S0_psd (hd : 2 ≤ d) : (toC (RAOq (S0 m d n e))).PosSemidef := by
  have hd' : (0 : ℚ) ≤ 2 / d := by positivity
  rw [RAOq_S0 hd, toC_add]
  exact (psd_toC_kron4 (psd_toC_smul_proj _ _ hd') (psd_toC_one _) psd_toC_Dw_add_X
    (psd_toC_proj _ _)).add
    (psd_toC_kron4 (psd_toC_smul_proj _ _ hd') (psd_toC_one _) psd_toC_Dw_sub_X (psd_toC_proj _ _))

/-- **Witness replacements** (`eq:witness-replacements`): `R_{B_O} S_0 ≥ 0` and
`R_{A_O} S_0 ≥ 0` in every port dimension. -/
theorem witness_replacements_psd (hd : 2 ≤ d) (he : 2 ≤ e) :
    (toC (RBOq (S0 m d n e))).PosSemidef ∧ (toC (RAOq (S0 m d n e))).PosSemidef :=
  ⟨RBOq_S0_psd he, RAOq_S0_psd hd⟩

lemma Zplus_mul_Dw_comm : Zplus n * Dw n = Dw n * Zplus n := by
  rw [Dw_eq, Zplus_eq, diagonal_mul_diagonal, diagonal_mul_diagonal]
  congr 1; funext i; ring

/-- `S_0` is symmetric, hence its complex image is Hermitian. -/
theorem S0_transpose : (S0 m d n e)ᵀ = S0 m d n e := by
  simp only [S0, transpose_add, transpose_sub, transpose_smul, kron4_transpose, proj_transpose,
    P_transpose, Z_transpose, Dw_transpose, X_transpose, transpose_mul, Zplus_transpose,
    Zplus_mul_Dw_comm]

theorem S0_isHermitian : (toC (S0 m d n e)).IsHermitian :=
  isHermitian_map_of_transpose _ S0_transpose

/-! ### The three traces (`eq:witness-traces`) -/

/-- `Tr(S_0 Q_{θ_m⊗θ_n}) = 3`. -/
theorem witness_trace_Qtheta (hm : 2 ≤ m) (hd : 2 ≤ d) (hn : 2 ≤ n) (he : 2 ≤ e) :
    trace (S0 m d n e * Qtheta m d n e) = 3 := by
  rw [Qtheta_eq_kron4, S0]
  simp only [Matrix.sub_mul, Matrix.add_mul, Matrix.smul_mul, trace_sub, trace_add, trace_smul,
    kron4_mul_kron4, trace_kron4, Matrix.mul_one, trace_proj1_mul_theta hm, trace_P hd,
    trace_Dw_mul_theta hn, trace_P he, trace_Z hd, trace_Z he, smul_eq_mul, mul_zero, zero_mul]
  norm_num

/-- `Tr(S_0 G_A) = -40`. -/
theorem witness_trace_GA (hm : 2 ≤ m) (hd : 2 ≤ d) (hn : 2 ≤ n) (he : 2 ≤ e) :
    trace (S0 m d n e * GA m d n e) = -40 := by
  rw [GA, S0]
  simp only [Matrix.sub_mul, Matrix.add_mul, Matrix.smul_mul, trace_sub, trace_add, trace_smul,
    kron4_mul_kron4, trace_kron4, Matrix.mul_one, trace_proj1_mul_P hm, trace_P_mul_Zplus hd,
    trace_Z_mul_Zplus hd, trace_Dw_mul_Zplus_mul_Z hn, trace_P he, smul_eq_mul, mul_zero,
    zero_mul]
  norm_num

/-- `Tr(S_0 G_B) = -24`. -/
theorem witness_trace_GB (hm : 2 ≤ m) (hd : 2 ≤ d) (hn : 2 ≤ n) (he : 2 ≤ e) :
    trace (S0 m d n e * GB m d n e) = -24 := by
  rw [GB, S0]
  simp only [Matrix.sub_mul, Matrix.add_mul, Matrix.smul_mul, trace_sub, trace_add, trace_smul,
    kron4_mul_kron4, trace_kron4, Matrix.mul_one, trace_proj1_mul_Z hm, trace_P hd, trace_Z hd,
    trace_Dw_mul_X, trace_X_mul_X hn, trace_Z_mul_Zplus he, smul_eq_mul, mul_zero, zero_mul]
  norm_num

/-- **The three witness traces** `(3, -40, -24)` (`eq:witness-traces`). -/
theorem witness_traces (hm : 2 ≤ m) (hd : 2 ≤ d) (hn : 2 ≤ n) (he : 2 ≤ e) :
    trace (S0 m d n e * Qtheta m d n e) = 3 ∧ trace (S0 m d n e * GA m d n e) = -40 ∧
      trace (S0 m d n e * GB m d n e) = -24 :=
  ⟨witness_trace_Qtheta hm hd hn he, witness_trace_GA hm hd hn he, witness_trace_GB hm hd hn he⟩

/-- **The witness is negative on `W_0`**: `Tr(S_0 W_0) = 3 - (40 + 24)/20 = -1/5` (`eq:negative`),
in every port dimension. -/
theorem witness_negative (hm : 2 ≤ m) (hd : 2 ≤ d) (hn : 2 ≤ n) (he : 2 ≤ e) :
    trace (S0 m d n e * W0 m d n e) = -1 / 5 := by
  rw [W0, Matrix.mul_add, Matrix.mul_smul, Matrix.mul_add, trace_add, trace_smul, trace_add,
    witness_trace_Qtheta hm hd hn he, witness_trace_GA hm hd hn he, witness_trace_GB hm hd hn he,
    smul_eq_mul]
  norm_num

/-- `Tr(S_0 W_q) = -1/5` at four qubit ports. -/
theorem witness_negative_qubit : trace (S0 2 2 2 2 * W0 2 2 2 2) = -1 / 5 :=
  witness_negative le_rfl le_rfl le_rfl le_rfl

/-- `Tr D_n = n + 8`. -/
theorem trace_Dw (hn : 2 ≤ n) : trace (Dw n) = n + 8 := by
  rw [Dw, trace_add, trace_smul, trace_one, Fintype.card_fin, proj_eq, trace_diagonal,
    sum_fin_of_two_le hn]
  · norm_num
  · intro i hi; split_ifs <;> first | omega | norm_num

/-- `Tr S_0 = 4(n + 8)` (`eq:witness-size`). -/
theorem trace_S0 (hm : 2 ≤ m) (hd : 2 ≤ d) (hn : 2 ≤ n) (he : 2 ≤ e) :
    trace (S0 m d n e) = 4 * (n + 8) := by
  have h1 : trace (proj m 1) = 1 := by
    rw [proj_eq, trace_diagonal, sum_fin_of_two_le hm]
    · norm_num
    · intro i hi; split_ifs <;> first | omega | norm_num
  simp only [S0, trace_sub, trace_add, trace_smul, trace_kron4, h1, trace_P hd, trace_P he,
    trace_Z hd, trace_Z he, trace_Dw hn, smul_eq_mul, mul_zero, zero_mul]
  ring

end Witness

/-! ### Nonnegativity on the causally separable cone (abstract form)

For `T ∈ O_{A≺B}` one has `R_{B_O} T = T`, and the replacement is self-adjoint for the
Hilbert–Schmidt pairing, so `Tr(S_0 T) = Tr((R_{B_O} S_0) T) ≥ 0` by positivity of both factors
(`sec:witness`). The statement below isolates exactly this argument; instantiating it with
`R_BO`/`OrderedAB` (`replacement_trace_pairing`) and `RBOq_S0_psd` gives
`witness_nonneg_on_cs`. -/

open scoped MatrixOrder Matrix.Norms.L2Operator in
/-- PSD trace pairing: `Tr(AB) ≥ 0` for PSD `A, B` (factor `A = Kᴴ K` and use cyclicity). -/
theorem trace_mul_nonneg_of_posSemidef {ι : Type} [Fintype ι] [DecidableEq ι]
    {A B : Matrix ι ι ℂ} (hA : A.PosSemidef) (hB : B.PosSemidef) : 0 ≤ trace (A * B) := by
  obtain ⟨K, hK⟩ := CStarAlgebra.nonneg_iff_eq_star_mul_self.mp hA.nonneg
  rw [hK, star_eq_conjTranspose, Matrix.mul_assoc, trace_mul_comm]
  exact (hB.mul_mul_conjTranspose_same K).trace_nonneg

/-- `Tr(S T) = Tr((R S) T) ≥ 0` for a self-adjoint replacement `R` fixing `T`, with `R S ≥ 0`
and `T ≥ 0` (the argument of `sec:witness`). -/
theorem witness_nonneg_of_replacement {ι : Type} [Fintype ι] [DecidableEq ι]
    (S T : Matrix ι ι ℂ) (R : Matrix ι ι ℂ → Matrix ι ι ℂ)
    (hself : ∀ A B : Matrix ι ι ℂ, trace (R A * B) = trace (A * R B))
    (hRS : (R S).PosSemidef) (hT : T.PosSemidef) (hTR : R T = T) :
    0 ≤ trace (S * T) := by
  rw [← hTR, ← hself]
  exact trace_mul_nonneg_of_posSemidef hRS hT

section Ports
variable (D : Ports)

/-- **The witness is nonnegative on every causally separable process** (`sec:witness`):
for `W ∈ O_{A≺B} + O_{B≺A}`, `Tr(S_0 W) ≥ 0` (in the complex order). -/
theorem witness_nonneg_on_cs (hd : 2 ≤ D.d) (he : 2 ≤ D.e) (W : PMat D)
    (hW : CausallySeparable D W) : 0 ≤ trace (toC (S0 D.m D.d D.n D.e) * W) := by
  obtain ⟨-, U', V', hU', hV', rfl⟩ := hW
  rw [Matrix.mul_add, trace_add]
  refine add_nonneg ?_ ?_
  · exact witness_nonneg_of_replacement _ _ (fun A => R_BO A) (fun A B => R_BO_pairing A B)
      (by rw [← toC_RBOq]; exact RBOq_S0_psd he) hU'.2.1 hU'.2.2
  · exact witness_nonneg_of_replacement _ _ (fun A => R_AO A) (fun A B => R_AO_pairing A B)
      (by rw [← toC_RAOq]; exact RAOq_S0_psd hd) hV'.2.1 hV'.2.2

/-- Real-part form of `witness_nonneg_on_cs`. -/
theorem witness_nonneg_on_cs_re (hd : 2 ≤ D.d) (he : 2 ≤ D.e) (W : PMat D)
    (hW : CausallySeparable D W) : 0 ≤ (trace (toC (S0 D.m D.d D.n D.e) * W)).re :=
  (Complex.nonneg_iff.mp (witness_nonneg_on_cs D hd he W hW)).1

end Ports

/-- **`W_q` is not causally separable** (`eq:negative` with `sec:witness`): the witness `S_0` is
nonnegative on `O_{A≺B} + O_{B≺A}` but `Tr(S_0 W_q) = -1/5`. -/
theorem wq_not_causallySeparable : ¬ CausallySeparable qubits (toC (W0 2 2 2 2)) := by
  intro h
  have h0 : (0 : ℂ) ≤ trace (toC (S0 2 2 2 2) * toC (W0 2 2 2 2)) :=
    witness_nonneg_on_cs qubits le_rfl le_rfl _ h
  rw [← Matrix.map_mul, trace_toC, witness_negative_qubit, Complex.nonneg_iff] at h0
  norm_num at h0

end CausalNonpurifiability
