module

public import CausalNonpurifiability.Certificates.QubitCore
public import CausalNonpurifiability.Data.Qubit
public import CausalNonpurifiability.Certificates.Soundness
public import CausalNonpurifiability.Definitions.Process

@[expose] public section


/-!
# `CausalNonpurifiability.Certificates.Qubit`

Exact rational certificates for the process `W_0` and its qubit endpoint `W_q`:

* `wq_posDef` — positive definiteness of `W_q` from the eight `2×2` LDL blocks
  (`eq:positive-blocks`: pivots `49, 523/49`, `41, 763/41`, `19, 3/19`, `11, 83/11`),
  assembled into one sparse unit-triangular factor `wqL` indexed by the digits of
  `j = 8α + 4o + 2β + t`; `w0_qubit_posDef` transports it to the tensor construction;
* `u_psd`, `v_psd` — `U = (Π+G_A)ᵀ(Π+G_A)/40`, `V = (Π+G_B)ᵀ(Π+G_B)/40` in every
  dimension (`eq:UV`);
* `signed_decomposition` — `W_0 = U + V + 2 Q_C` in every dimension
  (`eq:signed-decomposition`);
* `reference_state_A/B` — `ω_A(U) + C_A = θ_m/2`, `ω_B(V) + C_B = θ_n/2`, both of trace
  `1/2` (`eq:reference-states`), together with `Tr U = Tr V = de/5`, `Tr C = 3/10`,
  `Tr W_0 = de`;
* `gram_identity`, `K_psd` — `160 K = 16 bbᵀ + ½ uuᵀ + 7/2 vvᵀ` (`eq:K`, `eq:Gram`).

* `w0_valid`, `u_orderedAB`, `v_orderedBA` — validity (`eq:LV`, `eq:valid`) and the ordered-cone
  memberships against the definitions of `CausalNonpurifiability.Definitions.Process`, via the bridge
  `toC (R•q T) = R_• (toC T)` between the rational entry-rule replacements and the complex-linear
  maps of `CausalNonpurifiability.Linear.Replacement`.
-/

set_option autoImplicit false

namespace CausalNonpurifiability

open Matrix
open scoped Kronecker ComplexOrder

/-! ### The four `2×2` blocks of `80 W_q` (`eq:positive-blocks`) -/

/-- Determinants `523, 763, 3, 83` of the four blocks (`eq:positive-blocks`). -/
theorem positive_blocks_determinants : blockA 0 0 * blockB 0 0 - 16 = 523 ∧ blockA 0 1 * blockB 0 1 - 16 = 763 ∧
    blockA 1 0 * blockB 1 0 - 16 = 3 ∧ blockA 1 1 * blockB 1 1 - 16 = 83 := by decide +kernel

/-- The four `2×2` LDL certificates (`B = L diag(a, (ab-s²)/a) Lᵀ`). -/
theorem positive_blocks_ldl : !![(49 : ℚ), 4; 4, 11] = !![1, 0; 4 / 49, 1] * diagonal ![49, 523 / 49] * !![1, 0; 4 / 49, 1]ᵀ
    ∧ !![(41 : ℚ), -4; -4, 19] = !![1, 0; -4 / 41, 1] * diagonal ![41, 763 / 41] * !![1, 0; -4 / 41, 1]ᵀ
    ∧ !![(19 : ℚ), 4; 4, 1] = !![1, 0; 4 / 19, 1] * diagonal ![19, 3 / 19] * !![1, 0; 4 / 19, 1]ᵀ
    ∧ !![(11 : ℚ), -4; -4, 9] = !![1, 0; -4 / 11, 1] * diagonal ![11, 83 / 11] * !![1, 0; -4 / 11, 1]ᵀ := by
  decide +kernel

/-! ### The assembled LDL certificate of `W_q` -/

/-- Unit lower-triangular factor of `W_q`: within each `B_I` block (fixed `α, o, t`) the single
multiplier `s/a = 4(-1)^{α+t}/a(α,o)` sits at `(j(α,o,1,t), j(α,o,0,t))`. -/
def wqL : Matrix (Fin 16) (Fin 16) ℚ :=
  of fun j k =>
    if j = k then 1
    else if qα j = qα k ∧ qo j = qo k ∧ qt j = qt k ∧ qβ j = 1 ∧ qβ k = 0 then
      4 * (-1) ^ (qα j + qt j) / blockA (qα j) (qo j)
    else 0

/-- Pivots of `W_q`: `a/80` at `β = 0` and `(ab - 16)/(80 a)` at `β = 1`. -/
def wqPivot (j : Fin 16) : ℚ :=
  (1 / 80) * (if qβ j = 0 then blockA (qα j) (qo j)
    else (blockA (qα j) (qo j) * blockB (qα j) (qo j) - 16) / blockA (qα j) (qo j))

/-- The certificate identity `W_q = L diag(pivots) Lᵀ`, entrywise. -/
lemma wq_ldl_entries' : WqEntries = of fun i j => ∑ k, wqL i k * wqPivot k * wqL j k := by
  decide +kernel

lemma wq_ldl_entries : ∀ i j, WqEntries i j = ∑ k, wqL i k * wqPivot k * wqL j k := by
  intro i j
  rw [wq_ldl_entries']
  rfl

lemma wqPivot_pos : ∀ j, 0 < wqPivot j := by decide +kernel

/-- `L⁻¹ = 2·1 - L` (the strictly triangular part is nilpotent of order two). -/
lemma wqL_mul_inv : wqL * ((2 : ℚ) • 1 - wqL) = 1 := by decide +kernel

/-- **`W_q` is positive definite** (`eq:qubit-minimum`). -/
theorem wq_posDef : (toC WqEntries).PosDef :=
  rational_ldl_posDef_of_inverse WqEntries wqL ((2 : ℚ) • 1 - wqL) wqPivot wq_ldl_entries
    wqPivot_pos wqL_mul_inv

theorem wq_posSemidef : (toC WqEntries).PosSemidef := wq_posDef.posSemidef

/-- The tensor construction at four qubit ports is positive definite. -/
theorem w0_qubit_posDef : (toC (W0 2 2 2 2)).PosDef := by
  rw [w0_qubit_eq_wq, reindex_apply, Equiv.symm_symm, toC, ← submatrix_map]
  exact wq_posDef.submatrix qubitFlat.injective

theorem w0_qubit_posSemidef : (toC (W0 2 2 2 2)).PosSemidef := w0_qubit_posDef.posSemidef

/-! ### `U` and `V` as Hermitian squares (`eq:UV`) -/

section UV
variable {m d n e : ℕ}

theorem U_eq_sq :
    U m d n e = (1 / 40 : ℚ) • ((Pi m d n e + GA m d n e)ᵀ * (Pi m d n e + GA m d n e)) := by
  rw [Pi_add_GA_sq, U, smul_smul]; norm_num

theorem V_eq_sq (hn : 2 ≤ n) :
    V m d n e = (1 / 40 : ℚ) • ((Pi m d n e + GB m d n e)ᵀ * (Pi m d n e + GB m d n e)) := by
  rw [Pi_add_GB_sq hn, V, smul_smul]; norm_num

/-- `U ≥ 0` in every port dimension. -/
theorem u_psd : (toC (U m d n e)).PosSemidef :=
  transpose_mul_self_sound _ _ _ U_eq_sq (by norm_num)

/-- `V ≥ 0` in every port dimension with `n ≥ 2`. -/
theorem v_psd (hn : 2 ≤ n) : (toC (V m d n e)).PosSemidef :=
  transpose_mul_self_sound _ _ _ (V_eq_sq hn) (by norm_num)

/-- `R_{B_O} U = U` in rational coordinates (`U ∈ O_{A≺B}`, `eq:ordered-cones`). -/
theorem RBOq_U (he : 0 < e) : RBOq (U m d n e) = U m d n e := by
  have he' : (e : ℚ) ≠ 0 := by exact_mod_cast he.ne'
  simp only [U, Pi, GA, RBOq_smul, RBOq_add, RBOq_kron4, trace_one, Fintype.card_fin,
    div_self he', one_smul]

/-- `R_{A_O} V = V` in rational coordinates (`V ∈ O_{B≺A}`, `eq:ordered-cones`). -/
theorem RAOq_V (hd : 0 < d) : RAOq (V m d n e) = V m d n e := by
  have hd' : (d : ℚ) ≠ 0 := by exact_mod_cast hd.ne'
  simp only [V, Pi, GB, RAOq_smul, RAOq_add, RAOq_kron4, trace_one, Fintype.card_fin,
    div_self hd', one_smul]

end UV

/-! ### The signed-input decomposition (`eq:signed-decomposition`) -/

section Signed
variable {m d n e : ℕ}

/-- `θ_m ⊗ θ_n - (P_m ⊗ P_n)/10 = 2C` on `A_I B_I`: the input-space content of
`eq:signed-decomposition`. -/
lemma input_identity (m n : ℕ) :
    theta m ⊗ₖ theta n - (1 / 10 : ℚ) • (P m ⊗ₖ P n) = (2 : ℚ) • C m n := by
  ext ⟨a, b⟩ ⟨a', b'⟩
  simp only [C, theta_eq, P_eq, proj_eq, Matrix.sub_apply, Matrix.smul_apply, Matrix.add_apply,
    kroneckerMap_apply, diagonal_apply, smul_eq_mul]
  split_ifs <;> first | omega | norm_num

/-- **Signed decomposition** `W_0 = U + V + 2 Q_C` in every port dimension. -/
theorem signed_decomposition (m d n e : ℕ) :
    W0 m d n e = U m d n e + V m d n e + (2 : ℚ) • Qembed d e (C m n) := by
  rw [← Qembed_smul, ← input_identity, Qembed_sub, Qembed_smul, ← Pi_eq_Qembed, ← Qtheta]
  unfold W0 U V
  module

end Signed

/-! ### Reference states (`eq:reference-states`) and traces -/

section Reference
variable {m d n e : ℕ}

lemma trace_proj0 (hr : 2 ≤ m) : trace (proj m 0) = 1 := by
  rw [proj_eq, trace_diagonal, sum_fin_of_two_le hr]
  · norm_num
  · intro i hi; split_ifs <;> first | omega | norm_num

lemma trace_proj1 (hr : 2 ≤ m) : trace (proj m 1) = 1 := by
  rw [proj_eq, trace_diagonal, sum_fin_of_two_le hr]
  · norm_num
  · intro i hi; split_ifs <;> first | omega | norm_num

/-- `ω_A(U) = P_m/10` (`eq:reference-states`). -/
theorem omegaAq_U (hn : 2 ≤ n) (hd : 0 < d) (he : 0 < e) :
    omegaAq (U m d n e) = (1 / 10 : ℚ) • P m := by
  have hd' : (d : ℚ) ≠ 0 := by exact_mod_cast hd.ne'
  have he' : (e : ℚ) ≠ 0 := by exact_mod_cast he.ne'
  rw [U, omegaAq_smul, Pi, GA, omegaAq_add, omegaAq_kron4, omegaAq_kron4, trace_P hn, trace_Z hn,
    trace_one, trace_one, Fintype.card_fin, Fintype.card_fin, smul_add, smul_smul, smul_smul,
    ← add_smul]
  congr 1
  field_simp
  ring

/-- `ω_B(V) = P_n/10` (`eq:reference-states`). -/
theorem omegaBq_V (hm : 2 ≤ m) (hd : 0 < d) (he : 0 < e) :
    omegaBq (V m d n e) = (1 / 10 : ℚ) • P n := by
  have hd' : (d : ℚ) ≠ 0 := by exact_mod_cast hd.ne'
  have he' : (e : ℚ) ≠ 0 := by exact_mod_cast he.ne'
  rw [V, omegaBq_smul, Pi, GB, omegaBq_add, omegaBq_kron4, omegaBq_kron4, trace_P hm, trace_Z hm,
    trace_one, trace_one, Fintype.card_fin, Fintype.card_fin, smul_add, smul_smul, smul_smul]
  simp only [zero_mul, mul_zero, zero_div, zero_smul, add_zero]
  congr 1
  field_simp
  ring

/-- `C_A = Tr_{B_I} C = diag(44, 4)/160` (`eq:reference-states`). -/
theorem ptrB_C (hn : 2 ≤ n) :
    ptrB (C m n) = diagonal fun a => if a.val = 0 then 11 / 40 else if a.val = 1 then 1 / 40 else 0 := by
  ext a a'
  simp only [ptrB, of_apply]
  rw [sum_fin_of_two_le hn]
  · simp [C, proj_eq, kroneckerMap_apply, diagonal_apply]
    split_ifs <;> first | omega | norm_num
  · intro b hb
    simp [C, proj_eq, kroneckerMap_apply, diagonal_apply]
    split_ifs <;> first | omega | norm_num

/-- `C_B = Tr_{A_I} C = diag(44, 4)/160` (`eq:reference-states`). -/
theorem ptrA_C (hm : 2 ≤ m) :
    ptrA (C m n) = diagonal fun b => if b.val = 0 then 11 / 40 else if b.val = 1 then 1 / 40 else 0 := by
  ext b b'
  simp only [ptrA, of_apply]
  rw [sum_fin_of_two_le hm]
  · simp [C, proj_eq, kroneckerMap_apply, diagonal_apply]
    split_ifs <;> first | omega | norm_num
  · intro a ha
    simp [C, proj_eq, kroneckerMap_apply, diagonal_apply]
    split_ifs <;> first | omega | norm_num

/-- **Reference state of Alice**: `χ_A = ω_A(U) + C_A = θ_m/2` (`eq:reference-states`). -/
theorem reference_state_A (hn : 2 ≤ n) (hd : 0 < d) (he : 0 < e) :
    omegaAq (U m d n e) + ptrB (C m n) = (1 / 2 : ℚ) • theta m := by
  rw [omegaAq_U hn hd he, ptrB_C hn, P_eq, theta_eq]
  ext a a'
  simp only [Matrix.add_apply, Matrix.smul_apply, diagonal_apply, smul_eq_mul]
  split_ifs <;> first | omega | norm_num

/-- **Reference state of Bob**: `χ_B = ω_B(V) + C_B = θ_n/2` (`eq:reference-states`). -/
theorem reference_state_B (hm : 2 ≤ m) (hd : 0 < d) (he : 0 < e) :
    omegaBq (V m d n e) + ptrA (C m n) = (1 / 2 : ℚ) • theta n := by
  rw [omegaBq_V hm hd he, ptrA_C hm, P_eq, theta_eq]
  ext b b'
  simp only [Matrix.add_apply, Matrix.smul_apply, diagonal_apply, smul_eq_mul]
  split_ifs <;> first | omega | norm_num

/-- `Tr χ_A = 1/2`. -/
theorem trace_chiA (hm : 2 ≤ m) (hn : 2 ≤ n) (hd : 0 < d) (he : 0 < e) :
    trace (omegaAq (U m d n e) + ptrB (C m n)) = 1 / 2 := by
  rw [reference_state_A hn hd he, trace_smul, trace_theta hm, smul_eq_mul, mul_one]

/-- `Tr χ_B = 1/2`. -/
theorem trace_chiB (hm : 2 ≤ m) (hn : 2 ≤ n) (hd : 0 < d) (he : 0 < e) :
    trace (omegaBq (V m d n e) + ptrA (C m n)) = 1 / 2 := by
  rw [reference_state_B hm hd he, trace_smul, trace_theta hn, smul_eq_mul, mul_one]

/-- `Tr C = 3/10`. -/
theorem trace_C (hm : 2 ≤ m) (hn : 2 ≤ n) : trace (C m n) = 3 / 10 := by
  simp only [C, trace_smul, trace_add, trace_sub, trace_kronecker, trace_proj0 hm, trace_proj1 hm,
    trace_proj0 hn, trace_proj1 hn, smul_eq_mul]
  norm_num

/-- `Tr Π = 4de`. -/
theorem trace_Pi (hm : 2 ≤ m) (hn : 2 ≤ n) : trace (Pi m d n e) = 4 * (d * e : ℕ) := by
  simp only [Pi, trace_kron4, trace_P hm, trace_P hn, trace_one, Fintype.card_fin]
  push_cast; ring

/-- `Tr G_A = 0`. -/
theorem trace_GA (hn : 2 ≤ n) : trace (GA m d n e) = 0 := by
  simp [GA, trace_kron4, trace_Z hn]

/-- `Tr G_B = 0`. -/
theorem trace_GB (hm : 2 ≤ m) : trace (GB m d n e) = 0 := by
  simp [GB, trace_kron4, trace_Z hm]

/-- `Tr Q_{θ_m ⊗ θ_n} = de`. -/
theorem trace_Qtheta (hm : 2 ≤ m) (hn : 2 ≤ n) : trace (Qtheta m d n e) = (d * e : ℕ) := by
  simp only [Qtheta_eq_kron4, trace_kron4, trace_theta hm, trace_theta hn, trace_one,
    Fintype.card_fin]
  push_cast; ring

/-- `Tr W_0 = de` (`eq:valid`, normalization). -/
theorem trace_W0 (hm : 2 ≤ m) (hn : 2 ≤ n) : trace (W0 m d n e) = (d * e : ℕ) := by
  rw [W0, trace_add, trace_smul, trace_add, trace_GA hn, trace_GB hm, trace_Qtheta hm hn]
  simp

/-- `Tr U = de/5` (`eq:reference-states`). -/
theorem trace_U (hm : 2 ≤ m) (hn : 2 ≤ n) : trace (U m d n e) = (d * e : ℕ) / 5 := by
  rw [U, trace_smul, trace_add, trace_Pi hm hn, trace_GA hn, smul_eq_mul]
  ring

/-- `Tr V = de/5` (`eq:reference-states`). -/
theorem trace_V (hm : 2 ≤ m) (hn : 2 ≤ n) : trace (V m d n e) = (d * e : ℕ) / 5 := by
  rw [V, trace_smul, trace_add, trace_Pi hm hn, trace_GB hm, smul_eq_mul]
  ring

/-- `Tr W_c = de` (`eq:centers`, `eq:ball`). -/
theorem trace_Wc (hm : 2 ≤ m) (hn : 2 ≤ n) : trace (Wc m d n e) = (d * e : ℕ) := by
  have hm' : (m : ℚ) ≠ 0 := by exact_mod_cast (by omega : m ≠ 0)
  have hn' : (n : ℚ) ≠ 0 := by exact_mod_cast (by omega : n ≠ 0)
  rw [Wc, trace_add, trace_smul, trace_smul, trace_smul, trace_W0 hm hn, trace_one]
  simp only [Fintype.card_prod, Fintype.card_fin, smul_eq_mul]
  push_cast
  field_simp
  ring

end Reference

/-! ### The four-vertex Gram identity (`eq:K`, `eq:Gram`) -/

/-- Diagonal coefficients `c_{ij}` of `C` on the distinguished inputs (`eq:C`). -/
def cC : Fin 2 → Fin 2 → ℚ := ![![37 / 160, 7 / 160], ![7 / 160, -3 / 160]]

/-- `e_i - f_j` in vertex order `A0, A1, B0, B1`. -/
def evec (i j : Fin 2) : Fin 4 → ℚ :=
  fun k => (if k.val = i.val then 1 else 0) - (if k.val = j.val + 2 then 1 else 0)

/-- `K = ∑_{ij} c_{ij} (e_i - f_j)(e_i - f_j)ᵀ` (definition of `K` in `sec:statement`). -/
theorem Kmat_eq_vertex_sum :
    Kmat = ∑ i : Fin 2, ∑ j : Fin 2, cC i j • vecMulVec (evec i j) (evec i j) := by
  decide +kernel

/-- **Gram identity** `160 K = 16 bbᵀ + ½ uuᵀ + 7/2 vvᵀ` (`eq:Gram`). -/
theorem gram_identity :
    (160 : ℚ) • Kmat = (16 : ℚ) • vecMulVec bvec bvec + (1 / 2 : ℚ) • vecMulVec uvec uvec
      + (7 / 2 : ℚ) • vecMulVec vvec vvec := by
  decide +kernel

/-- `K ≥ 0` (`eq:Gram`). -/
theorem K_psd : (toC Kmat).PosSemidef :=
  gram_sound Kmat ![1 / 10, 1 / 320, 7 / 320] ![bvec, uvec, vvec] (by decide +kernel)
    (by decide +kernel)

/-! ### Positivity transport for Kronecker products of rational diagonals -/

section PsdHelpers
variable {m d n e : ℕ}

lemma psd_toC_kron4 {A : Matrix (Fin m) (Fin m) ℚ} {B : Matrix (Fin d) (Fin d) ℚ}
    {C : Matrix (Fin n) (Fin n) ℚ} {D : Matrix (Fin e) (Fin e) ℚ}
    (hA : (toC A).PosSemidef) (hB : (toC B).PosSemidef) (hC : (toC C).PosSemidef)
    (hD : (toC D).PosSemidef) : (toC (kron4 A B C D)).PosSemidef := by
  rw [toC_kron4]
  exact (hA.kronecker hB).kronecker (hC.kronecker hD)

lemma psd_toC_proj (r k : ℕ) : (toC (proj r k)).PosSemidef := by
  rw [proj_eq]
  exact diagonal_nonneg_sound _ fun i => by split_ifs <;> norm_num

lemma psd_toC_one (r : ℕ) : (toC (1 : Matrix (Fin r) (Fin r) ℚ)).PosSemidef := by
  rw [← diagonal_one]
  exact diagonal_nonneg_sound _ fun _ => zero_le_one

lemma psd_toC_smul_proj (r k : ℕ) {c : ℚ} (hc : 0 ≤ c) : (toC (c • proj r k)).PosSemidef := by
  rw [proj_eq, ← diagonal_smul]
  refine diagonal_nonneg_sound _ fun i => ?_
  simp only [Pi.smul_apply, smul_eq_mul]
  split_ifs <;> simp [hc]

end PsdHelpers

/-! ### Positivity of `W_0` in every port dimension (`eq:positive-blocks`)

`W_0` vanishes on `Π^⊥`; on `Π`, for fixed Alice input `a ∈ {0,1}` and eigenvectors of
`Z_d^+`, `Z_e^+` (signs `σ, τ`), its `B_I` block is
`θ(a) θ_n + (σ/20) Z_n + (Z(a) τ/20) X_n`, i.e. one of the four `2×2` blocks of
`eq:positive-blocks` (with the sign `τ` on the off-diagonal), padded by zeros. Each block is a
Gram sum `x vvᵀ + ((xy - s²)/x) e₁e₁ᵀ` with `v = (1, s/x)`, so `W_0` is a sum of eight
Kronecker products of PSD factors. No dimension hypothesis is needed. -/

section BlockPsd
variable {m d n e : ℕ}

/-- Spectral projector of `Z_r^+` onto the eigenvalue `+1`: `I_r - |1⟩⟨1|`. -/
def Pplus (r : ℕ) : Matrix (Fin r) (Fin r) ℚ := 1 - proj r 1

lemma Pplus_eq (r : ℕ) : Pplus r = diagonal fun i => if i.val = 1 then 0 else 1 := by
  ext i j
  simp only [Pplus, proj_eq, Matrix.sub_apply, one_apply, diagonal_apply]
  split_ifs <;> first | omega | norm_num

lemma psd_toC_Pplus (r : ℕ) : (toC (Pplus r)).PosSemidef := by
  rw [Pplus_eq]
  exact diagonal_nonneg_sound _ fun i => by split_ifs <;> norm_num

/-- `x|0⟩⟨0| + y|1⟩⟨1| + s(|0⟩⟨1| + |1⟩⟨0|)` on `Fin n`: a `2×2` block padded by zeros. -/
def blk (n : ℕ) (x y s : ℚ) : Matrix (Fin n) (Fin n) ℚ := x • proj n 0 + y • proj n 1 + s • X n

/-- `(1, s/x, 0, …)`. -/
def gv (n : ℕ) (x s : ℚ) : Fin n → ℚ := fun i => if i.val = 0 then 1 else if i.val = 1 then s / x else 0

/-- `(0, 1, 0, …)`. -/
def e1 (n : ℕ) : Fin n → ℚ := fun i => if i.val = 1 then 1 else 0

/-- Gram form of a block with nonzero leading entry: `blk x y s = x vvᵀ + ((xy - s²)/x) e₁e₁ᵀ`
(the `2×2` LDL certificate written as a sum of squares). -/
lemma blk_eq_gram {x y s : ℚ} (hx : x ≠ 0) :
    blk n x y s = x • vecMulVec (gv n x s) (gv n x s) + ((x * y - s ^ 2) / x) • vecMulVec (e1 n) (e1 n) := by
  ext i j
  simp only [blk, proj_eq, X_apply, gv, e1, Matrix.add_apply, Matrix.smul_apply, diagonal_apply,
    vecMulVec_apply, smul_eq_mul]
  split_ifs <;> first | omega | (field_simp; ring)

/-- A block with positive leading entry and nonnegative determinant is PSD. -/
lemma blk_psd {x y s : ℚ} (hx : 0 < x) (hdet : 0 ≤ x * y - s ^ 2) :
    (toC (blk n x y s)).PosSemidef := by
  rw [blk_eq_gram hx.ne']
  refine gram_sound _ ![x, (x * y - s ^ 2) / x] ![gv n x s, e1 n] ?_ ?_
  · simp [Fin.sum_univ_two]
  · intro k
    fin_cases k <;> simp [hx.le, div_nonneg hdet hx.le]

/-- The `B_I` block of `W_0` at Alice input weight `θa = θ(a)`, sign `za = Z(a)`, and
`Z_d^+`-, `Z_e^+`-signs `σ, τ`. -/
def wblk (n : ℕ) (θa za σ τ : ℚ) : Matrix (Fin n) (Fin n) ℚ :=
  θa • theta n + (σ / 20) • Z n + (za * τ / 20) • X n

lemma wblk_eq_blk (θa za σ τ : ℚ) :
    wblk n θa za σ τ = blk n (θa * (3 / 4) + σ / 20) (θa * (1 / 4) - σ / 20) (za * τ / 20) := by
  ext i j
  simp only [wblk, blk, theta_eq, Z_eq, proj_eq, X_apply, Matrix.add_apply, Matrix.smul_apply,
    diagonal_apply, smul_eq_mul]
  split_ifs <;> first | omega | ring

lemma kron4_theta₁_split (B : Matrix (Fin d) (Fin d) ℚ) (C : Matrix (Fin n) (Fin n) ℚ)
    (D : Matrix (Fin e) (Fin e) ℚ) :
    kron4 (theta m) B C D = (3 / 4 : ℚ) • kron4 (proj m 0) B C D + (1 / 4 : ℚ) • kron4 (proj m 1) B C D := by
  ext x y; simp only [kron4_apply, theta, Matrix.smul_apply, Matrix.add_apply, smul_eq_mul]; ring

lemma kron4_P₁_split (B : Matrix (Fin d) (Fin d) ℚ) (C : Matrix (Fin n) (Fin n) ℚ)
    (D : Matrix (Fin e) (Fin e) ℚ) :
    kron4 (P m) B C D = kron4 (proj m 0) B C D + kron4 (proj m 1) B C D := by
  ext x y; simp only [kron4_apply, P, Matrix.add_apply]; ring

lemma kron4_Z₁_split (B : Matrix (Fin d) (Fin d) ℚ) (C : Matrix (Fin n) (Fin n) ℚ)
    (D : Matrix (Fin e) (Fin e) ℚ) :
    kron4 (Z m) B C D = kron4 (proj m 0) B C D - kron4 (proj m 1) B C D := by
  ext x y; simp only [kron4_apply, Z, Matrix.sub_apply]; ring

lemma kron4_one₂_split (A : Matrix (Fin m) (Fin m) ℚ) (C : Matrix (Fin n) (Fin n) ℚ)
    (D : Matrix (Fin e) (Fin e) ℚ) :
    kron4 A (1 : Matrix (Fin d) (Fin d) ℚ) C D = kron4 A (Pplus d) C D + kron4 A (proj d 1) C D := by
  rw [← kron4_add₂, Pplus, sub_add_cancel]

lemma kron4_Zplus₂_split (A : Matrix (Fin m) (Fin m) ℚ) (C : Matrix (Fin n) (Fin n) ℚ)
    (D : Matrix (Fin e) (Fin e) ℚ) :
    kron4 A (Zplus d) C D = kron4 A (Pplus d) C D - kron4 A (proj d 1) C D := by
  rw [← kron4_sub₂, Pplus, Zplus, two_smul, sub_sub]

lemma kron4_one₄_split (A : Matrix (Fin m) (Fin m) ℚ) (B : Matrix (Fin d) (Fin d) ℚ)
    (C : Matrix (Fin n) (Fin n) ℚ) :
    kron4 A B C (1 : Matrix (Fin e) (Fin e) ℚ) = kron4 A B C (Pplus e) + kron4 A B C (proj e 1) := by
  rw [← kron4_add₄, Pplus, sub_add_cancel]

lemma kron4_Zplus₄_split (A : Matrix (Fin m) (Fin m) ℚ) (B : Matrix (Fin d) (Fin d) ℚ)
    (C : Matrix (Fin n) (Fin n) ℚ) :
    kron4 A B C (Zplus e) = kron4 A B C (Pplus e) - kron4 A B C (proj e 1) := by
  rw [← kron4_sub₄, Pplus, Zplus, two_smul, sub_sub]

/-- **Block decomposition of `W_0`** (`eq:positive-blocks`): eight Kronecker products
`|a⟩⟨a| ⊗ P^σ_d ⊗ block(a,σ,τ) ⊗ P^τ_e`, `a ∈ {0,1}`, `σ, τ ∈ {+, -}`. -/
theorem W0_eq_blocks :
    W0 m d n e
      = kron4 (proj m 0) (Pplus d) (wblk n (3 / 4) 1 1 1) (Pplus e)
        + kron4 (proj m 0) (Pplus d) (wblk n (3 / 4) 1 1 (-1)) (proj e 1)
        + kron4 (proj m 0) (proj d 1) (wblk n (3 / 4) 1 (-1) 1) (Pplus e)
        + kron4 (proj m 0) (proj d 1) (wblk n (3 / 4) 1 (-1) (-1)) (proj e 1)
        + kron4 (proj m 1) (Pplus d) (wblk n (1 / 4) (-1) 1 1) (Pplus e)
        + kron4 (proj m 1) (Pplus d) (wblk n (1 / 4) (-1) 1 (-1)) (proj e 1)
        + kron4 (proj m 1) (proj d 1) (wblk n (1 / 4) (-1) (-1) 1) (Pplus e)
        + kron4 (proj m 1) (proj d 1) (wblk n (1 / 4) (-1) (-1) (-1)) (proj e 1) := by
  simp only [W0, Qtheta_eq_kron4, GA, GB, kron4_theta₁_split, kron4_P₁_split, kron4_Z₁_split,
    kron4_one₂_split, kron4_Zplus₂_split, kron4_one₄_split, kron4_Zplus₄_split, wblk, kron4_add₃,
    kron4_smul₃]
  module

lemma psd_term {A : Matrix (Fin m) (Fin m) ℚ} {B : Matrix (Fin d) (Fin d) ℚ}
    {D : Matrix (Fin e) (Fin e) ℚ} (hA : (toC A).PosSemidef) (hB : (toC B).PosSemidef)
    (hD : (toC D).PosSemidef) {θa za σ τ : ℚ} (hx : 0 < θa * (3 / 4) + σ / 20)
    (hdet : 0 ≤ (θa * (3 / 4) + σ / 20) * (θa * (1 / 4) - σ / 20) - (za * τ / 20) ^ 2) :
    (toC (kron4 A B (wblk n θa za σ τ) D)).PosSemidef := by
  rw [toC_kron4, wblk_eq_blk]
  exact (hA.kronecker hB).kronecker ((blk_psd hx hdet).kronecker hD)

/-- **`W_0 ≥ 0` in every port dimension** (`eq:positive-blocks`, `eq:valid`). -/
theorem w0_psd (m d n e : ℕ) : (toC (W0 m d n e)).PosSemidef := by
  rw [W0_eq_blocks]
  simp only [toC_add]
  refine PosSemidef.add (PosSemidef.add (PosSemidef.add (PosSemidef.add (PosSemidef.add
    (PosSemidef.add (PosSemidef.add ?_ ?_) ?_) ?_) ?_) ?_) ?_) ?_ <;>
  refine psd_term (psd_toC_proj _ _) ?_ ?_ (by norm_num) (by norm_num) <;>
  first | exact psd_toC_Pplus _ | exact psd_toC_proj _ _

end BlockPsd

/-! ### The process equations at the rational level (`eq:LV-a,b,c`)

The three equations of `eq:LV` for `W_0`, `U`, `V` in rational coordinates, using the entry-rule
replacements `RAOq, RBOq, RAIAOq, RBIBOq` of `CausalNonpurifiability.Data.Local`. Together with the bridge lemmas to
the complex replacement maps they give `InLV`. -/

section LVq
variable {m d n e : ℕ}

lemma trace_one_div_self (hd : 0 < d) : trace (1 : Matrix (Fin d) (Fin d) ℚ) / (d : ℚ) = 1 := by
  rw [trace_one, Fintype.card_fin, div_self]
  exact_mod_cast hd.ne'

/-- `eq:LV-c` for `W_0`: `(1 - R_{A_O})(1 - R_{B_O}) W_0 = 0`. -/
theorem W0_LV_c (hd : 0 < d) (he : 0 < e) :
    W0 m d n e - RAOq (W0 m d n e) - RBOq (W0 m d n e) + RAOq (RBOq (W0 m d n e)) = 0 := by
  simp only [W0, Qtheta_eq_kron4, GA, GB, RAOq_add, RBOq_add, RAOq_smul, RBOq_smul, RAOq_kron4,
    RBOq_kron4, trace_one_div_self hd, trace_one_div_self he, one_smul]
  module

/-- `eq:LV-a` for `W_0`: `(1 - R_{A_O}) R_{B_IB_O} W_0 = 0`. -/
theorem W0_LV_a (hn : 2 ≤ n) (hd : 0 < d) :
    RBIBOq (W0 m d n e) - RAOq (RBIBOq (W0 m d n e)) = 0 := by
  simp only [W0, Qtheta_eq_kron4, GA, GB, RBIBOq_add, RBIBOq_smul, RBIBOq_kron4, trace_Z hn,
    trace_X, zero_mul, zero_div, zero_smul, smul_zero, add_zero, RAOq_smul, RAOq_kron4,
    trace_one_div_self hd, one_smul, sub_self]

/-- `eq:LV-b` for `W_0`: `(1 - R_{B_O}) R_{A_IA_O} W_0 = 0`. -/
theorem W0_LV_b (hm : 2 ≤ m) (he : 0 < e) :
    RAIAOq (W0 m d n e) - RBOq (RAIAOq (W0 m d n e)) = 0 := by
  simp only [W0, Qtheta_eq_kron4, GA, GB, RAIAOq_add, RAIAOq_smul, RAIAOq_kron4, trace_Z hm,
    zero_mul, zero_div, zero_smul, add_zero, RBOq_add, RBOq_smul, RBOq_kron4,
    trace_one_div_self he, one_smul, sub_self]

theorem U_LV_c (hd : 0 < d) (he : 0 < e) :
    U m d n e - RAOq (U m d n e) - RBOq (U m d n e) + RAOq (RBOq (U m d n e)) = 0 := by
  simp only [U, Pi, GA, RAOq_add, RBOq_add, RAOq_smul, RBOq_smul, RAOq_kron4, RBOq_kron4,
    trace_one_div_self hd, trace_one_div_self he, one_smul]
  module

theorem U_LV_a (hn : 2 ≤ n) (hd : 0 < d) :
    RBIBOq (U m d n e) - RAOq (RBIBOq (U m d n e)) = 0 := by
  simp only [U, Pi, GA, RBIBOq_add, RBIBOq_smul, RBIBOq_kron4, trace_Z hn, zero_mul, zero_div,
    zero_smul, add_zero, RAOq_smul, RAOq_kron4, trace_one_div_self hd, one_smul, sub_self]

theorem U_LV_b (he : 0 < e) :
    RAIAOq (U m d n e) - RBOq (RAIAOq (U m d n e)) = 0 := by
  simp only [U, Pi, GA, RAIAOq_add, RAIAOq_smul, RAIAOq_kron4, RBOq_add, RBOq_smul, RBOq_kron4,
    trace_one_div_self he, one_smul, sub_self]

theorem V_LV_c (hd : 0 < d) (he : 0 < e) :
    V m d n e - RAOq (V m d n e) - RBOq (V m d n e) + RAOq (RBOq (V m d n e)) = 0 := by
  simp only [V, Pi, GB, RAOq_add, RBOq_add, RAOq_smul, RBOq_smul, RAOq_kron4, RBOq_kron4,
    trace_one_div_self hd, trace_one_div_self he, one_smul]
  module

theorem V_LV_a (hd : 0 < d) :
    RBIBOq (V m d n e) - RAOq (RBIBOq (V m d n e)) = 0 := by
  simp only [V, Pi, GB, RBIBOq_add, RBIBOq_smul, RBIBOq_kron4, trace_X, zero_mul, zero_div,
    zero_smul, add_zero, RAOq_smul, RAOq_kron4, trace_one_div_self hd, one_smul, sub_self]

theorem V_LV_b (hm : 2 ≤ m) (he : 0 < e) :
    RAIAOq (V m d n e) - RBOq (RAIAOq (V m d n e)) = 0 := by
  simp only [V, Pi, GB, RAIAOq_add, RAIAOq_smul, RAIAOq_kron4, trace_Z hm, zero_mul, zero_div,
    zero_smul, add_zero, RBOq_smul, RBOq_kron4, trace_one_div_self he, one_smul, sub_self]

theorem W0_transpose : (W0 m d n e)ᵀ = W0 m d n e := by
  simp only [W0, Qtheta_eq_kron4, transpose_add, transpose_smul, kron4_transpose, theta_transpose,
    transpose_one, GA_transpose, GB_transpose]

theorem U_transpose : (U m d n e)ᵀ = U m d n e := by
  simp only [U, transpose_smul, transpose_add, Pi_transpose, GA_transpose]

theorem V_transpose : (V m d n e)ᵀ = V m d n e := by
  simp only [V, transpose_smul, transpose_add, Pi_transpose, GB_transpose]

theorem W0_isHermitian : (toC (W0 m d n e)).IsHermitian := isHermitian_map_of_transpose _ W0_transpose
theorem U_isHermitian : (toC (U m d n e)).IsHermitian := isHermitian_map_of_transpose _ U_transpose
theorem V_isHermitian : (toC (V m d n e)).IsHermitian := isHermitian_map_of_transpose _ V_transpose

end LVq

/-! ### Bridge to the complex replacement maps and the process definitions

`toC` intertwines the rational entry-rule replacements with the complex-linear maps
`R_AO, R_BO, R_AIAO, R_BIBO` of `CausalNonpurifiability.Linear.Replacement` (both implement `eq:replacement`).
Consequently the rational identities above give `InLV`, `Valid` (`eq:valid`) and the ordered-cone
memberships `U ∈ O_{A≺B}`, `V ∈ O_{B≺A}` (`eq:ordered-cones`) for every `D : Ports` with all
ports `≥ 2`. -/

section Bridge
variable {m d n e : ℕ}

lemma toC_zero {ι κ : Type*} : toC (0 : Matrix ι κ ℚ) = 0 := by
  ext i j; simp

lemma trace_toC {ι : Type*} [Fintype ι] (A : Matrix ι ι ℚ) :
    trace (toC A) = ((trace A : ℚ) : ℂ) := by
  simp [Matrix.trace]

lemma toC_RBOq (T : Matrix (Lab m d n e) (Lab m d n e) ℚ) : toC (RBOq T) = R_BO (toC T) := by
  ext ⟨⟨a, o⟩, ⟨b, t⟩⟩ ⟨⟨a', o'⟩, ⟨b', t'⟩⟩
  rw [R_BO_apply]
  simp only [toC_apply, RBOq, of_apply, invCard, Fintype.card_fin]
  split_ifs
  · push_cast; ring
  · simp

lemma toC_RAOq (T : Matrix (Lab m d n e) (Lab m d n e) ℚ) : toC (RAOq T) = R_AO (toC T) := by
  ext ⟨⟨a, o⟩, ⟨b, t⟩⟩ ⟨⟨a', o'⟩, ⟨b', t'⟩⟩
  rw [R_AO_apply]
  simp only [toC_apply, RAOq, of_apply, invCard, Fintype.card_fin]
  split_ifs
  · push_cast; ring
  · simp

lemma toC_RBIBOq (T : Matrix (Lab m d n e) (Lab m d n e) ℚ) :
    toC (RBIBOq T) = R_BIBO (toC T) := by
  ext ⟨⟨a, o⟩, ⟨b, t⟩⟩ ⟨⟨a', o'⟩, ⟨b', t'⟩⟩
  rw [R_BIBO_apply]
  simp only [toC_apply, RBIBOq, of_apply, invCard, Fintype.card_prod, Fintype.card_fin]
  split_ifs
  · push_cast; ring
  · simp

lemma toC_RAIAOq (T : Matrix (Lab m d n e) (Lab m d n e) ℚ) :
    toC (RAIAOq T) = R_AIAO (toC T) := by
  ext ⟨⟨a, o⟩, ⟨b, t⟩⟩ ⟨⟨a', o'⟩, ⟨b', t'⟩⟩
  rw [R_AIAO_apply]
  simp only [toC_apply, RAIAOq, of_apply, invCard, Fintype.card_prod, Fintype.card_fin]
  split_ifs
  · push_cast; ring
  · simp

end Bridge

section Ports
variable (D : Ports)

/-- `W_0 ∈ L_V` (`eq:LV`) for all ports `≥ 2`. -/
theorem w0_inLV (h : AllPortsGE2 D) : InLV D (toC (W0 D.m D.d D.n D.e)) := by
  obtain ⟨hm, hd, hn, he⟩ := h
  refine ⟨W0_isHermitian, ?_, ?_, ?_⟩
  · rw [← toC_RBIBOq, ← toC_RAOq, ← toC_sub, W0_LV_a hn (by omega), toC_zero]
  · rw [← toC_RAIAOq, ← toC_RBOq, ← toC_sub, W0_LV_b hm (by omega), toC_zero]
  · rw [← toC_RBOq, ← toC_RAOq, ← toC_RAOq, ← toC_sub, ← toC_sub, ← toC_add,
      W0_LV_c (by omega) (by omega), toC_zero]

/-- **`W_0` is a valid process** (`eq:valid`, `thm:main` (i)) for all ports `≥ 2`. -/
theorem w0_valid (h : AllPortsGE2 D) : Valid D (toC (W0 D.m D.d D.n D.e)) := by
  obtain ⟨hm, hd, hn, he⟩ := h
  refine ⟨w0_inLV D ⟨hm, hd, hn, he⟩, w0_psd _ _ _ _, ?_⟩
  rw [trace_toC, trace_W0 hm hn, Rat.cast_natCast]

/-- The four-qubit endpoint `Wq := toC (W0 2 2 2 2)` of `Main` is a valid process. -/
theorem wq_valid : Valid qubits (toC (W0 2 2 2 2)) :=
  w0_valid qubits ⟨le_rfl, le_rfl, le_rfl, le_rfl⟩

theorem u_inLV (h : AllPortsGE2 D) : InLV D (toC (U D.m D.d D.n D.e)) := by
  obtain ⟨hm, hd, hn, he⟩ := h
  refine ⟨U_isHermitian, ?_, ?_, ?_⟩
  · rw [← toC_RBIBOq, ← toC_RAOq, ← toC_sub, U_LV_a hn (by omega), toC_zero]
  · rw [← toC_RAIAOq, ← toC_RBOq, ← toC_sub, U_LV_b (by omega), toC_zero]
  · rw [← toC_RBOq, ← toC_RAOq, ← toC_RAOq, ← toC_sub, ← toC_sub, ← toC_add,
      U_LV_c (by omega) (by omega), toC_zero]

theorem v_inLV (h : AllPortsGE2 D) : InLV D (toC (V D.m D.d D.n D.e)) := by
  obtain ⟨hm, hd, hn, he⟩ := h
  refine ⟨V_isHermitian, ?_, ?_, ?_⟩
  · rw [← toC_RBIBOq, ← toC_RAOq, ← toC_sub, V_LV_a (by omega), toC_zero]
  · rw [← toC_RAIAOq, ← toC_RBOq, ← toC_sub, V_LV_b hm (by omega), toC_zero]
  · rw [← toC_RBOq, ← toC_RAOq, ← toC_RAOq, ← toC_sub, ← toC_sub, ← toC_add,
      V_LV_c (by omega) (by omega), toC_zero]

/-- **`U ∈ O_{A≺B}`** (`eq:UV`, `eq:ordered-cones`). -/
theorem u_orderedAB (h : AllPortsGE2 D) : OrderedAB D (toC (U D.m D.d D.n D.e)) :=
  ⟨u_inLV D h, u_psd, by rw [← toC_RBOq, RBOq_U D.e_pos]⟩

/-- **`V ∈ O_{B≺A}`** (`eq:UV`, `eq:ordered-cones`). -/
theorem v_orderedBA (h : AllPortsGE2 D) : OrderedBA D (toC (V D.m D.d D.n D.e)) :=
  ⟨v_inLV D h, v_psd h.2.2.1, by rw [← toC_RAOq, RAOq_V D.d_pos]⟩

/-- Bridge for the first-party ordered marginal: `toC (ω_A^ℚ T) = ω_A D (toC T)`
(`eq:ordered-marginal`). -/
theorem toC_omegaAq (T : Matrix (Lab D.m D.d D.n D.e) (Lab D.m D.d D.n D.e) ℚ) :
    toC (omegaAq T) = omegaA D (toC T) := by
  ext a a'
  rw [omegaA_apply]
  simp only [toC_apply, omegaAq, Matrix.smul_apply, of_apply, smul_eq_mul]
  push_cast
  ring

/-- Bridge for the second-party ordered marginal: `toC (ω_B^ℚ T) = ω_B D (toC T)`. -/
theorem toC_omegaBq (T : Matrix (Lab D.m D.d D.n D.e) (Lab D.m D.d D.n D.e) ℚ) :
    toC (omegaBq T) = omegaB D (toC T) := by
  ext b b'
  rw [omegaB_apply]
  simp only [toC_apply, omegaBq, Matrix.smul_apply, of_apply, smul_eq_mul]
  push_cast
  ring

/-- `ω_A(U) = P_m/10` in the complex process space (`eq:reference-states`). -/
theorem omegaA_toC_U (h : AllPortsGE2 D) :
    omegaA D (toC (U D.m D.d D.n D.e)) = toC ((1 / 10 : ℚ) • P D.m) := by
  rw [← toC_omegaAq, omegaAq_U h.2.2.1 (by have := h.2.1; omega) (by have := h.2.2.2; omega)]

/-- `ω_B(V) = P_n/10` in the complex process space (`eq:reference-states`). -/
theorem omegaB_toC_V (h : AllPortsGE2 D) :
    omegaB D (toC (V D.m D.d D.n D.e)) = toC ((1 / 10 : ℚ) • P D.n) := by
  rw [← toC_omegaBq, omegaBq_V h.1 (by have := h.2.1; omega) (by have := h.2.2.2; omega)]

/-- `W_0 = U + V + 2 Q_C` in the complex process space (`eq:signed-decomposition`). -/
theorem signed_decomposition_toC :
    toC (W0 D.m D.d D.n D.e)
      = toC (U D.m D.d D.n D.e) + toC (V D.m D.d D.n D.e)
        + ((2 : ℚ) : ℂ) • toC (Qembed D.d D.e (C D.m D.n)) := by
  rw [← toC_smul, ← toC_add, ← toC_add, ← signed_decomposition]

end Ports

/-! ### Real `2×2` blocks over `ℂ` (shared by `eq:qubit-minimum` and `eq:witness-size`) -/

section RealBlocks

/-- Sum over `Fin r`, `r ≥ 2`, of a function vanishing above index `1` (general codomain). -/
lemma sum_fin_of_two_le' {M : Type*} [AddCommMonoid M] {r : ℕ} (hr : 2 ≤ r) (f : Fin r → M)
    (hf : ∀ i : Fin r, 2 ≤ i.val → f i = 0) :
    ∑ i, f i = f ⟨0, by omega⟩ + f ⟨1, by omega⟩ := by
  obtain ⟨k, rfl⟩ : ∃ k, r = k + 2 := ⟨r - 2, by omega⟩
  rw [Fin.sum_univ_succ, Fin.sum_univ_succ,
    Finset.sum_eq_zero (fun i _ => hf _ (by simp [Fin.val_succ]))]
  have h0 : (⟨0, by omega⟩ : Fin (k + 2)) = 0 := Fin.ext (by simp)
  have h1 : (⟨1, by omega⟩ : Fin (k + 2)) = 1 := Fin.ext (by simp)
  rw [h0, h1, Fin.succ_zero_eq_one, add_zero]

/-- Rank-one positivity `u uᴴ ≥ 0` over `ℂ`. -/
lemma psd_vecMulVec_star {ι : Type} [Fintype ι] (u : ι → ℂ) :
    (vecMulVec u (star u)).PosSemidef := by
  have e : vecMulVec u (star u)
      = (of fun i (_ : Fin 1) => u i) * (of fun i (_ : Fin 1) => u i)ᴴ := by
    ext i j; simp [mul_apply, vecMulVec_apply, conjTranspose_apply]
  rw [e]
  exact posSemidef_self_mul_conjTranspose _

/-- The padded real `2×2` block `x|0⟩⟨0| + y|1⟩⟨1| + s(|0⟩⟨1| + |1⟩⟨0|)` on `Fin n`, over `ℂ`. -/
noncomputable def blkC (n : ℕ) (x y s : ℝ) : Matrix (Fin n) (Fin n) ℂ :=
  of fun i j =>
    if i = j then (if i.val = 0 then (x : ℂ) else if i.val = 1 then (y : ℂ) else 0)
    else (if (i.val = 0 ∧ j.val = 1) ∨ (i.val = 1 ∧ j.val = 0) then (s : ℂ) else 0)

lemma toC_blk (n : ℕ) (x y s : ℚ) : toC (blk n x y s) = blkC n x y s := by
  ext i j
  simp only [toC_apply, blk, blkC, of_apply, proj_eq, X_apply, Matrix.add_apply, Matrix.smul_apply,
    diagonal_apply, smul_eq_mul]
  split_ifs <;> first | omega | (push_cast; ring)

lemma blkC_sub (n : ℕ) (x y s x' y' s' : ℝ) :
    blkC n x y s - blkC n x' y' s' = blkC n (x - x') (y - y') (s - s') := by
  ext i j
  simp only [blkC, of_apply, Matrix.sub_apply]
  split_ifs <;> push_cast <;> ring

lemma blkC_add (n : ℕ) (x y s x' y' s' : ℝ) :
    blkC n x y s + blkC n x' y' s' = blkC n (x + x') (y + y') (s + s') := by
  ext i j
  simp only [blkC, of_apply, Matrix.add_apply]
  split_ifs <;> push_cast <;> ring

lemma trace_blkC {n : ℕ} (hn : 2 ≤ n) (x y s : ℝ) : trace (blkC n x y s) = ((x + y : ℝ) : ℂ) := by
  simp only [trace, diag_apply, blkC, of_apply, if_true]
  rw [sum_fin_of_two_le' hn]
  · simp
  · intro i hi; split_ifs <;> first | omega | rfl

/-- A padded real `2×2` block with positive leading entry and nonnegative determinant is PSD
(Gram form `x⁻¹ (x, s)(x, s)ᵀ + ((xy - s²)/x) e₁e₁ᵀ`). -/
theorem blkC_psd {n : ℕ} {x y s : ℝ} (hx : 0 < x) (hdet : 0 ≤ x * y - s ^ 2) :
    (blkC n x y s).PosSemidef := by
  have hx' : (x : ℂ) ≠ 0 := by exact_mod_cast hx.ne'
  have e : blkC n x y s
      = ((x⁻¹ : ℝ) : ℂ) • vecMulVec (fun i : Fin n => if i.val = 0 then (x : ℂ) else if i.val = 1 then (s : ℂ) else 0)
          (star fun i : Fin n => if i.val = 0 then (x : ℂ) else if i.val = 1 then (s : ℂ) else 0)
        + (((x * y - s ^ 2) / x : ℝ) : ℂ) • vecMulVec (fun i : Fin n => if i.val = 1 then (1 : ℂ) else 0)
          (star fun i : Fin n => if i.val = 1 then (1 : ℂ) else 0) := by
    ext i j
    simp only [blkC, of_apply, Matrix.add_apply, Matrix.smul_apply, vecMulVec_apply, Pi.star_apply,
      smul_eq_mul, Complex.star_def]
    split_ifs <;>
      first
      | omega
      | (simp [Complex.conj_ofReal]; done)
      | (simp [Complex.conj_ofReal]; field_simp; try ring)
  rw [e]
  exact ((psd_vecMulVec_star _).smul (Complex.zero_le_real.mpr (inv_nonneg.mpr hx.le))).add
    ((psd_vecMulVec_star _).smul (Complex.zero_le_real.mpr (div_nonneg hdet hx.le)))

/-- Kronecker bilinearity over `ℂ` (subtraction, right factor). -/
lemma kron_sub_right {l m n p : Type} (A : Matrix l m ℂ) (B C : Matrix n p ℂ) :
    A ⊗ₖ (B - C) = A ⊗ₖ B - A ⊗ₖ C := by
  ext ⟨i, k⟩ ⟨j, l⟩; simp [kroneckerMap_apply]; ring

/-- Kronecker bilinearity over `ℂ` (subtraction, left factor). -/
lemma kron_sub_left {l m n p : Type} (A B : Matrix l m ℂ) (C : Matrix n p ℂ) :
    (A - B) ⊗ₖ C = A ⊗ₖ C - B ⊗ₖ C := by
  ext ⟨i, k⟩ ⟨j, l⟩; simp [kroneckerMap_apply]; ring

end RealBlocks

/-! ### The exact minimum eigenvalue of `W_q` (`eq:qubit-minimum`)

`λ_min(W_q) = (10 - √97)/80`: the block `(19, ±4; ±4, 1)/80` of `eq:positive-blocks` has
characteristic polynomial `μ² - 20μ + 3` (in units of `1/80`) with roots `10 ± √97`, attained by
the eigenvector `(4, μ - 19)`; the other three block types have strictly larger least eigenvalues
(`(60 - √1508)/2`, `(60 - √548)/2`, `(20 - √68)/2`, all `≫ 0.151`). -/

section ExactMinimum

/-- `λ_min(W_q) = (10 - √97)/80` (`eq:qubit-minimum`). -/
noncomputable def lamMin : ℝ := (10 - Real.sqrt 97) / 80

lemma sqrt97_sq : Real.sqrt 97 ^ 2 = 97 := Real.sq_sqrt (by norm_num)
lemma sqrt97_lt_ten : Real.sqrt 97 < 10 := by nlinarith [sqrt97_sq, Real.sqrt_nonneg 97]
lemma nine_lt_sqrt97 : 9 < Real.sqrt 97 := by nlinarith [sqrt97_sq, Real.sqrt_nonneg 97]

/-- `λ_min(W_q) > 0` (`eq:qubit-minimum`). -/
theorem wq_lamMin_pos : 0 < lamMin :=
  div_pos (by linarith [sqrt97_lt_ten]) (by norm_num)

lemma P_two : P 2 = 1 := by decide +kernel

lemma toC_blk_two_sub (x y s : ℚ) (c : ℝ) :
    toC (blk 2 x y s) - (c : ℂ) • (1 : Matrix (Fin 2) (Fin 2) ℂ) = blkC 2 (x - c) (y - c) s := by
  rw [toC_blk]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [blkC, one_apply]

/-- A shifted `2×2` block `B - c·I` with `c < B₀₀` and `det(B - cI) ≥ 0` is PSD. -/
lemma block_shift_psd (x y s : ℚ) (c : ℝ) (hx : c < x)
    (hdet : 0 ≤ ((x : ℝ) - c) * ((y : ℝ) - c) - (s : ℝ) ^ 2) :
    (toC (blk 2 x y s) - (c : ℂ) • (1 : Matrix (Fin 2) (Fin 2) ℂ)).PosSemidef := by
  rw [toC_blk_two_sub]
  exact blkC_psd (by linarith) hdet

/-- The identity on the four-qubit lab index, in the eight-block form of `W0_eq_blocks`. -/
lemma one_eq_blocks_qubit :
    (1 : Matrix (Lab 2 2 2 2) (Lab 2 2 2 2) ℚ)
      = kron4 (proj 2 0) (Pplus 2) (P 2) (Pplus 2) + kron4 (proj 2 0) (Pplus 2) (P 2) (proj 2 1)
        + kron4 (proj 2 0) (proj 2 1) (P 2) (Pplus 2) + kron4 (proj 2 0) (proj 2 1) (P 2) (proj 2 1)
        + kron4 (proj 2 1) (Pplus 2) (P 2) (Pplus 2) + kron4 (proj 2 1) (Pplus 2) (P 2) (proj 2 1)
        + kron4 (proj 2 1) (proj 2 1) (P 2) (Pplus 2) + kron4 (proj 2 1) (proj 2 1) (P 2) (proj 2 1) := by
  decide +kernel

/-- Shifted block term: `(A⊗B)⊗(C⊗D) - c·(A⊗B)⊗(C'⊗D) = (A⊗B)⊗((C - c·C')⊗D)`. -/
lemma kron_shift {A B C C' D : Matrix (Fin 2) (Fin 2) ℂ} (c : ℂ) :
    (A ⊗ₖ B) ⊗ₖ (C ⊗ₖ D) - c • ((A ⊗ₖ B) ⊗ₖ (C' ⊗ₖ D)) = (A ⊗ₖ B) ⊗ₖ ((C - c • C') ⊗ₖ D) := by
  rw [kron_sub_left, smul_kronecker, kron_sub_right, kronecker_smul]

/-- Positivity of a shifted block of `W_0` at four qubits. -/
lemma wblk_shift_psd (θa za σ τ : ℚ) (hx : lamMin < ((θa * (3 / 4) + σ / 20 : ℚ) : ℝ))
    (hdet : 0 ≤ (((θa * (3 / 4) + σ / 20 : ℚ) : ℝ) - lamMin) *
      (((θa * (1 / 4) - σ / 20 : ℚ) : ℝ) - lamMin) - ((za * τ / 20 : ℚ) : ℝ) ^ 2) :
    (toC (wblk 2 θa za σ τ) - (lamMin : ℂ) • toC (P 2)).PosSemidef := by
  rw [P_two, toC_one, wblk_eq_blk]
  exact block_shift_psd _ _ _ _ hx hdet

/-- **`W_0 - λ_min I ≥ 0` at four qubits** (blockwise, `eq:qubit-minimum`). -/
theorem w0_qubit_sub_lamMin_psd :
    (toC (W0 2 2 2 2) - (lamMin : ℂ) • (1 : Matrix (Lab 2 2 2 2) (Lab 2 2 2 2) ℂ)).PosSemidef := by
  have hone : (1 : Matrix (Lab 2 2 2 2) (Lab 2 2 2 2) ℂ) = toC 1 := toC_one.symm
  rw [hone, W0_eq_blocks, one_eq_blocks_qubit]
  simp only [toC_add, toC_kron4, smul_add]
  have e : ∀ (A B C C' D : Matrix (Fin 2) (Fin 2) ℂ),
      (A ⊗ₖ B) ⊗ₖ ((C - (lamMin : ℂ) • C') ⊗ₖ D)
        = (A ⊗ₖ B) ⊗ₖ (C ⊗ₖ D) - (lamMin : ℂ) • ((A ⊗ₖ B) ⊗ₖ (C' ⊗ₖ D)) :=
    fun A B C C' D => (kron_shift (lamMin : ℂ)).symm
  have key : ∀ (θa za σ τ : ℚ) (A B D : Matrix (Fin 2) (Fin 2) ℚ),
      (toC A).PosSemidef → (toC B).PosSemidef → (toC D).PosSemidef →
      (toC (wblk 2 θa za σ τ) - (lamMin : ℂ) • toC (P 2)).PosSemidef →
      ((toC A ⊗ₖ toC B) ⊗ₖ (toC (wblk 2 θa za σ τ) ⊗ₖ toC D)
        - (lamMin : ℂ) • ((toC A ⊗ₖ toC B) ⊗ₖ (toC (P 2) ⊗ₖ toC D))).PosSemidef := by
    intro θa za σ τ A B D hA hB hD hblk
    rw [← e]
    exact (hA.kronecker hB).kronecker (hblk.kronecker hD)
  have h1 := key (3 / 4) 1 1 1 _ _ _ (psd_toC_proj 2 0) (psd_toC_Pplus 2) (psd_toC_Pplus 2)
    (wblk_shift_psd _ _ _ _ (by unfold lamMin; push_cast; linarith [nine_lt_sqrt97])
      (by unfold lamMin; push_cast; nlinarith [sqrt97_sq, nine_lt_sqrt97, sqrt97_lt_ten]))
  have h2 := key (3 / 4) 1 1 (-1) _ _ _ (psd_toC_proj 2 0) (psd_toC_Pplus 2) (psd_toC_proj 2 1)
    (wblk_shift_psd _ _ _ _ (by unfold lamMin; push_cast; linarith [nine_lt_sqrt97])
      (by unfold lamMin; push_cast; nlinarith [sqrt97_sq, nine_lt_sqrt97, sqrt97_lt_ten]))
  have h3 := key (3 / 4) 1 (-1) 1 _ _ _ (psd_toC_proj 2 0) (psd_toC_proj 2 1) (psd_toC_Pplus 2)
    (wblk_shift_psd _ _ _ _ (by unfold lamMin; push_cast; linarith [nine_lt_sqrt97])
      (by unfold lamMin; push_cast; nlinarith [sqrt97_sq, nine_lt_sqrt97, sqrt97_lt_ten]))
  have h4 := key (3 / 4) 1 (-1) (-1) _ _ _ (psd_toC_proj 2 0) (psd_toC_proj 2 1) (psd_toC_proj 2 1)
    (wblk_shift_psd _ _ _ _ (by unfold lamMin; push_cast; linarith [nine_lt_sqrt97])
      (by unfold lamMin; push_cast; nlinarith [sqrt97_sq, nine_lt_sqrt97, sqrt97_lt_ten]))
  have h5 := key (1 / 4) (-1) 1 1 _ _ _ (psd_toC_proj 2 1) (psd_toC_Pplus 2) (psd_toC_Pplus 2)
    (wblk_shift_psd _ _ _ _ (by unfold lamMin; push_cast; linarith [nine_lt_sqrt97])
      (by unfold lamMin; push_cast; nlinarith [sqrt97_sq, nine_lt_sqrt97, sqrt97_lt_ten]))
  have h6 := key (1 / 4) (-1) 1 (-1) _ _ _ (psd_toC_proj 2 1) (psd_toC_Pplus 2) (psd_toC_proj 2 1)
    (wblk_shift_psd _ _ _ _ (by unfold lamMin; push_cast; linarith [nine_lt_sqrt97])
      (by unfold lamMin; push_cast; nlinarith [sqrt97_sq, nine_lt_sqrt97, sqrt97_lt_ten]))
  have h7 := key (1 / 4) (-1) (-1) 1 _ _ _ (psd_toC_proj 2 1) (psd_toC_proj 2 1) (psd_toC_Pplus 2)
    (wblk_shift_psd _ _ _ _ (by unfold lamMin; push_cast; linarith [nine_lt_sqrt97])
      (by unfold lamMin; push_cast; nlinarith [sqrt97_sq, nine_lt_sqrt97, sqrt97_lt_ten]))
  have h8 := key (1 / 4) (-1) (-1) (-1) _ _ _ (psd_toC_proj 2 1) (psd_toC_proj 2 1) (psd_toC_proj 2 1)
    (wblk_shift_psd _ _ _ _ (by unfold lamMin; push_cast; linarith [nine_lt_sqrt97])
      (by unfold lamMin; push_cast; nlinarith [sqrt97_sq, nine_lt_sqrt97, sqrt97_lt_ten]))
  have total := ((((((h1.add h2).add h3).add h4).add h5).add h6).add h7).add h8
  convert total using 1
  abel

/-- **`W_q - λ_min I ≥ 0`** (`eq:qubit-minimum`): `λ_min = (10 - √97)/80` is a lower bound of the
spectrum of `W_q`. -/
theorem wq_sub_lamMin_psd :
    (toC WqEntries - (lamMin : ℂ) • (1 : Matrix (Fin 16) (Fin 16) ℂ)).PosSemidef := by
  have e : toC WqEntries - (lamMin : ℂ) • (1 : Matrix (Fin 16) (Fin 16) ℂ)
      = (toC (W0 2 2 2 2) - (lamMin : ℂ) • 1).submatrix qubitFlat.symm qubitFlat.symm := by
    rw [wq_entries_eq_pauli, reindex_apply]
    ext i j
    simp only [Matrix.sub_apply, Matrix.smul_apply, submatrix_apply, toC_apply, one_apply,
      EmbeddingLike.apply_eq_iff_eq]
  rw [e]
  exact (posSemidef_submatrix_equiv _).mpr w0_qubit_sub_lamMin_psd

/-- Column `9` of `80 W_q` (index `j(1,0,0,1)`). -/
def col9 : Fin 16 → ℚ := ![0, 0, 0, 0, 0, 0, 0, 0, 0, 19, 0, 4, 0, 0, 0, 0]
/-- Column `11` of `80 W_q` (index `j(1,0,1,1)`). -/
def col11 : Fin 16 → ℚ := ![0, 0, 0, 0, 0, 0, 0, 0, 0, 4, 0, 1, 0, 0, 0, 0]

lemma Wq80_col9 : ∀ j, Wq80 j 9 = col9 j := by decide +kernel
lemma Wq80_col11 : ∀ j, Wq80 j 11 = col11 j := by decide +kernel

/-- The eigenvector `(4, μ - 19)`, `μ = 10 - √97`, on the block `j ∈ {9, 11}` of `W_q`. -/
noncomputable def vmin : Fin 16 → ℂ :=
  fun j => if j = 9 then 4 else if j = 11 then ((10 - Real.sqrt 97 - 19 : ℝ) : ℂ) else 0

/-- **`λ_min` is attained** (`eq:qubit-minimum`): `W_q v = λ_min v` for the nonzero vector `vmin`;
together with `wq_sub_lamMin_psd`, `λ_min(W_q) = (10 - √97)/80` exactly. -/
theorem wq_lamMin_attained :
    ∃ v : Fin 16 → ℂ, v ≠ 0 ∧ (toC WqEntries - (lamMin : ℂ) • 1) *ᵥ v = 0 := by
  refine ⟨vmin, ?_, ?_⟩
  · intro h
    have := congrFun h 9
    simp [vmin] at this
  · have hs : ((Real.sqrt 97 : ℝ) : ℂ) ^ 2 = 97 := by
      rw [← Complex.ofReal_pow, sqrt97_sq]; norm_num
    ext j
    simp only [Matrix.mulVec, dotProduct, Pi.zero_apply]
    rw [Finset.sum_eq_add (9 : Fin 16) 11 (by decide)
      (fun c _ hc => by simp [vmin, hc.1, hc.2]) (by simp) (by simp)]
    simp only [Matrix.sub_apply, Matrix.smul_apply, toC_apply, WqEntries, Matrix.smul_apply,
      Wq80_col9, Wq80_col11, one_apply, smul_eq_mul, vmin, lamMin]
    fin_cases j <;> simp [col9, col11] <;>
      first
      | linear_combination (-1 / 80 : ℂ) * hs
      | linear_combination (1 / 80 : ℂ) * hs
      | ring

end ExactMinimum

/-! ### The actual input marginal (`eq:actual-input`) -/

section ActualInput
variable {m d n e : ℕ}

lemma ptrOut_apply (T : Matrix (Lab m d n e) (Lab m d n e) ℚ) (x y : Fin m × Fin n) :
    ptrOut T x y = ∑ o, ∑ t, T ((x.1, o), (x.2, t)) ((y.1, o), (y.2, t)) := rfl

lemma ptrOut_kron4 (A : Matrix (Fin m) (Fin m) ℚ) (B : Matrix (Fin d) (Fin d) ℚ)
    (C : Matrix (Fin n) (Fin n) ℚ) (D : Matrix (Fin e) (Fin e) ℚ) :
    ptrOut (kron4 A B C D) = (trace B * trace D) • (A ⊗ₖ C) := by
  ext ⟨a, b⟩ ⟨a', b'⟩
  simp only [ptrOut_apply, kron4_apply, Matrix.smul_apply, kroneckerMap_apply, smul_eq_mul,
    trace, diag_apply]
  rw [Finset.sum_mul_sum]
  simp only [Finset.sum_mul]
  refine Finset.sum_congr rfl fun o _ => Finset.sum_congr rfl fun t _ => by ring

lemma ptrOut_add (T T' : Matrix (Lab m d n e) (Lab m d n e) ℚ) :
    ptrOut (T + T') = ptrOut T + ptrOut T' := by
  ext x y
  simp only [ptrOut_apply, Matrix.add_apply, Finset.sum_add_distrib]

lemma ptrOut_smul (c : ℚ) (T : Matrix (Lab m d n e) (Lab m d n e) ℚ) :
    ptrOut (c • T) = c • ptrOut T := by
  ext x y
  simp only [ptrOut_apply, Matrix.smul_apply, smul_eq_mul, Finset.mul_sum]

lemma trace_Zplus {r : ℕ} (hr : 2 ≤ r) : trace (Zplus r) = r - 2 := by
  rw [Zplus_eq, trace_diagonal]
  have h : ∀ i : Fin r, (if i.val = 1 then (-1 : ℚ) else 1) = 1 - (if i.val = 1 then 2 else 0) := by
    intro i; split_ifs <;> norm_num
  simp only [h, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul, mul_one]
  rw [sum_fin_of_two_le hr]
  · norm_num
  · intro i hi; split_ifs <;> first | omega | rfl

/-- **`eq:actual-input`** (regression theorem, not used in the EC proof — the development uses
`χ_A = θ_m/2` directly): the normalized input marginal of `W_0` is
`θ_m ⊗ θ_n + ((d-2)/(20d)) P_m ⊗ Z_n + ((e-2)/(20e)) Z_m ⊗ X_n`; it is a product state only for
`d = e = 2`. -/
theorem actual_input (hd : 2 ≤ d) (he : 2 ≤ e) :
    (1 / ((d : ℚ) * e)) • ptrOut (W0 m d n e)
      = theta m ⊗ₖ theta n + ((d - 2 : ℚ) / (20 * d)) • (P m ⊗ₖ Z n)
        + ((e - 2 : ℚ) / (20 * e)) • (Z m ⊗ₖ X n) := by
  have hd' : (d : ℚ) ≠ 0 := by exact_mod_cast (by omega : d ≠ 0)
  have he' : (e : ℚ) ≠ 0 := by exact_mod_cast (by omega : e ≠ 0)
  rw [W0, Qtheta_eq_kron4, GA, GB, ptrOut_add, ptrOut_smul, ptrOut_add, ptrOut_kron4, ptrOut_kron4,
    ptrOut_kron4, trace_one, trace_one, Fintype.card_fin, Fintype.card_fin, trace_Zplus hd,
    trace_Zplus he]
  ext x y
  simp only [Matrix.smul_apply, Matrix.add_apply, smul_eq_mul]
  field_simp
  ring

end ActualInput

end CausalNonpurifiability
