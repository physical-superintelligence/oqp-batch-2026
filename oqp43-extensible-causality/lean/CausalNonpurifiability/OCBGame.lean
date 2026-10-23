module

public import CausalNonpurifiability.OCB
public import CausalNonpurifiability.Bias
public import CausalNonpurifiability.BellCHSH
public import CausalNonpurifiability.Classes
public import CausalNonpurifiability.Robustness
public import CausalNonpurifiability.Definitions.OCBGame
public import CausalNonpurifiability.Definitions.Separability

@[expose] public section


/-!
# `CausalNonpurifiability.OCBGame`

`intro:WOCB` and Appendix C: `W_OCB` is a process,
every causal distribution wins the game of [OCB] (`ocbWin`) with probability at most `3/4`, and
`W_OCB` wins it with probability `(2 + √2)/4` with the instruments of [OCB]:

* Alice measures `A_I` in the computational basis (outcome `a`) and prepares `|x⟩` on `A_O`;
* Bob, for `g = 0`, measures `B_I` in the computational basis (outcome `b`) and prepares `|0⟩`;
  for `g = 1` he measures `B_I` in the basis `|+⟩, |-⟩` (outcome `b`) and prepares `|y ⊕ b⟩`.

Hence `W_OCB` is not a causal process, and therefore neither extensibly causal nor causally
separable.

Proof outline. The causal bound: for a component without signalling from Bob to Alice, Alice's
guess of Bob's bit is right with probability `1/2`; mirrored for the other order. The value: the
Born probabilities split into a rational part of `I` and one of `IZZI + ZIXZ`, and the two
rational winning sums (`ocbGameQ`) are evaluated by the kernel, as in `OCB.lean`. Validity:
`W_OCB = (1 + A)/4` with `A = (IZZI + ZIXZ)/√2` Hermitian and `A² = 1`, so `(1 + A)² = 2(1 + A)`;
the conditions of `L_V` come from those of `Π` and of `G_A + G_B` (at four qubits `Π = I`,
`G_A = IZZI`, `G_B = ZIXZ`).
-/

set_option autoImplicit false

open Matrix
open scoped Kronecker ComplexOrder

namespace CausalNonpurifiability

/-! ### The causal bound `3/4` -/

section Bound

variable {q : Prob (Fin 2) (Fin 2 × Fin 2) (Fin 2) (Fin 2)}

/-- Without signalling from Bob to Alice the game is won with probability at most `3/4`. -/
theorem ocbWin_le_of_NS_AB (hq : Conditional q) (hns : NS_AB q) : ocbWin q ≤ 3 / 4 := by
  have h0 : ∀ x y : Fin 2, ∑ a : Fin 2, q x (y, 0) a x ≤ 1 := fun x y =>
    calc ∑ a : Fin 2, q x (y, 0) a x ≤ ∑ a : Fin 2, ∑ b : Fin 2, q x (y, 0) a b :=
          Finset.sum_le_sum fun a _ =>
            Finset.single_le_sum (fun b _ => hq.1 x (y, 0) a b) (Finset.mem_univ x)
      _ = 1 := hq.2 x (y, 0)
  have h1 : ∀ x : Fin 2, ∑ y : Fin 2, ∑ b : Fin 2, q x (y, 1) y b = 1 := fun x =>
    calc ∑ y : Fin 2, ∑ b : Fin 2, q x (y, 1) y b = ∑ y : Fin 2, ∑ b : Fin 2, q x (0, 1) y b :=
          Finset.sum_congr rfl fun y _ => hns x (y, 1) (0, 1) y
      _ = 1 := hq.2 x (0, 1)
  have e00 := h0 0 0
  have e01 := h0 0 1
  have e10 := h0 1 0
  have e11 := h0 1 1
  have f0 := h1 0
  have f1 := h1 1
  simp only [ocbWin, Fin.sum_univ_two] at e00 e01 e10 e11 f0 f1 ⊢
  linarith

/-- Without signalling from Alice to Bob the game is won with probability at most `3/4`. -/
theorem ocbWin_le_of_NS_BA (hq : Conditional q) (hns : NS_BA q) : ocbWin q ≤ 3 / 4 := by
  have h0 : ∀ y : Fin 2, ∑ x : Fin 2, ∑ a : Fin 2, q x (y, 0) a x = 1 := fun y =>
    calc ∑ x : Fin 2, ∑ a : Fin 2, q x (y, 0) a x = ∑ x : Fin 2, ∑ a : Fin 2, q 0 (y, 0) a x :=
          Finset.sum_congr rfl fun x _ => hns x 0 (y, 0) x
      _ = ∑ a : Fin 2, ∑ x : Fin 2, q 0 (y, 0) a x := Finset.sum_comm
      _ = 1 := hq.2 0 (y, 0)
  have h1 : ∀ x y : Fin 2, ∑ b : Fin 2, q x (y, 1) y b ≤ 1 := fun x y =>
    calc ∑ b : Fin 2, q x (y, 1) y b ≤ ∑ a : Fin 2, ∑ b : Fin 2, q x (y, 1) a b :=
          Finset.single_le_sum (f := fun a => ∑ b : Fin 2, q x (y, 1) a b)
            (fun a _ => Finset.sum_nonneg fun b _ => hq.1 x (y, 1) a b) (Finset.mem_univ y)
      _ = 1 := hq.2 x (y, 1)
  have e0 := h0 0
  have e1 := h0 1
  have f00 := h1 0 0
  have f01 := h1 0 1
  have f10 := h1 1 0
  have f11 := h1 1 1
  simp only [ocbWin, Fin.sum_univ_two] at e0 e1 f00 f01 f10 f11 ⊢
  linarith

end Bound

/-- **The causal inequality of [OCB]**: every causal distribution wins with probability at most
`3/4`. -/
theorem ocbWin_le_of_causal {p : Prob (Fin 2) (Fin 2 × Fin 2) (Fin 2) (Fin 2)} (hp : Causal p) :
    ocbWin p ≤ 3 / 4 := by
  obtain ⟨lam, pAB, pBA, h0, h1, hAB, hBA, hnsAB, hnsBA, hdec⟩ := hp
  have hsplit : ocbWin p = lam * ocbWin pAB + (1 - lam) * ocbWin pBA := by
    simp only [ocbWin, Fin.sum_univ_two, hdec]
    ring
  rw [hsplit]
  have hA := ocbWin_le_of_NS_AB hAB hnsAB
  have hB := ocbWin_le_of_NS_BA hBA hnsBA
  linarith [mul_le_mul_of_nonneg_left hA h0, mul_le_mul_of_nonneg_left hB (sub_nonneg.mpr h1)]

/-! ### Relabelling settings -/

/-- The same instrument with its settings relabelled by `f`. -/
def Instrument.comap {I O X X' A : Type} [Fintype I] [Fintype O] [Fintype A] [DecidableEq I]
    (M : Instrument I O X A) (f : X' → X) : Instrument I O X' A where
  elem x a := M.elem (f x) a
  positive x a := M.positive (f x) a
  normalized x := M.normalized (f x)

/-- Relabelling Bob's settings preserves causality. -/
theorem Causal.comp_settings {X Y Y' A B : Type} [Fintype A] [Fintype B] {p : Prob X Y A B}
    (h : Causal p) (g : Y' → Y) : Causal (fun x y a b => p x (g y) a b) := by
  obtain ⟨lam, pAB, pBA, h0, h1, hAB, hBA, hnsAB, hnsBA, hdec⟩ := h
  exact ⟨lam, fun x y a b => pAB x (g y) a b, fun x y a b => pBA x (g y) a b, h0, h1,
    ⟨fun x y a b => hAB.1 x (g y) a b, fun x y => hAB.2 x (g y)⟩,
    ⟨fun x y a b => hBA.1 x (g y) a b, fun x y => hBA.2 x (g y)⟩,
    fun x y y' a => hnsAB x (g y) (g y') a, fun x x' y b => hnsBA x x' (g y) b,
    fun x y a b => hdec x (g y) a b⟩

/-- If the distribution of Bob's instrument with settings relabelled by `f` is causal and `f` has
a right inverse `g`, the distribution of the instrument itself is causal. -/
theorem causal_born_comap (D : Ports) {X Y Y' A B : Type} [Fintype A] [Fintype B] (W : PMat D)
    (M : Instrument (Fin D.m) (Fin D.d) X A) (N : Instrument (Fin D.n) (Fin D.e) Y B)
    (f : Y' → Y) (g : Y → Y') (hfg : ∀ y, f (g y) = y)
    (h : Causal (born D W M (N.comap f))) : Causal (born D W M N) := by
  have h2 := h.comp_settings g
  have e : (fun x y a b => born D W M (N.comap f) x (g y) a b) = born D W M N := by
    funext x y a b
    show born D W M N x (f (g y)) a b = born D W M N x y a b
    rw [hfg]
  rwa [e] at h2

/-- Bob's settings `(y, g)` as the single setting `y + 2g`. -/
def ocbEnc (y : Fin 2 × Fin 2) : Fin 4 :=
  ⟨y.1.val + 2 * y.2.val, by have := y.1.isLt; have := y.2.isLt; omega⟩

/-- The inverse of `ocbEnc`. -/
def ocbDec (y : Fin 4) : Fin 2 × Fin 2 :=
  (⟨y.val % 2, Nat.mod_lt _ (by norm_num)⟩, ⟨y.val / 2, by have := y.isLt; omega⟩)

theorem ocbDec_enc : ∀ y : Fin 2 × Fin 2, ocbDec (ocbEnc y) = y := by decide +kernel

/-! ### The instruments of [OCB] -/

/-- Alice's operation for setting `x` and outcome `a`: `|a⟩⟨a| ⊗ |x⟩⟨x|` (measure `A_I` in the
computational basis, prepare `|x⟩` on `A_O`). -/
def ocbAliceQ (x a : Fin 2) : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℚ :=
  proj 2 a.val ⊗ₖ proj 2 x.val

/-- `plusQ 0 = |+⟩⟨+|` and `plusQ 1 = |-⟩⟨-|`. -/
def plusQ (b : Fin 2) : Matrix (Fin 2) (Fin 2) ℚ :=
  of fun i j => if i = j then 1 / 2 else if b = 0 then 1 / 2 else -1 / 2

/-- Bob's operation for setting `(y, g)` and outcome `b`: for `g = 0`, `|b⟩⟨b| ⊗ |0⟩⟨0|`; for
`g = 1`, `|±⟩⟨±| ⊗ |y ⊕ b⟩⟨y ⊕ b|`. -/
def ocbBobQ (y : Fin 2 × Fin 2) (b : Fin 2) : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℚ :=
  if y.2 = 0 then proj 2 b.val ⊗ₖ proj 2 0 else plusQ b ⊗ₖ proj 2 (y.1 + b).val

/-- Rational partial trace over the output factor. -/
def ptraceOutQ {I O : Type} [Fintype O] (T : Matrix (I × O) (I × O) ℚ) : Matrix I I ℚ :=
  of fun i j => ∑ o, T (i, o) (j, o)

theorem ptraceOut_toC {I O : Type} [Fintype O] (T : Matrix (I × O) (I × O) ℚ) :
    ptraceOut (toC T) = toC (ptraceOutQ T) := by
  ext i j
  simp [ptraceOut, ptraceOutQ, toC_apply, Matrix.of_apply, Rat.cast_sum]

theorem ocbAliceQ_sq :
    ∀ x a : Fin 2, ocbAliceQ x a = (1 : ℚ) • ((ocbAliceQ x a)ᵀ * ocbAliceQ x a) := by
  decide +kernel

theorem ocbBobQ_sq :
    ∀ (y : Fin 2 × Fin 2) (b : Fin 2), ocbBobQ y b = (1 : ℚ) • ((ocbBobQ y b)ᵀ * ocbBobQ y b) := by
  decide +kernel

theorem ocbAliceQ_norm : ∀ x : Fin 2, ptraceOutQ (ocbAliceQ x 0 + ocbAliceQ x 1) = 1 := by
  decide +kernel

theorem ocbBobQ_norm : ∀ y : Fin 2 × Fin 2, ptraceOutQ (ocbBobQ y 0 + ocbBobQ y 1) = 1 := by
  decide +kernel

/-- Alice's instrument of [OCB]. -/
noncomputable def ocbAlice : Instrument (Fin 2) (Fin 2) (Fin 2) (Fin 2) where
  elem x a := toC (ocbAliceQ x a)
  positive x a := transpose_mul_self_sound _ _ 1 (ocbAliceQ_sq x a) (by norm_num)
  normalized x := by
    show ptraceOut (∑ a : Fin 2, toC (ocbAliceQ x a)) = 1
    rw [Fin.sum_univ_two, ← toC_add, ptraceOut_toC, ocbAliceQ_norm x, toC_one]

/-- Bob's instrument of [OCB]. -/
noncomputable def ocbBob : Instrument (Fin 2) (Fin 2) (Fin 2 × Fin 2) (Fin 2) where
  elem y b := toC (ocbBobQ y b)
  positive y b := transpose_mul_self_sound _ _ 1 (ocbBobQ_sq y b) (by norm_num)
  normalized y := by
    show ptraceOut (∑ b : Fin 2, toC (ocbBobQ y b)) = 1
    rw [Fin.sum_univ_two, ← toC_add, ptraceOut_toC, ocbBobQ_norm y, toC_one]

/-! ### The rational parts of `W_OCB` -/

/-- `IIII`. -/
def ocbK0 : Matrix (Lab 2 2 2 2) (Lab 2 2 2 2) ℚ := kron4 1 1 1 1

/-- `IZZI + ZIXZ`, the two terms of `W_OCB` that involve the outputs. -/
def ocbK1 : Matrix (Lab 2 2 2 2) (Lab 2 2 2 2) ℚ :=
  kron4 1 !![1, 0; 0, -1] !![1, 0; 0, -1] 1 + kron4 !![1, 0; 0, -1] 1 !![0, 1; 1, 0] !![1, 0; 0, -1]

theorem WOCB_eq :
    WOCB = ((1 / 4 : ℝ) : ℂ) • toC ocbK0 + ((1 / (4 * Real.sqrt 2) : ℝ) : ℂ) • toC ocbK1 :=
  rfl

theorem ocbK0_eq_one : ocbK0 = 1 := by decide +kernel

theorem ocbK0_eq_Pi : ocbK0 = Pi 2 2 2 2 := by decide +kernel

theorem ocbK1_eq : ocbK1 = GA 2 2 2 2 + GB 2 2 2 2 := by decide +kernel

theorem ocbK1_transpose : ocbK1ᵀ = ocbK1 := by decide +kernel

theorem ocbK1_sq : ocbK1 * ocbK1 = (2 : ℚ) • 1 := by decide +kernel

theorem trace_ocbK0 : trace ocbK0 = 16 := by decide +kernel

theorem trace_ocbK1 : trace ocbK1 = 0 := by decide +kernel

/-! ### Validity of `W_OCB` -/

section GAGB

variable {m d n e : ℕ}

theorem GAGB_LV_a (hn : 2 ≤ n) :
    RBIBOq (GA m d n e + GB m d n e) - RAOq (RBIBOq (GA m d n e + GB m d n e)) = 0 := by
  simp only [GA, GB, RBIBOq_add, RBIBOq_kron4, trace_Z hn, trace_X, zero_mul, zero_div, zero_smul,
    add_zero, RAOq_zero, sub_self]

theorem GAGB_LV_b (hm : 2 ≤ m) (he : 0 < e) :
    RAIAOq (GA m d n e + GB m d n e) - RBOq (RAIAOq (GA m d n e + GB m d n e)) = 0 := by
  simp only [GA, GB, RAIAOq_add, RAIAOq_kron4, trace_Z hm, zero_mul, zero_div, zero_smul,
    add_zero, RBOq_smul, RBOq_kron4, trace_one_div_self he, one_smul, sub_self]

theorem GAGB_LV_c (hd : 0 < d) (he : 0 < e) :
    (GA m d n e + GB m d n e) - RAOq (GA m d n e + GB m d n e) - RBOq (GA m d n e + GB m d n e) +
      RAOq (RBOq (GA m d n e + GB m d n e)) = 0 := by
  simp only [GA, GB, RAOq_add, RBOq_add, RAOq_smul, RBOq_smul, RAOq_kron4, RBOq_kron4,
    trace_one_div_self hd, trace_one_div_self he, one_smul]
  module

end GAGB

/-- `G_A + G_B ∈ L_V`. -/
theorem gagb_inLV (D : Ports) (hD : AllPortsGE2 D) :
    InLV D (toC (GA D.m D.d D.n D.e + GB D.m D.d D.n D.e)) := by
  refine ⟨isHermitian_map_of_transpose _
    (by rw [Matrix.transpose_add, GA_transpose, GB_transpose]), ?_, ?_, ?_⟩
  · rw [← toC_RBIBOq, ← toC_RAOq, ← toC_sub, GAGB_LV_a hD.2.2.1, toC_zero]
  · rw [← toC_RAIAOq, ← toC_RBOq, ← toC_sub, GAGB_LV_b hD.1 D.e_pos, toC_zero]
  · rw [← toC_RBOq, ← toC_RAOq, ← toC_RAOq, ← toC_sub, ← toC_sub, ← toC_add,
      GAGB_LV_c D.d_pos D.e_pos, toC_zero]

theorem wocb_inLV : InLV qubits WOCB := by
  have h0 : InLV qubits (toC ocbK0) := by
    rw [ocbK0_eq_Pi]
    exact pi_inLV qubits
  have h1 : InLV qubits (toC ocbK1) := by
    rw [ocbK1_eq]
    exact gagb_inLV qubits ⟨le_rfl, le_rfl, le_rfl, le_rfl⟩
  rw [WOCB_eq]
  exact genLV_add (genLV_smul (isSelfAdjoint_ofReal _) h0) (genLV_smul (isSelfAdjoint_ofReal _) h1)

/-- `1 + A ≥ 0` for a Hermitian involution `A`: `(1 + A)ᴴ (1 + A) = 2 (1 + A)`. -/
theorem posSemidef_one_add_of_sq {ι : Type} [Fintype ι] [DecidableEq ι] {A : Matrix ι ι ℂ}
    (hAH : Aᴴ = A) (hAA : A * A = 1) : (1 + A).PosSemidef := by
  have hsq : (1 + A)ᴴ * (1 + A) = (2 : ℂ) • (1 + A) := by
    rw [Matrix.conjTranspose_add, Matrix.conjTranspose_one, hAH, Matrix.add_mul, Matrix.one_mul,
      Matrix.mul_add, Matrix.mul_one, hAA, two_smul]
    abel
  have h := posSemidef_complex_smul (Matrix.posSemidef_conjTranspose_mul_self (1 + A))
    (Complex.zero_le_real.mpr (by norm_num : (0 : ℝ) ≤ 1 / 2))
  rw [hsq, smul_smul] at h
  have hc : ((1 / 2 : ℝ) : ℂ) * 2 = 1 := by norm_num
  rwa [hc, one_smul] at h

theorem wocb_psd : WOCB.PosSemidef := by
  have hs : Real.sqrt 2 * Real.sqrt 2 = 2 := Real.mul_self_sqrt (by norm_num)
  have hW : WOCB = ((1 / 4 : ℝ) : ℂ) • (1 + ((1 / Real.sqrt 2 : ℝ) : ℂ) • toC ocbK1) := by
    have hc : (1 / (4 * Real.sqrt 2) : ℝ) = 1 / 4 * (1 / Real.sqrt 2) := by ring
    rw [WOCB_eq, hc, Complex.ofReal_mul, ← smul_smul, ← smul_add, ocbK0_eq_one, toC_one]
  have hKH : (toC ocbK1)ᴴ = toC ocbK1 := isHermitian_map_of_transpose ocbK1 ocbK1_transpose
  have hKK : toC ocbK1 * toC ocbK1 = (2 : ℂ) • 1 := by
    rw [toC_mul_rat, ocbK1_sq, toC_smul, toC_one]
    norm_num
  have hAH : (((1 / Real.sqrt 2 : ℝ) : ℂ) • toC ocbK1)ᴴ = ((1 / Real.sqrt 2 : ℝ) : ℂ) • toC ocbK1 := by
    rw [Matrix.conjTranspose_smul, hKH, (isSelfAdjoint_ofReal _).star_eq]
  have hAA : (((1 / Real.sqrt 2 : ℝ) : ℂ) • toC ocbK1) * (((1 / Real.sqrt 2 : ℝ) : ℂ) • toC ocbK1)
      = 1 := by
    rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul, hKK, smul_smul]
    have hR : 1 / Real.sqrt 2 * (1 / Real.sqrt 2) * 2 = (1 : ℝ) := by
      rw [div_mul_div_comm, one_mul, hs]
      norm_num
    have hr : ((1 / Real.sqrt 2 : ℝ) : ℂ) * ((1 / Real.sqrt 2 : ℝ) : ℂ) * 2 = 1 := by
      first
        | exact_mod_cast hR
        | rw [← Complex.ofReal_mul, ← Complex.ofReal_ofNat 2, ← Complex.ofReal_mul, hR,
            Complex.ofReal_one]
    rw [hr, one_smul]
  rw [hW]
  exact posSemidef_complex_smul (posSemidef_one_add_of_sq hAH hAA)
    (Complex.zero_le_real.mpr (by norm_num))

theorem wocb_trace : Matrix.trace WOCB = ((qubits.d * qubits.e : ℕ) : ℂ) := by
  rw [WOCB_eq, Matrix.trace_add, Matrix.trace_smul, Matrix.trace_smul, trace_toC, trace_toC,
    trace_ocbK0, trace_ocbK1]
  norm_num [qubits_d, qubits_e]

/-- `W_OCB` is a process. -/
theorem wocb_valid : Valid qubits WOCB := ⟨wocb_inLV, wocb_psd, wocb_trace⟩

/-! ### The winning probability `(2 + √2)/4` -/

theorem toC_kronecker {ι κ : Type*} (A : Matrix ι ι ℚ) (B : Matrix κ κ ℚ) :
    toC (A ⊗ₖ B) = toC A ⊗ₖ toC B := by
  ext ⟨i, k⟩ ⟨j, l⟩
  simp [kroneckerMap_apply]

theorem re_trace_WOCB_mul (Q : Matrix (Lab 2 2 2 2) (Lab 2 2 2 2) ℚ) :
    ((WOCB * toC Q).trace).re =
      1 / 4 * ((trace (ocbK0 * Q) : ℚ) : ℝ) +
        1 / (4 * Real.sqrt 2) * ((trace (ocbK1 * Q) : ℚ) : ℝ) := by
  rw [WOCB_eq, Matrix.add_mul, Matrix.smul_mul, Matrix.smul_mul, ← Matrix.map_mul,
    ← Matrix.map_mul, Matrix.trace_add, Matrix.trace_smul, Matrix.trace_smul, trace_toC,
    trace_toC]
  simp only [smul_eq_mul, Complex.add_re, Complex.re_ofReal_mul, Complex.ratCast_re]

theorem born_ocb (x : Fin 2) (y : Fin 2 × Fin 2) (a b : Fin 2) :
    born qubits WOCB ocbAlice ocbBob x y a b =
      1 / 4 * ((trace (ocbK0 * (ocbAliceQ x a ⊗ₖ ocbBobQ y b)) : ℚ) : ℝ) +
        1 / (4 * Real.sqrt 2) * ((trace (ocbK1 * (ocbAliceQ x a ⊗ₖ ocbBobQ y b)) : ℚ) : ℝ) := by
  show ((WOCB * (toC (ocbAliceQ x a) ⊗ₖ toC (ocbBobQ y b))).trace).re = _
  rw [← toC_kronecker, re_trace_WOCB_mul]

/-- The winning sum of `ocbWin` for the Born probabilities of a rational operator `K`. -/
def ocbGameQ (K : Matrix (Lab 2 2 2 2) (Lab 2 2 2 2) ℚ) : ℚ :=
  (1 / 8) * ∑ x : Fin 2, ∑ y : Fin 2,
    ((∑ a : Fin 2, trace (K * (ocbAliceQ x a ⊗ₖ ocbBobQ (y, 0) x))) +
      ∑ b : Fin 2, trace (K * (ocbAliceQ x y ⊗ₖ ocbBobQ (y, 1) b)))

theorem ocbGameQ_K0 : ocbGameQ ocbK0 = 2 := by decide +kernel

theorem ocbGameQ_K1 : ocbGameQ ocbK1 = 2 := by decide +kernel

/-- `W_OCB` wins the game of [OCB] with probability `(2 + √2)/4`. -/
theorem ocbWin_born : ocbWin (born qubits WOCB ocbAlice ocbBob) = (2 + Real.sqrt 2) / 4 := by
  have h : ocbWin (born qubits WOCB ocbAlice ocbBob) =
      1 / 4 * ((ocbGameQ ocbK0 : ℚ) : ℝ) + 1 / (4 * Real.sqrt 2) * ((ocbGameQ ocbK1 : ℚ) : ℝ) := by
    simp only [ocbWin, born_ocb, ocbGameQ, Fin.sum_univ_two]
    push_cast
    ring
  have hs : Real.sqrt 2 * Real.sqrt 2 = 2 := Real.mul_self_sqrt (by norm_num)
  have k : 1 / (4 * Real.sqrt 2) * 2 = Real.sqrt 2 / 4 := by
    rw [div_mul_eq_mul_div, one_mul, div_eq_iff (by positivity)]
    linear_combination (-1 : ℝ) * hs
  have h2 : ((2 : ℚ) : ℝ) = 2 := by norm_num
  rw [h, ocbGameQ_K0, ocbGameQ_K1, h2, k]
  ring

/-- `W_OCB` is not a causal process. -/
theorem wocb_not_causalProcess : ¬ CausalProcess qubits WOCB := by
  intro h
  have hc : Causal (born qubits WOCB ocbAlice ocbBob) :=
    causal_born_comap qubits WOCB ocbAlice ocbBob ocbDec ocbEnc ocbDec_enc
      (h.2 1 3 1 1 ocbAlice (ocbBob.comap ocbDec))
  have hle := ocbWin_le_of_causal hc
  rw [ocbWin_born] at hle
  have hs : Real.sqrt 2 * Real.sqrt 2 = 2 := Real.mul_self_sqrt (by norm_num)
  have hpos : 0 < Real.sqrt 2 := by positivity
  nlinarith [hs, hpos]

/-- **`intro:WOCB` and Appendix C**: `W_OCB` is a process; every causal
distribution wins the game of [OCB] with probability at most `3/4`; for some instruments (those
of [OCB], `ocbAlice` and `ocbBob`), `W_OCB` wins with probability `(2 + √2)/4 > 3/4`; hence `W_OCB`
violates a causal inequality and is neither causal, nor extensibly causal, nor causally
separable. -/
theorem appC_OCB_game :
    Valid qubits WOCB ∧
    (∀ p : Prob (Fin 2) (Fin 2 × Fin 2) (Fin 2) (Fin 2), Causal p → ocbWin p ≤ 3 / 4) ∧
    (∃ (M : Instrument (Fin 2) (Fin 2) (Fin 2) (Fin 2))
      (N : Instrument (Fin 2) (Fin 2) (Fin 2 × Fin 2) (Fin 2)),
      ocbWin (born qubits WOCB M N) = (2 + Real.sqrt 2) / 4) ∧
    3 / 4 < (2 + Real.sqrt 2) / 4 ∧
    ¬ CausalProcess qubits WOCB ∧ ¬ ExtensiblyCausal qubits WOCB ∧
    ¬ CausallySeparable qubits WOCB := by
  have hs : Real.sqrt 2 * Real.sqrt 2 = 2 := Real.mul_self_sqrt (by norm_num)
  have hpos : 0 < Real.sqrt 2 := by positivity
  have hnec : ¬ ExtensiblyCausal qubits WOCB := fun h =>
    wocb_not_causalProcess (causalProcess_of_extensiblyCausal h)
  exact ⟨wocb_valid, fun p hp => ocbWin_le_of_causal hp, ⟨ocbAlice, ocbBob, ocbWin_born⟩,
    by nlinarith [hs, hpos], wocb_not_causalProcess, hnec,
    fun h => hnec (extensiblyCausal_of_causallySeparable h)⟩

end CausalNonpurifiability
