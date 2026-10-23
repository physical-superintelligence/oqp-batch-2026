module

public import CausalNonpurifiability.Unconditional
public import CausalNonpurifiability.Boundary.Dilation
public import CausalNonpurifiability.Uniform

@[expose] public section


/-!
# `CausalNonpurifiability.MainTheorem`

The statements of Theorem 1.1 (`thm:intro`) and of Theorem 3.1 (`thm:main`), parts (i), (ii),
(iii), assembled from the library, with every clause of the manuscript and no hypothesis beyond
those of the manuscript. The dichotomy `eq:dichotomy` is `dimension_dichotomy`
(`CausalNonpurifiability/Unconditional.lean`).

Conventions of the statements:

* "process" is `Valid D W`; "causally nonseparable" is `¬ CausallySeparable D W`, where
  `CausallySeparable` contains `Valid`, so that for a process the negation is the manuscript's
  notion;
* "of rank `4de`" and "its rank is full" for `W_0` are equalities for `Matrix.rank`; the space
  `A_I A_O B_I B_O` has dimension `m d n e`;
* "of full rank" for `W_q` and on the ball `eq:ball` is positive definiteness (`Matrix.PosDef`),
  which for a positive operator is the same as full rank;
* the ball is `{W_c + Δ : Δ ∈ L_V, Tr Δ = 0, ‖Δ‖_∞ ≤ 1/(300 m n)}` with the operator norm
  `opNorm`.
-/

set_option autoImplicit false

namespace CausalNonpurifiability

open Matrix
open scoped ComplexOrder

/-- The rank `4de` of `W_0` is the dimension `m d n e` of the space if and only if `m = n = 2`
(last sentence of Theorem 3.1(i)). -/
theorem uniform_rank_full_iff {m d n e : ℕ} (hm : 2 ≤ m) (hd : 2 ≤ d) (hn : 2 ≤ n)
    (he : 2 ≤ e) : (toC (W0 m d n e)).rank = m * d * n * e ↔ m = 2 ∧ n = 2 := by
  rw [uniform_rank hm hd hn he]
  constructor
  · intro h
    have hde : 0 < d * e := Nat.mul_pos (by omega) (by omega)
    have h4 : m * n = 4 := by
      have h' : (m * n) * (d * e) = 4 * (d * e) := by
        calc (m * n) * (d * e) = m * d * n * e := by ring
          _ = 4 * d * e := h.symm
          _ = 4 * (d * e) := by ring
      exact Nat.eq_of_mul_eq_mul_right hde h'
    have hm2 : m ≤ 2 := by
      by_contra hc
      have h6 : 3 * 2 ≤ m * n := Nat.mul_le_mul (by omega) hn
      rw [h4] at h6
      omega
    have hn2 : n ≤ 2 := by
      by_contra hc
      have h6 : 2 * 3 ≤ m * n := Nat.mul_le_mul hm (by omega)
      rw [h4] at h6
      omega
    exact ⟨by omega, by omega⟩
  · rintro ⟨rfl, rfl⟩
    ring

/-- **Theorem 1.1** (`thm:intro`): `W_q` is a process matrix of full rank; it is extensibly
causal and causally nonseparable, and it is not purifiable. -/
theorem theorem_intro :
    Valid qubits Wq ∧ Wq.PosDef ∧ ExtensiblyCausal qubits Wq ∧ ¬ CausallySeparable qubits Wq ∧
      ¬ Purifiable qubits Wq :=
  ⟨qubit_kernel.1, qubit_kernel.2.1, qubit_kernel.2.2.1, qubit_kernel.2.2.2,
    qubit_not_purifiable⟩

/-- **Theorem 3.1(i)** (`thm:main`): for `m, d, n, e ≥ 2` the operator `W_0` is a process of rank
`4de`; it is extensibly causal and causally nonseparable, and it is not purifiable; its rank is
full if and only if `m = n = 2`. -/
theorem main_theorem_i (D : Ports) (hD : AllPortsGE2 D) :
    Valid D (toC (W0 D.m D.d D.n D.e)) ∧
      Matrix.rank (toC (W0 D.m D.d D.n D.e)) = 4 * D.d * D.e ∧
      ExtensiblyCausal D (toC (W0 D.m D.d D.n D.e)) ∧
      ¬ CausallySeparable D (toC (W0 D.m D.d D.n D.e)) ∧
      ¬ Purifiable D (toC (W0 D.m D.d D.n D.e)) ∧
      (Matrix.rank (toC (W0 D.m D.d D.n D.e)) = D.m * D.d * D.n * D.e ↔ D.m = 2 ∧ D.n = 2) :=
  ⟨(uniform_kernel D hD).1, (uniform_kernel D hD).2.1, (uniform_kernel D hD).2.2.1,
    (uniform_kernel D hD).2.2.2, uniform_not_purifiable D hD,
    uniform_rank_full_iff hD.1 hD.2.1 hD.2.2.1 hD.2.2.2⟩

/-- **Theorem 3.1(ii)** (`thm:main`, `eq:ball`): for `m, d, n, e ≥ 2`, every operator `W_c + Δ`
with `Δ ∈ L_V`, `Tr Δ = 0` and `‖Δ‖_∞ ≤ 1/(300 m n)` is a process of full rank that is extensibly
causal and causally nonseparable, and that is not purifiable. -/
theorem main_theorem_ii (D : Ports) (hD : AllPortsGE2 D) {H : PMat D} (hLV : InLV D H)
    (htr : H.trace = 0) (hnorm : opNorm H ≤ 1 / (300 * D.m * D.n)) :
    Valid D (WcC D + H) ∧ (WcC D + H).PosDef ∧ ExtensiblyCausal D (WcC D + H) ∧
      ¬ CausallySeparable D (WcC D + H) ∧ ¬ Purifiable D (WcC D + H) :=
  ⟨(relative_ball_kernel_norm D hD hLV htr hnorm).1,
    (relative_ball_kernel_norm D hD hLV htr hnorm).2.1,
    (relative_ball_kernel_norm D hD hLV htr hnorm).2.2.1,
    (relative_ball_kernel_norm D hD hLV htr hnorm).2.2.2,
    ball_not_purifiable_norm D hD hLV htr hnorm⟩

/-- **Theorem 3.1(iii)** (`thm:main`): if at least one of `m, d, n, e` is `1`, every process on
`A_I A_O B_I B_O` belongs to `O_A` or to `O_B`, and it is purifiable. -/
theorem main_theorem_iii (D : Ports) (h1 : D.m = 1 ∨ D.d = 1 ∨ D.n = 1 ∨ D.e = 1) {W : PMat D}
    (hW : Valid D W) : (OrderedAB D W ∨ OrderedBA D W) ∧ Purifiable D W :=
  ⟨one_dimensional_ordered h1 hW, one_dimensional_purifiable h1 hW⟩

/-- **Causal separability dichotomy** (`subsec:classes`): for two parties
without global past and future, every extensibly causal process is causally separable if and only
if one of the four dimensions is one. -/
theorem cs_dichotomy (D : Ports) :
    (∀ W : PMat D, ExtensiblyCausal D W → CausallySeparable D W) ↔
      min D.m (min D.d (min D.n D.e)) = 1 := by
  constructor
  · intro hall
    by_contra hne
    have hD : AllPortsGE2 D := (allPortsGE2_iff D).mpr hne
    obtain ⟨-, -, hEC, hnCS, -⟩ := main_theorem_i D hD
    exact hnCS (hall _ hEC)
  · intro h1 W hEC
    exact one_dimensional_causallySeparable ((min_eq_one_iff D).mp h1) hEC.1

/-- **`W_q` is an interior process**: `W_q` is positive definite, and every
Hermitian `T` with the linear conditions of `L_V`, the trace of `W_q` and `‖T - W_q‖_∞` small
enough is a process (radius `λ_min(W_q) = (10 - √97)/80`, `eq:qubit-minimum`). -/
theorem wq_interior :
    Wq.PosDef ∧ ∃ r : ℝ, 0 < r ∧ ∀ T : PMat qubits, InLV qubits T → T.trace = Wq.trace →
      opNorm (T - Wq) ≤ r → Valid qubits T := by
  have hV : Valid qubits Wq := theorem_intro.1
  refine ⟨theorem_intro.2.1, lamMin, wq_lamMin_pos, fun T hT htr hn => ?_⟩
  have hH : InLV qubits (T - Wq) := genLV_sub hT hV.1
  obtain ⟨h1, -⟩ := psd_bounds_of_opNorm_le hH.1 wq_lamMin_pos.le hn
  have h2 : (Wq - (lamMin : ℂ) • (1 : PMat qubits)).PosSemidef := w0_qubit_sub_lamMin_psd
  have e : T = (Wq - (lamMin : ℂ) • (1 : PMat qubits)) + ((lamMin : ℂ) • 1 + (T - Wq)) := by
    abel
  refine ⟨hT, ?_, htr.trans hV.2.2⟩
  rw [e]
  exact h2.add h1

/-- **Non-empty interior**: for `m, d, n, e ≥ 2` the processes that are
extensibly causal, causally nonseparable and not purifiable contain every process within
operator-norm distance `1/(300mn) > 0` of the process `W_c` (Theorem 3.1(ii)). -/
theorem interior_nonempty (D : Ports) (hD : AllPortsGE2 D) :
    ∃ r : ℝ, 0 < r ∧ Valid D (WcC D) ∧ ∀ T : PMat D, Valid D T → opNorm (T - WcC D) ≤ r →
      ExtensiblyCausal D T ∧ ¬ CausallySeparable D T ∧ ¬ Purifiable D T := by
  have hc := wc_valid D hD
  refine ⟨1 / (300 * D.m * D.n), div_pos one_pos (mul_pos (mul_pos (by norm_num)
    (Nat.cast_pos.mpr D.m_pos)) (Nat.cast_pos.mpr D.n_pos)), hc, fun T hT hn => ?_⟩
  have hLV : InLV D (T - WcC D) := genLV_sub hT.1 hc.1
  have htr : (T - WcC D).trace = 0 := by rw [Matrix.trace_sub, hT.2.2, hc.2.2, sub_self]
  obtain ⟨-, -, hEC, hCS, hP⟩ := main_theorem_ii D hD hLV htr hn
  have e : WcC D + (T - WcC D) = T := by abel
  rw [e] at hEC hCS hP
  exact ⟨hEC, hCS, hP⟩

/-- **`eq:qubit`**: at four qubits `W_q = W₀`, and `W₀` is the Pauli sum
`(20 IIII + 10 ZIII + 10 IIZI + 5 ZIZI + 4 IZZI + 4 ZIXZ)/80` with `Z = diag(1, -1)` and
`X = [[0, 1], [1, 0]]`, words in the order `A_I A_O B_I B_O` (`kron4`); checked entrywise by
kernel evaluation over `ℚ`, as `wq_entries_eq_pauli`. -/
theorem eq_qubit_pauli :
    Wq = toC (W0 2 2 2 2) ∧
      W0 2 2 2 2 = (1 / 80 : ℚ) • ((20 : ℚ) • kron4 1 1 1 1 +
        (10 : ℚ) • kron4 !![1, 0; 0, -1] 1 1 1 + (10 : ℚ) • kron4 1 1 !![1, 0; 0, -1] 1 +
        (5 : ℚ) • kron4 !![1, 0; 0, -1] 1 !![1, 0; 0, -1] 1 +
        (4 : ℚ) • kron4 1 !![1, 0; 0, -1] !![1, 0; 0, -1] 1 +
        (4 : ℚ) • kron4 !![1, 0; 0, -1] 1 !![0, 1; 1, 0] !![1, 0; 0, -1]) :=
  ⟨rfl, by decide +kernel⟩

end CausalNonpurifiability
