module

public import CGLMPBounds.Fourier.LemmaF1
public import CGLMPBounds.TensorCHSH.Measurement
public import CGLMPBounds.Certificates.TableF1

@[expose] public section


/-!
# The global noise separation (A.6)

Supplement, Theorem A.3, equation (A.6): "For every integer `m ≥ 955`, the two rank-one
measurements per party defining `T_m` on `Φ_{2^m}` satisfy `v_crit(T_m) < 3049/5000 < v_crit(Q_{2^m})`.
For `m ≥ 1182`, the stronger bound `v_crit(T_m) < 17/29 < 3/5 < v_crit(Q_{2^m})` holds."

`T_m` is the behaviour of the common-input tensor CHSH measurements (`tensorCHSHTable`), `Q_{2^m}` the
Fourier-phase behaviour (`fourierTable (2^m)`); `v_crit` is the global critical visibility under
uniform noise.

Proof: (F.5) identifies `T_m` with the closed formula; discarding output bits (F.7) reduces `m` to
`955` (resp. `1182`), where the exact certificates of Table F.1 apply; Lemma F.1 at `d = 2^m` gives
the lower bound for `Q_{2^m}`.
-/

namespace CGLMPBounds

theorem two_le_two_pow {m : ℕ} (hm : 1 ≤ m) : 2 ≤ 2 ^ m :=
  calc 2 = 2 ^ 1 := by norm_num
    _ ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) hm

/-- **Equation (A.6)**: for every `m ≥ 955`, `v_crit(T_m) < 3049/5000 < v_crit(Q_{2^m})`. -/
theorem noise_separation_955 (m : ℕ) (hm : 955 ≤ m) :
    critVisibility (TensorCHSH.tensorCHSHTable m) < 3049 / 5000 ∧
      (3049 : ℝ) / 5000 < critVisibility (fourierTable (2 ^ m)) := by
  refine ⟨?_, ?_⟩
  · rw [TensorCHSH.tensorCHSHTable_eq]
    exact lt_of_le_of_lt (TensorCHSH.critVisibility_tensorTable_le hm _)
      Certificates.critVisibility_tensorTable_955_lt
  · exact lt_critVisibility_fourierTable (2 ^ m) (two_le_two_pow (by omega))

/-- **Equation (A.6), stronger bound**: for every `m ≥ 1182`,
`v_crit(T_m) < 17/29 < 3/5 < v_crit(Q_{2^m})`. -/
theorem noise_separation_1182 (m : ℕ) (hm : 1182 ≤ m) :
    critVisibility (TensorCHSH.tensorCHSHTable m) < 17 / 29 ∧ (17 : ℝ) / 29 < 3 / 5 ∧
      (3 : ℝ) / 5 < critVisibility (fourierTable (2 ^ m)) := by
  refine ⟨?_, by norm_num, ?_⟩
  · rw [TensorCHSH.tensorCHSHTable_eq]
    exact lt_of_le_of_lt (TensorCHSH.critVisibility_tensorTable_le hm _)
      Certificates.critVisibility_tensorTable_1182_lt
  · exact lt_trans (by norm_num : (3 : ℝ) / 5 < 3049 / 5000)
      (lt_critVisibility_fourierTable (2 ^ m) (two_le_two_pow (by omega)))

end CGLMPBounds
