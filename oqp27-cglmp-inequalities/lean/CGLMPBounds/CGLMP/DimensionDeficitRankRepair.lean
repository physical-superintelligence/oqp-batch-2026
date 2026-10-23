module

public import CGLMPBounds.CGLMP.DimensionDeficitRounding

@[expose] public section


/-!
# The factor-two block rank repair estimate

Appendix E: for the block projection `Λ = diag(Λ₀,…,Λ_{d-1})`, let `M = d⁻¹∑ Λₐ`
have integer trace `k`. Rounding `M` to its top-k spectral projection `P` gives
`∑ ‖Λₐ-P‖²_F ≤ 2d Tr(M-M²)`. With `N = 4dn` and
`ε_red = Tr(M-M²)/(4n)`, this is `‖Λ-I_d⊗P‖²₂,N ≤ 2 ε_red`.
The normalized result is stated as a sum of squared block Frobenius norms.
-/

open Matrix
open scoped ComplexOrder

namespace CGLMPBounds

noncomputable section

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem posSemidef_of_hermitian_idempotent {P : Matrix ι ι ℂ}
    (hP : P.IsHermitian) (hP2 : P * P = P) : P.PosSemidef := by
  have h := Matrix.posSemidef_conjTranspose_mul_self P
  rwa [hP.eq, hP2] at h

theorem average_projection_posSemidef {d : ℕ} (hd : 0 < d) {M : Matrix ι ι ℂ}
    (L : Fin d → Matrix ι ι ℂ) (hL : ∀ a, (L a).IsHermitian)
    (hL2 : ∀ a, L a * L a = L a) (hsum : ∑ a, L a = (d : ℝ) • M) : M.PosSemidef := by
  have hd' : (d : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have havg : M = (d : ℝ)⁻¹ • ∑ a, L a := by
    rw [hsum, smul_smul, inv_mul_cancel₀ hd', one_smul]
  have hpos : (∑ a, L a).PosSemidef :=
    Matrix.posSemidef_sum Finset.univ (fun a _ => posSemidef_of_hermitian_idempotent (hL a) (hL2 a))
  rw [havg]
  exact hpos.smul (inv_nonneg.mpr (Nat.cast_nonneg d))

/-- An average of orthogonal projections is a positive contraction. -/
theorem average_projections_positive_contraction {d : ℕ} (hd : 0 < d) {M : Matrix ι ι ℂ}
    (L : Fin d → Matrix ι ι ℂ) (hL : ∀ a, (L a).IsHermitian)
    (hL2 : ∀ a, L a * L a = L a) (hsum : ∑ a, L a = (d : ℝ) • M) :
    M.PosSemidef ∧ (1 - M).PosSemidef := by
  refine ⟨average_projection_posSemidef hd L hL hL2 hsum, ?_⟩
  have hcomp : ∀ a, (1 - L a) * (1 - L a) = 1 - L a := by
    intro a
    simp only [Matrix.sub_mul, Matrix.mul_sub, Matrix.one_mul, Matrix.mul_one, hL2]
    abel
  have hsumcomp : ∑ a, (1 - L a) = (d : ℝ) • (1 - M) := by
    rw [Finset.sum_sub_distrib, hsum, smul_sub]
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, Nat.cast_smul_eq_nsmul]
  exact average_projection_posSemidef hd (fun a => 1 - L a)
    (fun a => Matrix.isHermitian_one.sub (hL a)) hcomp hsumcomp

theorem re_trace_sq_distance_projection {M P : Matrix ι ι ℂ}
    (hM : M.IsHermitian) (hP : P.IsHermitian) (hP2 : P * P = P) :
    (Matrix.trace ((M - P)ᴴ * (M - P))).re
      = (Matrix.trace (M * M)).re + (Matrix.trace P).re - 2 * (Matrix.trace (M * P)).re := by
  rw [(hM.sub hP).eq, Matrix.sub_mul, Matrix.mul_sub, Matrix.mul_sub,
    hP2, Matrix.trace_sub, Matrix.trace_sub, Matrix.trace_sub, Matrix.trace_mul_comm P M]
  simp only [Complex.sub_re]
  ring

/-- The block-projection rank-repair estimate before normalization. The explicit average
identity `∑ Λ_a = d M` is the source's definition of `Λ̄`. -/
theorem exists_block_projection_rounding {d k : ℕ} {M : Matrix ι ι ℂ}
    (L : Fin d → Matrix ι ι ℂ) (hL : ∀ a, (L a).IsHermitian)
    (hL2 : ∀ a, L a * L a = L a) (hsum : ∑ a, L a = (d : ℝ) • M)
    (hM : M.PosSemidef) (hC : (1 - M).PosSemidef)
    (htrace : (Matrix.trace M).re = (k : ℝ)) :
    ∃ P : Matrix ι ι ℂ, P.IsHermitian ∧ P * P = P ∧ P.rank = k ∧
      (∑ a, (Matrix.trace ((L a - P)ᴴ * (L a - P))).re)
        ≤ 2 * d * (Matrix.trace (M - M * M)).re := by
  obtain ⟨P, hP, hP2, hRank, hTrP, herror⟩ :=
    exists_integer_trace_rounding_with_trace hM hC k htrace
  have hTrP' : (Matrix.trace P).re = (k : ℝ) := by rw [hTrP, Complex.natCast_re]
  have hdef : (Matrix.trace (M - M * M)).re = (k : ℝ) - (Matrix.trace (M * M)).re := by
    rw [Matrix.trace_sub, Complex.sub_re, htrace]
  have hcross : (Matrix.trace (M * M)).re ≤ (Matrix.trace (M * P)).re := by
    rw [re_trace_sq_distance_projection hM.1 hP hP2, hTrP', hdef] at herror
    linarith
  have htrace_sum : ∑ a, (Matrix.trace (L a)).re = (d : ℝ) * k := by
    rw [← Complex.re_sum, ← Matrix.trace_sum, hsum, Matrix.trace_smul,
      Complex.real_smul, Complex.re_ofReal_mul, htrace]
  have hcross_sum : ∑ a, (Matrix.trace (L a * P)).re
      = (d : ℝ) * (Matrix.trace (M * P)).re := by
    rw [← Complex.re_sum, ← Matrix.trace_sum, ← Finset.sum_mul, hsum,
      Matrix.smul_mul, Matrix.trace_smul, Complex.real_smul, Complex.re_ofReal_mul]
  have htotal : (∑ a, (Matrix.trace ((L a - P)ᴴ * (L a - P))).re)
      = 2 * d * ((k : ℝ) - (Matrix.trace (M * P)).re) := by
    simp_rw [re_trace_sq_distance_projection (hL _) hP hP2, hL2, hTrP']
    rw [Finset.sum_sub_distrib, Finset.sum_add_distrib, htrace_sum,
      ← Finset.mul_sum, hcross_sum]
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    ring
  refine ⟨P, hP, hP2, hRank, ?_⟩
  rw [htotal, hdef]
  exact mul_le_mul_of_nonneg_left (sub_le_sub_left hcross _) (by positivity)

/-- The factor `2` of Appendix E after normalizing by `N = 4dn` and using
`ε_red = Tr(M-M²)/(4n)`. -/
theorem exists_normalized_block_projection_rounding {d k n : ℕ}
    (hd : 0 < d) (hn : 0 < n) {M : Matrix ι ι ℂ}
    (L : Fin d → Matrix ι ι ℂ) (hL : ∀ a, (L a).IsHermitian)
    (hL2 : ∀ a, L a * L a = L a) (hsum : ∑ a, L a = (d : ℝ) • M)
    (hM : M.PosSemidef) (hC : (1 - M).PosSemidef)
    (htrace : (Matrix.trace M).re = (k : ℝ)) :
    ∃ P : Matrix ι ι ℂ, P.IsHermitian ∧ P * P = P ∧ P.rank = k ∧
      (∑ a, (Matrix.trace ((L a - P)ᴴ * (L a - P))).re) / (4 * d * n)
        ≤ 2 * ((Matrix.trace (M - M * M)).re / (4 * n)) := by
  obtain ⟨P, hP, hP2, hRank, herror⟩ := exists_block_projection_rounding L hL hL2 hsum hM hC htrace
  refine ⟨P, hP, hP2, hRank, ?_⟩
  have hd' : (0 : ℝ) < d := Nat.cast_pos.mpr hd
  have hn' : (0 : ℝ) < n := Nat.cast_pos.mpr hn
  have heq : 2 * ((Matrix.trace (M - M * M)).re / (4 * n))
      = (2 * d * (Matrix.trace (M - M * M)).re) / (4 * d * n) := by
    field_simp <;> ring
  rw [heq]
  exact div_le_div_of_nonneg_right herror (by positivity)

/-- Rank repair for a block projection, deriving positivity of its average rather than
assuming it. The conclusion is the source's factor-two estimate in block coordinates. -/
theorem block_rank_repair {d k n : ℕ} (hd : 0 < d) (hn : 0 < n) {M : Matrix ι ι ℂ}
    (L : Fin d → Matrix ι ι ℂ) (hL : ∀ a, (L a).IsHermitian)
    (hL2 : ∀ a, L a * L a = L a) (hsum : ∑ a, L a = (d : ℝ) • M)
    (htrace : (Matrix.trace M).re = (k : ℝ)) :
    ∃ P : Matrix ι ι ℂ, P.IsHermitian ∧ P * P = P ∧ P.rank = k ∧
      (∑ a, (Matrix.trace ((L a - P)ᴴ * (L a - P))).re) / (4 * d * n)
        ≤ 2 * ((Matrix.trace (M - M * M)).re / (4 * n)) := by
  obtain ⟨hM, hC⟩ := average_projections_positive_contraction hd L hL hL2 hsum
  exact exists_normalized_block_projection_rounding hd hn L hL hL2 hsum hM hC htrace


end

end CGLMPBounds
