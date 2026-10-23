module

public import CGLMPBounds.Hardy.CircleMatrixL2

@[expose] public section


/-! Parseval and the signed Hilbert pairing for actual finite matrix
functions in L². The negative-frequency energy is the literal natural-number
series; integer zero/positive/negative splitting is explicit. -/

namespace CGLMPBounds.Hardy
open MeasureTheory Matrix
open scoped ComplexConjugate Matrix.Norms.Elementwise
noncomputable section
local instance : Fact (0 < (1 : ℝ)) := ⟨zero_lt_one⟩
local instance {r : ℕ} : ENormedAddMonoid (Circulation.Mat r) :=
  inferInstanceAs (ENormedAddMonoid (Fin r → Fin r → ℂ))

 theorem scalar_circle_hasSum_integral_sq (f : UnitCircle → ℂ)
    (hf : MemLp f 2 circleMeasure) :
    HasSum (fun k : ℤ => ‖fourierCoeff f k‖^2) (∫ t, ‖f t‖^2 ∂circleMeasure) := by
  have h := hasSum_sq_fourierCoeff (hf.toLp f)
  simp only [fourierCoeff_congr_ae hf.coeFn_toLp] at h
  convert h using 1
  apply integral_congr_ae
  filter_upwards [hf.coeFn_toLp] with t ht
  rw [ht]

theorem matrixCircleEnergy_hasSum {r : ℕ} (F : UnitCircle → Circulation.Mat r)
    (hF : MemLp F 2 circleMeasure) :
    HasSum (fun k : ℤ => Circulation.hsSq (matrixCircleFourierCoefficient F k))
      (matrixCircleEnergy F) := by
  have hi := hF.integrable (by norm_num)
  have hsq (i j : Fin r) : Integrable (fun t => ‖F t i j‖^2) circleMeasure :=
    (memLp_two_iff_integrable_sq_norm ((hF.eval i).eval j).aestronglyMeasurable).mp
      ((hF.eval i).eval j)
  have hs := (hasSum_sum (fun i (_ : i ∈ (Finset.univ : Finset (Fin r))) =>
    hasSum_sum (fun j (_ : j ∈ (Finset.univ : Finset (Fin r))) =>
      scalar_circle_hasSum_integral_sq (fun t => F t i j) ((hF.eval i).eval j)))).div_const (r : ℝ)
  convert hs using 1
  · funext k
    simp only [matrix_hsSq_eq_entry_norm_sq, matrixCircleFourierCoefficient_apply _ hi]
  · unfold matrixCircleEnergy
    simp only [matrix_hsSq_eq_entry_norm_sq]
    rw [integral_div]
    rw [integral_finsetSum Finset.univ (fun i _ => integrable_finsetSum _ (fun j _ => hsq i j))]
    congr 1
    apply Finset.sum_congr rfl
    intro i _
    rw [integral_finsetSum Finset.univ (fun j _ => hsq i j)]

theorem scalar_circle_inner_integrable (f g : UnitCircle → ℂ)
    (hf : MemLp f 2 circleMeasure) (hg : MemLp g 2 circleMeasure) :
    Integrable (fun t => conj (f t)*g t) circleMeasure := by
  have h : MemLp (star f * g) 1 circleMeasure := hf.star.mul hg
  have he : star f * g = (fun t => conj (f t)*g t) := rfl
  simpa only [he, memLp_one_iff_integrable] using h

theorem matrix_tr_inner_eq_entries {r : ℕ} (X Y : Circulation.Mat r) :
    Circulation.tr (Xᴴ*Y) = (∑ i, ∑ j, conj (X i j)*Y i j)/(r : ℂ) := by
  unfold Circulation.tr
  congr 1
  simp only [Matrix.trace, Matrix.diag_apply, Matrix.mul_apply, Matrix.conjTranspose_apply,
    Complex.star_def]
  exact Finset.sum_comm

theorem matrix_circle_inner_integrable {r : ℕ} (F G : UnitCircle → Circulation.Mat r)
    (hF : MemLp F 2 circleMeasure) (hG : MemLp G 2 circleMeasure) :
    Integrable (fun t => Circulation.tr ((F t)ᴴ*G t)) circleMeasure := by
  simp only [matrix_tr_inner_eq_entries]
  apply Integrable.div_const
  apply integrable_finsetSum
  intro i _
  apply integrable_finsetSum
  intro j _
  exact scalar_circle_inner_integrable _ _ ((hF.eval i).eval j) ((hG.eval i).eval j)

theorem matrix_hilbert_pairing_hasSum {r : ℕ} (F : UnitCircle → Circulation.Mat r)
    (hF : MemLp F 2 circleMeasure) :
    HasSum (fun k : ℤ => hilbertMultiplier k *
      (Circulation.hsSq (matrixCircleFourierCoefficient F k) : ℂ))
      (∫ t, Circulation.tr ((F t)ᴴ * matrixHilbert F t) ∂circleMeasure) := by
  have hi := hF.integrable (by norm_num)
  have hentry (i j : Fin r) := scalar_circle_parseval_pairing
    (fun t => F t i j) (scalarHilbert (fun t => F t i j))
      ((hF.eval i).eval j) (scalarHilbert_memLp _)
  have hs := (hasSum_sum (fun i (_ : i ∈ (Finset.univ : Finset (Fin r))) =>
    hasSum_sum (fun j (_ : j ∈ (Finset.univ : Finset (Fin r))) => hentry i j))).div_const (r : ℂ)
  have hfinite (a : Fin r → Fin r → ℂ) (m : ℂ) :
      m * ((∑ i, ∑ j, (‖a i j‖ : ℂ)^2) / (r : ℂ)) =
        (∑ i, ∑ j, conj (a i j) * (m * a i j)) / (r : ℂ) := by
    rw [← mul_div_assoc]
    congr 1
    simp only [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    calc
      _ = m * (a i j * conj (a i j)) := by
        rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, Complex.ofReal_pow]
      _ = _ := by ring
  convert hs using 1
  · funext k
    simp only [matrix_hsSq_eq_entry_norm_sq, matrixCircleFourierCoefficient_apply _ hi,
      scalarHilbert_fourierCoeff _ ((hF.eval _).eval _)]
    push_cast
    exact hfinite (fun i j => fourierCoeff (fun t => F t i j) k) (hilbertMultiplier k)
  · simp only [matrix_tr_inner_eq_entries, matrixHilbert]
    rw [integral_div]
    rw [integral_finsetSum Finset.univ (fun i _ => integrable_finsetSum _ (fun j _ =>
      scalar_circle_inner_integrable _ _ ((hF.eval i).eval j) (scalarHilbert_memLp _)))]
    congr 1
    apply Finset.sum_congr rfl
    intro i _
    rw [integral_finsetSum Finset.univ (fun j _ => scalar_circle_inner_integrable _ _
      ((hF.eval i).eval j) (scalarHilbert_memLp _))]

set_option maxHeartbeats 1000000 in
theorem matrix_hilbert_signed_energy {r : ℕ} (F : UnitCircle → Circulation.Mat r)
    (hF : MemLp F 2 circleMeasure) :
    -(∫ t, Circulation.tr ((F t)ᴴ*matrixHilbert F t) ∂circleMeasure).im =
      matrixCircleEnergy F - Circulation.hsSq (matrixCircleFourierCoefficient F 0) -
        2*matrixCircleNegativeEnergy F := by
  let e : ℤ → ℝ := fun k => Circulation.hsSq (matrixCircleFourierCoefficient F k)
  have he := matrixCircleEnergy_hasSum F hF
  have hpair := matrix_hilbert_pairing_hasSum F hF
  have hsign : HasSum (fun k : ℤ => (k.sign : ℝ)*e k)
      (-(∫ t, Circulation.tr ((F t)ᴴ*matrixHilbert F t) ∂circleMeasure).im) := by
    have h := (Complex.imCLM.hasSum hpair).neg
    convert h using 1
    · funext k
      simp [hilbertMultiplier, Complex.mul_im, e]
    · simp only [Complex.imCLM_apply]
  have enat : Summable (fun n : ℕ => e (n : ℤ)) :=
    he.summable.comp_injective Nat.cast_injective
  have eneg : Summable (fun n : ℕ => e (-(n + 1 : ℤ))) :=
    he.summable.comp_injective
      (show Function.Injective (fun n : ℕ => -(n + 1 : ℤ)) by
        intro a b hab
        have hh : (a : ℤ) + 1 = (b : ℤ) + 1 := neg_injective hab
        omega)
  have snat : Summable (fun n : ℕ => ((n : ℤ).sign : ℝ) * e (n : ℤ)) :=
    hsign.summable.comp_injective Nat.cast_injective
  have sneg : Summable (fun n : ℕ => ((-(n + 1 : ℤ)).sign : ℝ) * e (-(n + 1 : ℤ))) :=
    hsign.summable.comp_injective
      (show Function.Injective (fun n : ℕ => -(n + 1 : ℤ)) by
        intro a b hab
        have hh : (a : ℤ) + 1 = (b : ℤ) + 1 := neg_injective hab
        omega)
  have htotal := he.tsum_eq
  have hsigned := hsign.tsum_eq
  rw [tsum_of_nat_of_neg_add_one enat eneg, enat.tsum_eq_zero_add] at htotal
  rw [tsum_of_nat_of_neg_add_one snat sneg, snat.tsum_eq_zero_add] at hsigned
  have hpos (n : ℕ) : (((n : ℤ)+1).sign : ℝ) = 1 := by
    rw [Int.sign_eq_one_of_pos (by omega)]
    norm_num
  have hneg (n : ℕ) : ((-(n+1 : ℤ)).sign : ℝ) = -1 := by
    rw [Int.sign_eq_neg_one_of_neg (by omega)]
    norm_num
  simp only [Nat.cast_zero, Int.sign_zero, Int.cast_zero, zero_mul, zero_add, Nat.cast_add, Nat.cast_one,
    hpos, hneg, one_mul, neg_one_mul, tsum_neg] at hsigned
  change _ = matrixCircleEnergy F-e 0-2*(∑' n : ℕ, e (-((n+1 : ℕ) : ℤ)))
  change e 0 + (∑' n : ℕ, e ((n+1 : ℕ) : ℤ)) +
    (∑' n : ℕ, e (-(n+1 : ℤ))) = matrixCircleEnergy F at htotal
  change (∑' n : ℕ, e ((n+1 : ℕ) : ℤ)) -
    (∑' n : ℕ, e (-(n+1 : ℤ))) = _ at hsigned
  simp only [Nat.cast_add, Nat.cast_one] at htotal hsigned ⊢
  linarith

end
end CGLMPBounds.Hardy
