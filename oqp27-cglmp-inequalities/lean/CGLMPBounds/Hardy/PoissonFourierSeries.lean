module

public import CGLMPBounds.Hardy.PoissonAnalytic
public import CGLMPBounds.Hardy.CircularHilbertParseval

@[expose] public section


/-! Actual scalar Herglotz integrals have the genuine positive-frequency
power series. Integrals are interchanged with an absolutely dominated
geometric series, using the L¹ norm of the given boundary function. -/
namespace CGLMPBounds.Hardy
noncomputable section
open MeasureTheory Filter Complex
open scoped Topology ComplexConjugate
local instance : Fact (0 < (1 : ℝ)) := ⟨zero_lt_one⟩

def scalarPoissonIntegral (f : UnitCircle → ℂ) (z : ℂ) : ℂ :=
  ∫ t, circleHerglotzKernel z t*f t ∂circleMeasure

lemma circle_fourierCoeff_norm_le (f : UnitCircle → ℂ) (k : ℤ) :
    ‖fourierCoeff f k‖ ≤ ∫ t, ‖f t‖ ∂circleMeasure := by
  unfold fourierCoeff
  apply (norm_integral_le_integral_norm _).trans_eq
  apply integral_congr_ae
  exact Eventually.of_forall fun t => by
    change ‖fourier (-k) t • f t‖ = ‖f t‖
    rw [norm_smul,circle_fourier_norm,one_mul]

lemma circle_fourierCoeff_zero (f : UnitCircle → ℂ) :
    fourierCoeff f 0 = ∫ t, f t ∂circleMeasure := by
  simp only [fourierCoeff,neg_zero,fourier_zero,one_smul]

lemma scalarPoissonIntegral_series {f : UnitCircle → ℂ} (hf : Integrable f circleMeasure)
    {z : ℂ} (hz : ‖z‖ < 1) :
    scalarPoissonIntegral f z = fourierCoeff f 0 +
      2 * ∑' n : ℕ, z^(n+1)*fourierCoeff f ((n+1 : ℕ) : ℤ) := by
  let F : ℕ → UnitCircle → ℂ := fun n t => (z/fourier 1 t)^(n+1)*f t
  have hF (n : ℕ) : Integrable (F n) circleMeasure := by
    have he : F n = fun t => z^(n+1)*(fourier (-((n+1 : ℕ) : ℤ)) t*f t) := by
      funext t
      dsimp only [F]
      rw [circle_geometric_term_eq,mul_assoc]
    rw [he]
    exact (hf.fourier_smul (-((n+1 : ℕ) : ℤ))).const_mul _
  have hsum : Summable (fun n : ℕ => ∫ t, ‖F n t‖ ∂circleMeasure) := by
    have he (n : ℕ) : (∫ t, ‖F n t‖ ∂circleMeasure) =
        ‖z‖^(n+1)*(∫ t, ‖f t‖ ∂circleMeasure) := by
      simp only [F,norm_mul,norm_pow,norm_div,circle_fourier_norm,div_one,integral_const_mul]
    simp_rw [he]
    exact ((summable_nat_add_iff 1).mpr
      (summable_geometric_of_lt_one (norm_nonneg z) hz)).mul_right _
  have heval (t : UnitCircle) : (∑' n : ℕ, F n t) =
      ((circleHerglotzKernel z t-1)/2)*f t := by
    exact ((circleHerglotzKernel_hasSum hz t).mul_right (f t)).tsum_eq
  have hactual : Integrable (fun t => ((circleHerglotzKernel z t-1)/2)*f t) circleMeasure := by
    have h := ((circleHerglotz_mul_integrable hz hf).sub hf).div_const (2 : ℂ)
    convert h using 1
    ext t
    change ((circleHerglotzKernel z t-1)/2)*f t =
      (circleHerglotzKernel z t*f t-f t)/2
    ring
  have hinter := integral_tsum_of_summable_integral_norm hF hsum
  have hcoeff (n : ℕ) : (∫ t, F n t ∂circleMeasure) =
      z^(n+1)*fourierCoeff f ((n+1 : ℕ) : ℤ) := by
    simp only [F,circle_geometric_term_eq,mul_assoc,integral_const_mul,fourierCoeff,smul_eq_mul]
  simp_rw [hcoeff,heval] at hinter
  have hefun : (fun t => circleHerglotzKernel z t*f t) =
      (fun t => f t + 2*(((circleHerglotzKernel z t-1)/2)*f t)) := by
    funext t
    ring
  rw [scalarPoissonIntegral,hefun,integral_add hf (hactual.const_mul _),integral_const_mul,
    ← hinter,circle_fourierCoeff_zero]

lemma scalarPoissonRadial_series {f : UnitCircle → ℂ} (hf : Integrable f circleMeasure)
    {ρ : ℝ} (hρ : ρ ∈ Set.Ico (0 : ℝ) 1) (t : UnitCircle) :
    scalarPoissonIntegral f ((ρ : ℂ)*fourier 1 t) = fourierCoeff f 0 +
      2 * ∑' n : ℕ, ((ρ : ℂ)^(n+1)*fourierCoeff f ((n+1 : ℕ) : ℤ))*
        fourier ((n+1 : ℕ) : ℤ) t := by
  rw [scalarPoissonIntegral_series hf (by
    simpa only [norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg hρ.1,
      circle_fourier_norm,mul_one] using hρ.2)]
  congr 2
  apply tsum_congr
  intro n
  rw [mul_pow,circle_fourier_nat_pow]
  ring

lemma scalarPoissonRadial_continuous {f : UnitCircle → ℂ}
    (hf : Integrable f circleMeasure) {ρ : ℝ} (hρ : ρ ∈ Set.Ico (0 : ℝ) 1) :
    Continuous (fun t : UnitCircle => scalarPoissonIntegral f ((ρ : ℂ)*fourier 1 t)) := by
  have ha : AnalyticOnNhd ℂ (scalarPoissonIntegral f) (Metric.ball 0 1) := by
    intro z hz
    exact analyticAt_circleHerglotz_integral (by simpa [Metric.mem_ball,dist_zero_right] using hz) hf
  apply ha.continuousOn.comp_continuous (continuous_const.mul (fourier 1).continuous)
  intro t
  simpa only [Metric.mem_ball,dist_zero_right,Pi.mul_apply,norm_mul,Complex.norm_real,Real.norm_eq_abs,
    abs_of_nonneg hρ.1,circle_fourier_norm,mul_one] using hρ.2

lemma circle_fourierCoeff_const (c : ℂ) (k : ℤ) :
    fourierCoeff (fun _ : UnitCircle => c) k = if k=0 then c else 0 := by
  rw [fourierCoeff]
  simp only [smul_eq_mul,integral_mul_const,circle_integral_fourier,neg_eq_zero]
  split_ifs <;> simp_all

lemma scalarPoissonRadial_fourierCoeff {f : UnitCircle → ℂ}
    (hf : Integrable f circleMeasure) {ρ : ℝ} (hρ : ρ ∈ Set.Ico (0 : ℝ) 1) (k : ℤ) :
    fourierCoeff (fun t : UnitCircle => scalarPoissonIntegral f ((ρ : ℂ)*fourier 1 t)) k =
      if k=0 then fourierCoeff f 0 else if 0<k then
        2*(ρ : ℂ)^k.toNat*fourierCoeff f k else 0 := by
  let a : ℕ → ℂ := fun n => (ρ : ℂ)^(n+1)*fourierCoeff f ((n+1 : ℕ) : ℤ)
  have ha : Summable (fun n : ℕ => ‖a n‖) := by
    apply Summable.of_nonneg_of_le (fun _ => norm_nonneg _) _
      (((summable_nat_add_iff 1).mpr
        (summable_geometric_of_lt_one hρ.1 hρ.2)).mul_right (∫ t, ‖f t‖ ∂circleMeasure))
    intro n
    dsimp only [a]
    rw [norm_mul,norm_pow,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg hρ.1]
    exact mul_le_mul_of_nonneg_left (circle_fourierCoeff_norm_le f _) (pow_nonneg hρ.1 _)
  let G : ℕ → UnitCircle → ℂ := fun n t => a n*fourier ((n+1 : ℕ) : ℤ) t
  have hG (n : ℕ) : Integrable (G n) circleMeasure :=
    (((fourier ((n+1 : ℕ) : ℤ)).continuous).const_mul (a n)).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hmod (n : ℕ) : Integrable (fun t => fourier (-k) t*G n t) circleMeasure :=
    (hG n).fourier_smul (-k)
  have hsum : Summable (fun n : ℕ => ∫ t, ‖fourier (-k) t*G n t‖ ∂circleMeasure) := by
    simpa only [G,norm_mul,circle_fourier_norm,one_mul,mul_one,integral_const,measure_univ,
      probReal_univ,ENNReal.toReal_one,one_smul] using ha
  have hinter := integral_tsum_of_summable_integral_norm hmod hsum
  have hsumG : Integrable (fun t => ∑' n, G n t) circleMeasure := by
    have hc : Continuous (fun t => ∑' n, G n t) := by
      apply continuous_tsum (fun n => ((fourier ((n+1 : ℕ) : ℤ)).continuous).const_mul (a n)) ha
      intro n t
      simp only [G,norm_mul,circle_fourier_norm,mul_one,le_refl]
    exact hc.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hcoeff : fourierCoeff (fun t => ∑' n, G n t) k =
      ∑' n : ℕ, if k=((n+1 : ℕ) : ℤ) then a n else 0 := by
    unfold fourierCoeff
    simp only [smul_eq_mul]
    have hpoint (t : UnitCircle) : fourier (-k) t*(∑' n, G n t) =
        ∑' n, fourier (-k) t*G n t := (tsum_mul_left).symm
    simp_rw [hpoint,← hinter]
    apply tsum_congr
    intro n
    have he : (fun t => fourier (-k) t*G n t) =
        (fun t => a n*fourier (-k+((n+1 : ℕ) : ℤ)) t) := by
      funext t
      dsimp only [G]
      rw [fourier_add]
      ring
    rw [he,integral_const_mul,circle_integral_fourier]
    by_cases hk : k=((n+1 : ℕ) : ℤ)
    · simp [hk]
    · rw [if_neg (show -k+((n+1 : ℕ) : ℤ) ≠ 0 by omega),mul_zero,if_neg hk]
  have hfun : (fun t => scalarPoissonIntegral f ((ρ : ℂ)*fourier 1 t)) =
      (fun t => fourierCoeff f 0 + 2*(∑' n, G n t)) :=
    funext (fun t => scalarPoissonRadial_series hf hρ t)
  rw [hfun]
  change fourierCoeff ((fun _ : UnitCircle => fourierCoeff f 0) +
    (fun t => 2*(∑' n, G n t))) k = _
  rw [fourierCoeff.add (integrable_const _) (hsumG.const_mul _),Pi.add_apply,
    fourierCoeff.const_mul,circle_fourierCoeff_const,hcoeff]
  by_cases hk : 0<k
  · have hkn : k ≠ 0 := ne_of_gt hk
    rw [if_neg hkn,if_neg hkn,if_pos hk,zero_add]
    rw [tsum_eq_single (k.toNat-1)]
    · rw [if_pos (show k=((k.toNat-1+1 : ℕ) : ℤ) by omega)]
      dsimp only [a]
      rw [show k.toNat-1+1=k.toNat by omega,
        show (k.toNat : ℤ)=k by omega]
      ring
    · intro n hn
      exact if_neg (by omega)
  · have hs : (∑' n : ℕ, if k=((n+1 : ℕ) : ℤ) then a n else 0)=0 := by
      calc
        _ = ∑' _ : ℕ, (0 : ℂ) := tsum_congr (fun n => if_neg (by omega))
        _ = 0 := tsum_zero
    rw [hs,mul_zero,add_zero]
    simp only [if_neg hk]

end
end CGLMPBounds.Hardy
