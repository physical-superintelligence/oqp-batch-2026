module

public import CGLMPBounds.Hardy.PoissonFourierSeries
public import Mathlib.Analysis.Normed.Group.Tannery

@[expose] public section


/-! Genuine L² radial convergence of the scalar Herglotz integral to f+iHf.
The actual Fourier coefficients are computed first; Parseval and dominated
convergence of their squared norms give the limit. -/
namespace CGLMPBounds.Hardy
noncomputable section
open Set MeasureTheory Filter Complex
open scoped Topology ComplexConjugate
local instance : Fact (0 < (1 : ℝ)) := ⟨zero_lt_one⟩

lemma scalar_circle_parseval_norm_sq (f : UnitCircle → ℂ)
    (hf : MemLp f 2 circleMeasure) :
    (∫ t, ‖f t‖^2 ∂circleMeasure) = ∑' k : ℤ, ‖fourierCoeff f k‖^2 := by
  have h := hasSum_sq_fourierCoeff (hf.toLp f)
  have he : (∫ t, ‖hf.toLp f t‖^2 ∂circleMeasure) = ∫ t, ‖f t‖^2 ∂circleMeasure := by
    apply integral_congr_ae
    exact hf.coeFn_toLp.mono fun t ht => by
      change ‖hf.toLp f t‖^2 = ‖f t‖^2
      rw [ht]
  rw [he] at h
  simpa only [fourierCoeff_congr_ae hf.coeFn_toLp] using h.tsum_eq.symm

lemma circle_fourierCoeff_sub {f g : UnitCircle → ℂ}
    (hf : Integrable f circleMeasure) (hg : Integrable g circleMeasure) (k : ℤ) :
    fourierCoeff (fun t => f t-g t) k = fourierCoeff f k-fourierCoeff g k := by
  simp only [fourierCoeff,smul_sub]
  exact integral_sub (hf.fourier_smul (-k)) (hg.fourier_smul (-k))

lemma scalar_analytic_boundary_memLp (f : UnitCircle → ℂ)
    (hf : MemLp f 2 circleMeasure) :
    MemLp (fun t => f t + Complex.I*scalarHilbert f t) 2 circleMeasure :=
  hf.add ((scalarHilbert_memLp f).const_smul Complex.I)

lemma scalar_analytic_boundary_fourierCoeff (f : UnitCircle → ℂ)
    (hf : MemLp f 2 circleMeasure) (k : ℤ) :
    fourierCoeff (fun t => f t + Complex.I*scalarHilbert f t) k =
      if k=0 then fourierCoeff f 0 else if 0<k then 2*fourierCoeff f k else 0 := by
  change fourierCoeff (f + (fun t => Complex.I*scalarHilbert f t)) k = _
  rw [fourierCoeff.add (hf.integrable (by norm_num))
    (((scalarHilbert_memLp f).integrable (by norm_num)).const_mul Complex.I),
    Pi.add_apply,fourierCoeff.const_mul,scalarHilbert_fourierCoeff f hf]
  simp only [Pi.add_apply,hilbertMultiplier]
  by_cases hk : k=0
  · simp [hk]
  · by_cases hpos : 0<k
    · simp [hk,hpos,Int.sign_eq_one_of_pos hpos] <;>
        ring_nf <;> norm_num [Complex.I_sq] <;> ring
    · have hneg : k < 0 := by omega
      simp [hk,hpos,Int.sign_eq_neg_one_of_neg hneg] <;>
        ring_nf <;> norm_num [Complex.I_sq] <;> ring

lemma scalarPoissonRadial_memLp {f : UnitCircle → ℂ}
    (hf : Integrable f circleMeasure) {ρ : ℝ} (hρ : ρ ∈ Ico (0 : ℝ) 1) :
    MemLp (fun t : UnitCircle => scalarPoissonIntegral f ((ρ : ℂ)*fourier 1 t)) 2 circleMeasure :=
  (scalarPoissonRadial_continuous hf hρ).memLp_of_hasCompactSupport
    (HasCompactSupport.of_compactSpace _)

lemma scalarPoissonRadial_error_integral {f : UnitCircle → ℂ}
    (hf : MemLp f 2 circleMeasure) {ρ : ℝ} (hρ : ρ ∈ Ico (0 : ℝ) 1) :
    (∫ t, ‖scalarPoissonIntegral f ((ρ : ℂ)*fourier 1 t) -
      (f t+Complex.I*scalarHilbert f t)‖^2 ∂circleMeasure) =
    ∑' k : ℤ, if 0<k then
      ‖(2*((ρ : ℂ)^k.toNat-1))*fourierCoeff f k‖^2 else 0 := by
  have hfi := hf.integrable (by norm_num)
  have hrho := scalarPoissonRadial_memLp hfi hρ
  have hboundary := scalar_analytic_boundary_memLp f hf
  have hdiff : MemLp (fun t => scalarPoissonIntegral f ((ρ : ℂ)*fourier 1 t) -
      (f t+Complex.I*scalarHilbert f t)) 2 circleMeasure := by
    convert! hrho.sub hboundary using 1 <;> rfl
  rw [scalar_circle_parseval_norm_sq _ hdiff]
  apply tsum_congr
  intro k
  rw [circle_fourierCoeff_sub (hrho.integrable (by norm_num)) (hboundary.integrable (by norm_num)),
    scalarPoissonRadial_fourierCoeff hfi hρ,scalar_analytic_boundary_fourierCoeff f hf]
  by_cases hk : k=0
  · simp [hk]
  · by_cases hp : 0<k
    · simp only [if_neg hk,if_pos hp,Pi.sub_apply]
      congr 2
      ring
    · simp [hk,hp]

theorem scalarPoissonRadial_L2_tendsto {f : UnitCircle → ℂ}
    (hf : MemLp f 2 circleMeasure) :
    Tendsto (fun ρ : ℝ => ∫ t,
      ‖scalarPoissonIntegral f ((ρ : ℂ)*fourier 1 t) -
        (f t+Complex.I*scalarHilbert f t)‖^2 ∂circleMeasure)
      (𝓝[<] 1) (𝓝 0) := by
  let F : ℝ → ℤ → ℝ := fun ρ k => if 0<k then
    ‖(2*((ρ : ℂ)^k.toNat-1))*fourierCoeff f k‖^2 else 0
  have hsum : Summable (fun k : ℤ => 4*‖fourierCoeff f k‖^2) :=
    (scalar_fourier_hasSum_norm_sq f hf).summable.mul_left 4
  have hterm (k : ℤ) : Tendsto (fun ρ => F ρ k) (𝓝[<] 1) (𝓝 0) := by
    by_cases hk : 0<k
    · have hc : ContinuousAt (fun ρ : ℝ =>
          ‖(2*((ρ : ℂ)^k.toNat-1))*fourierCoeff f k‖^2) 1 := by fun_prop
      simpa [F,hk] using hc.tendsto.mono_left nhdsWithin_le_nhds
    · simp only [F,if_neg hk]
      exact tendsto_const_nhds
  have hbound : ∀ᶠ ρ : ℝ in 𝓝[<] 1, ∀ k : ℤ,
      ‖F ρ k‖ ≤ 4*‖fourierCoeff f k‖^2 := by
    filter_upwards [Ioo_mem_nhdsLT zero_lt_one] with ρ hρ
    intro k
    by_cases hk : 0<k
    · have hp0 : 0 ≤ ρ^k.toNat := pow_nonneg hρ.1.le _
      have hp1 : ρ^k.toNat ≤ 1 := pow_le_one₀ hρ.1.le hρ.2.le
      have hnorm : ‖(ρ : ℂ)^k.toNat-1‖ ≤ 1 := by
        rw [← Complex.ofReal_pow,← Complex.ofReal_one,← Complex.ofReal_sub,
          Complex.norm_real,Real.norm_eq_abs]
        exact abs_le.mpr ⟨by linarith,by linarith⟩
      simp only [F,if_pos hk,Real.norm_eq_abs,abs_sq,norm_mul,norm_ofNat]
      have hm : 2*‖(ρ : ℂ)^k.toNat-1‖*‖fourierCoeff f k‖ ≤
          2*‖fourierCoeff f k‖ := by
        nlinarith [mul_le_mul_of_nonneg_right hnorm (norm_nonneg (fourierCoeff f k))]
      calc
        _ ≤ (2*‖fourierCoeff f k‖)^2 :=
          (sq_le_sq₀ (by positivity) (by positivity)).2 hm
        _ = _ := by ring
    · simp only [F,if_neg hk,norm_zero]
      positivity
  have ht := tendsto_tsum_of_dominated_convergence hsum hterm hbound
  simp only [tsum_zero] at ht
  apply ht.congr'
  filter_upwards [Ioo_mem_nhdsLT zero_lt_one] with ρ hρ
  exact (scalarPoissonRadial_error_integral hf ⟨hρ.1.le,hρ.2⟩).symm

theorem scalarPoissonRadial_L2_bound {f : UnitCircle → ℂ}
    (hf : MemLp f 2 circleMeasure) {ρ : ℝ} (hρ : ρ ∈ Ico (0 : ℝ) 1) :
    (∫ t, ‖scalarPoissonIntegral f ((ρ : ℂ)*fourier 1 t)‖^2 ∂circleMeasure) ≤
      4*(∫ t, ‖f t‖^2 ∂circleMeasure) := by
  rw [scalar_circle_parseval_norm_sq _ (scalarPoissonRadial_memLp
    (hf.integrable (by norm_num)) hρ),scalar_circle_parseval_norm_sq f hf,← tsum_mul_left]
  apply Summable.tsum_le_tsum
  · intro k
    rw [scalarPoissonRadial_fourierCoeff (hf.integrable (by norm_num)) hρ]
    split_ifs with hk hk
    · subst k
      nlinarith [sq_nonneg ‖fourierCoeff f 0‖]
    · have hp : ρ^k.toNat ≤ 1 := pow_le_one₀ hρ.1 hρ.2.le
      simp only [norm_mul,norm_pow,norm_ofNat,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg hρ.1]
      have hp0 : 0 ≤ ρ^k.toNat := pow_nonneg hρ.1 _
      have hm : 2*ρ^k.toNat*‖fourierCoeff f k‖ ≤ 2*‖fourierCoeff f k‖ := by
        nlinarith [mul_le_mul_of_nonneg_right hp (norm_nonneg (fourierCoeff f k))]
      calc
        _ ≤ (2*‖fourierCoeff f k‖)^2 :=
          (sq_le_sq₀ (by positivity) (by positivity)).2 hm
        _ = _ := by ring
    · simp <;> positivity
  · exact (scalar_fourier_hasSum_norm_sq _ (scalarPoissonRadial_memLp
      (hf.integrable (by norm_num)) hρ)).summable
  · exact (scalar_fourier_hasSum_norm_sq f hf).summable.mul_left 4

end
end CGLMPBounds.Hardy
