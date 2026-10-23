module

public import CGLMPBounds.Hardy.CircularHilbertBasics

@[expose] public section


/-! Scalar Parseval pairing and conjugation/skew-adjointness of the genuine
circular L² Hilbert transform. All equalities of representatives are a.e. -/

namespace CGLMPBounds.Hardy
open MeasureTheory Matrix
open scoped ComplexConjugate InnerProductSpace
noncomputable section
local instance : Fact (0 < (1 : ℝ)) := ⟨zero_lt_one⟩

theorem circle_fourierCoeff_conj (f : UnitCircle → ℂ) (k : ℤ) :
    fourierCoeff (fun t => conj (f t)) k = conj (fourierCoeff f (-k)) := by
  unfold fourierCoeff
  rw [← integral_conj]
  apply integral_congr_ae
  filter_upwards [] with t
  simp only [smul_eq_mul, map_mul, neg_neg, ← fourier_neg]

theorem scalar_circle_fourier_unique (f g : UnitCircle → ℂ)
    (hf : MemLp f 2 circleMeasure) (hg : MemLp g 2 circleMeasure)
    (hcoeff : ∀ k : ℤ, fourierCoeff f k = fourierCoeff g k) : f =ᵐ[circleMeasure] g := by
  have hLp : hf.toLp f = hg.toLp g := by
    apply (fourierBasis (T := 1)).repr.injective
    ext k
    simpa only [fourierBasis_repr, fourierCoeff_congr_ae hf.coeFn_toLp,
      fourierCoeff_congr_ae hg.coeFn_toLp] using hcoeff k
  exact hf.coeFn_toLp.symm.trans ((Filter.EventuallyEq.of_eq (congrArg (fun z : CircleL2 => (z : UnitCircle → ℂ)) hLp)).trans hg.coeFn_toLp)

theorem scalarHilbert_conj (f : UnitCircle → ℂ) (hf : MemLp f 2 circleMeasure) :
    scalarHilbert (fun t => conj (f t)) =ᵐ[circleMeasure]
      fun t => conj (scalarHilbert f t) := by
  have hfc : MemLp (fun t => conj (f t)) 2 circleMeasure := by
    have he : star f = (fun t => conj (f t)) := rfl
    simpa only [he] using hf.star
  have hHc : MemLp (fun t => conj (scalarHilbert f t)) 2 circleMeasure := by
    have he : star (scalarHilbert f) = (fun t => conj (scalarHilbert f t)) := rfl
    simpa only [he] using (scalarHilbert_memLp f).star
  apply scalar_circle_fourier_unique _ _ (scalarHilbert_memLp _) hHc
  intro k
  rw [scalarHilbert_fourierCoeff _ hfc, circle_fourierCoeff_conj,
    circle_fourierCoeff_conj, scalarHilbert_fourierCoeff _ hf, map_mul,
    hilbertMultiplier_conj, hilbertMultiplier_neg, neg_neg]

theorem scalar_circle_parseval_pairing (f g : UnitCircle → ℂ)
    (hf : MemLp f 2 circleMeasure) (hg : MemLp g 2 circleMeasure) :
    HasSum (fun k : ℤ => conj (fourierCoeff f k) * fourierCoeff g k)
      (∫ t, conj (f t) * g t ∂circleMeasure) := by
  have h := (fourierBasis (T := 1)).hasSum_inner_mul_inner (hf.toLp f) (hg.toLp g)
  have hterm (k : ℤ) :
      inner ℂ (hf.toLp f) (fourierBasis (T := 1) k) *
          inner ℂ (fourierBasis (T := 1) k) (hg.toLp g) =
        conj (fourierCoeff f k) * fourierCoeff g k := by
    rw [← inner_conj_symm (hf.toLp f) (fourierBasis (T := 1) k),
      ← HilbertBasis.repr_apply_apply, ← HilbertBasis.repr_apply_apply,
      fourierBasis_repr, fourierBasis_repr,
      fourierCoeff_congr_ae hf.coeFn_toLp, fourierCoeff_congr_ae hg.coeFn_toLp]
  have hval : inner ℂ (hf.toLp f) (hg.toLp g) =
      ∫ t, conj (f t) * g t ∂circleMeasure := by
    rw [L2.inner_def]
    apply integral_congr_ae
    filter_upwards [hf.coeFn_toLp, hg.coeFn_toLp] with t hft hgt
    simp only [hft, hgt, RCLike.inner_apply']
  simpa only [hterm, hval] using h

theorem scalarHilbert_skewAdjoint (f g : UnitCircle → ℂ)
    (hf : MemLp f 2 circleMeasure) (hg : MemLp g 2 circleMeasure) :
    (∫ t, conj (f t) * scalarHilbert g t ∂circleMeasure) =
      -(∫ t, conj (scalarHilbert f t) * g t ∂circleMeasure) := by
  have hleft := scalar_circle_parseval_pairing f (scalarHilbert g) hf (scalarHilbert_memLp g)
  have hright := (scalar_circle_parseval_pairing (scalarHilbert f) g
    (scalarHilbert_memLp f) hg).neg
  apply hleft.unique
  convert hright using 1
  ext k
  rw [scalarHilbert_fourierCoeff _ hf, scalarHilbert_fourierCoeff _ hg,
    map_mul, hilbertMultiplier_conj]
  ring

theorem scalarHilbert_add (f g : UnitCircle → ℂ)
    (hf : MemLp f 2 circleMeasure) (hg : MemLp g 2 circleMeasure) :
    scalarHilbert (fun t => f t + g t) =ᵐ[circleMeasure]
      fun t => scalarHilbert f t + scalarHilbert g t := by
  apply scalar_circle_fourier_unique _ _ (scalarHilbert_memLp _)
    ((scalarHilbert_memLp f).add (scalarHilbert_memLp g))
  intro k
  change fourierCoeff (scalarHilbert (f + g)) k =
    fourierCoeff (scalarHilbert f + scalarHilbert g) k
  rw [scalarHilbert_fourierCoeff _ (hf.add hg)]
  change hilbertMultiplier k * fourierCoeff (f+g) k =
    fourierCoeff (scalarHilbert f + scalarHilbert g) k
  rw [fourierCoeff.add (hf.integrable (by norm_num)) (hg.integrable (by norm_num)),
    fourierCoeff.add ((scalarHilbert_memLp f).integrable (by norm_num))
      ((scalarHilbert_memLp g).integrable (by norm_num))]
  simp only [Pi.add_apply, scalarHilbert_fourierCoeff _ hf, scalarHilbert_fourierCoeff _ hg]
  ring

theorem scalarHilbert_const_mul (f : UnitCircle → ℂ)
    (hf : MemLp f 2 circleMeasure) (c : ℂ) :
    scalarHilbert (fun t => c*f t) =ᵐ[circleMeasure]
      fun t => c*scalarHilbert f t := by
  apply scalar_circle_fourier_unique _ _ (scalarHilbert_memLp _)
    ((scalarHilbert_memLp f).const_smul c)
  intro k
  change fourierCoeff (scalarHilbert (c • f)) k =
    fourierCoeff (c • scalarHilbert f) k
  rw [scalarHilbert_fourierCoeff _ (hf.const_smul c), fourierCoeff.const_smul,
    fourierCoeff.const_smul, scalarHilbert_fourierCoeff _ hf]
  simp only [smul_eq_mul]
  ring

theorem scalarHilbert_congr_ae (f g : UnitCircle → ℂ)
    (hfg : f =ᵐ[circleMeasure] g) : scalarHilbert f = scalarHilbert g := by
  unfold scalarHilbert scalarHilbertLp
  simp only [fourierCoeff_congr_ae hfg]

end
end CGLMPBounds.Hardy
