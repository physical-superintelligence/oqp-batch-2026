module

public import ThreeCopyQutritWerner.CertificateRepeatedMetricPositivity

@[expose] public section


/-!
# Positive physical realization from the exact frame Gram

The scalar overlap matrix is proved positive from a principal submatrix of
an actual physical Gram. The resulting construction takes only the original
weighted positive blocks and a complete physical frame basis.
-/

noncomputable section

open scoped Matrix ComplexOrder

namespace ThreeCopyQutritWerner

private theorem certificate_frame_pivot_cast {T : Type*} (size : T → ℕ)
    (pivot : (t : T) → Fin (size t)) {t u : T} (h : t = u) :
    h.symm ▸ pivot u = pivot t := by
  subst u
  rfl

/-- The column index may be infinite: every test vector has finite support. -/
private theorem certificate_frame_gram_posSemidef
    {n m : Type*} [Fintype n] (S : Matrix n m ℂ) :
    (Sᴴ * S).PosSemidef := by
  classical
  refine ⟨Matrix.isHermitian_conjTranspose_mul_self S, fun x => ?_⟩
  have hSS : ((Sᴴ * S).submatrix (↑) (↑) : Matrix x.support x.support ℂ).PosSemidef := by
    have heq : (Sᴴ * S).submatrix (↑) (↑) =
        (S.submatrix id ((↑) : x.support → m))ᴴ *
          S.submatrix id ((↑) : x.support → m) := by
      ext i j
      rfl
    rw [heq]
    exact Matrix.posSemidef_conjTranspose_mul_self _
  simpa [Finsupp.sum, ← Finset.sum_attach x.support, ← Finset.subtype_mem_eq_attach,
    ← Finsupp.subtypeDomain_apply, ← Finsupp.support_subtypeDomain] using hSS.2 _

/-- Positivity of the scalar descendant overlaps follows from the physical Gram,
without any additional numerical positivity premise. -/
theorem certificate_scalar_metric_posSemidef_of_gram
    {n F T : Type*} [Fintype n] [DecidableEq T]
    (size : T → ℕ) (type : F → T)
    (pivot : (t : T) → Fin (size t))
    (S : Matrix n (Σ f, Fin (size (type f))) ℂ)
    (G : (t : T) → Matrix (Fin (size t)) (Fin (size t)) ℂ)
    (K : Matrix F F ℂ) (hG : ∀ t, (G t).PosDef)
    (hGram : Sᴴ * S = certificateRepeatedFrameMetric size type G K)
    (hzero : ∀ f f', type f ≠ type f' → K f f' = 0) :
    K.PosSemidef := by
  let pick : F → Σ f, Fin (size (type f)) := fun f => ⟨f, pivot (type f)⟩
  let g : T → ℝ := fun t => (G t (pivot t) (pivot t)).re
  have hg : ∀ t, 0 < g t := fun t => (Complex.pos_iff.mp (hG t).diag_pos).1
  have hreal (t : T) : (g t : ℂ) = G t (pivot t) (pivot t) := by
    apply Complex.ext
    · rfl
    · exact (Complex.pos_iff.mp (hG t).diag_pos).2
  apply certificate_scalar_metric_posSemidef type K ((Sᴴ * S).submatrix pick pick)
    g hg ((certificate_frame_gram_posSemidef S).submatrix pick) hzero
  intro f f'
  rw [hGram]
  change certificateRepeatedFrameMetric size type G K
    ⟨f, pivot (type f)⟩ ⟨f', pivot (type f')⟩ = _
  by_cases h : type f = type f'
  · simp only [certificateRepeatedFrameMetric, dif_pos h, if_pos h, hreal]
    exact congrArg (fun j : Fin (size (type f)) =>
      K f f' * G (type f) (pivot (type f)) j)
      (certificate_frame_pivot_cast size pivot h)
  · simp only [certificateRepeatedFrameMetric, dif_neg h, if_neg h]

/-- The repeated source metric commutes with a scalar ring homomorphism. -/
theorem certificateRepeatedFrameMetric_map
    {F T R R' : Type*} [DecidableEq T] [Semiring R] [Semiring R']
    (size : T → ℕ) (type : F → T)
    (G : (t : T) → Matrix (Fin (size t)) (Fin (size t)) R)
    (K : Matrix F F R) (φ : R →+* R') :
    (certificateRepeatedFrameMetric size type G K).map φ =
      certificateRepeatedFrameMetric size type (fun t => (G t).map φ) (K.map φ) := by
  ext i j
  by_cases h : type i.1 = type j.1 <;>
    simp [certificateRepeatedFrameMetric, Matrix.map_apply, h]

/-- An exact integer physical Gram is the same Gram over the complex numbers. -/
theorem certificate_integer_gram_complex
    {n m : Type*} [Fintype n] (S : Matrix n m ℤ) (H : Matrix m m ℤ)
    (h : Sᵀ * S = H) :
    (S.map (Int.cast : ℤ → ℂ))ᴴ * S.map (Int.cast : ℤ → ℂ) =
      H.map (Int.cast : ℤ → ℂ) := by
  have ht : (S.map (Int.cast : ℤ → ℂ))ᴴ = Sᵀ.map (Int.cast : ℤ → ℂ) := by
    ext i j
    simp
  rw [ht]
  change Sᵀ.map (Int.castRingHom ℂ) * S.map (Int.castRingHom ℂ) =
    H.map (Int.castRingHom ℂ)
  rw [← Matrix.map_mul, h]

/-- Every family of original-metric positive blocks has an actual positive
physical realization with exactly the prescribed action on the complete basis. -/
theorem certificate_exists_positive_frame_realization
    {n F T : Type*} [Fintype n] [DecidableEq n]
    [Fintype F] [DecidableEq F] [Fintype T] [DecidableEq T]
    (size : T → ℕ) (type : F → T)
    (pivot : (t : T) → Fin (size t))
    (S : Matrix n (Σ f, Fin (size (type f))) ℂ)
    (G A : (t : T) → Matrix (Fin (size t)) (Fin (size t)) ℂ)
    (K : Matrix F F ℂ) (hS : Function.Bijective S.mulVec)
    (hG : ∀ t, (G t).PosDef)
    (hGram : Sᴴ * S = certificateRepeatedFrameMetric size type G K)
    (hzero : ∀ f f', type f ≠ type f' → K f f' = 0)
    (hGA : ∀ t, (G t * A t).PosSemidef) :
    ∃ M : Matrix n n ℂ, M.PosSemidef ∧
      M * S = S * Matrix.blockDiagonal' (fun f => A (type f)) := by
  obtain ⟨V, hSV, hVS⟩ := certificate_exists_inverse_of_bijective S hS
  have hK := certificate_scalar_metric_posSemidef_of_gram
    size type pivot S G K hG hGram hzero
  refine ⟨S * Matrix.blockDiagonal' (fun f => A (type f)) * V, ?_, ?_⟩
  · exact certificate_repeated_realization_posSemidef size type S V G A K
      hSV hGram hK hGA
  · exact certificate_realization_action S V _ hVS

end ThreeCopyQutritWerner
