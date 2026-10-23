module

public import ThreeCopyQutritWerner.ThinFixedRowSource
public import ThreeCopyQutritWerner.FixedRowPencilExtraction
public import ThreeCopyQutritWerner.ThinPencilFreeInput

@[expose] public section


/-!
# All original input blocks share the fixed-row projection

Two distinct nonzero source rays and the free third input coefficient
recover every original input block. The projector is constructed once from
the actual remaining-site/logical matrix; no input support is supplied.
-/

noncomputable section

open scoped Matrix ComplexConjugate

namespace ThreeCopyQutritWerner

theorem thinTensorSource_pencil
    (κ : Fin 3 × Fin 3 → ℂ) (R : Matrix (Fin 3) (Fin 2) ℂ) (z : ℂ) :
    firstSiteFactorBlock (thinTensorSource κ R) 0 +
      z • firstSiteFactorBlock (thinTensorSource κ R) 1 =
      twoSiteVectorSource ((fun b => κ (0, b)) + z • (fun b => κ (1, b))) R := by
  ext ⟨b, c⟩ j
  simp only [thinTensorSource, twoSiteVectorSource, firstSiteFactorBlock,
    Matrix.add_apply, Matrix.smul_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  ring

theorem thin_fixed_row_all_input_projection
    (X Y : Matrix QutritSites (Fin 2) ℂ)
    (κ : Fin 3 × Fin 3 → ℂ) (R : Matrix (Fin 3) (Fin 2) ℂ)
    (hX : X = thinTensorSource κ R) (hκ : κ ≠ 0) (hκ2 : ∀ b, κ (2, b) = 0)
    (hC : (X * Yᴴ).rank ≤ 2) (hz : endpointEnergy (X * Yᴴ) = 0)
    (hrow : ∀ r q, (X * Yᴴ) (2, r) q = 0) :
    ∃ P : Matrix (Fin 3) (Fin 3) ℂ,
      P.IsHermitian ∧ P * P = P ∧ P.rank = 2 ∧
      ∀ i j : Fin 3, ∃ α : ℂ,
        R * (firstSiteFactorBlock (firstSiteFactorBlock Y i) j)ᴴ = α • P := by
  let u : Fin 3 → ℂ := fun b => κ (0, b)
  let v : Fin 3 → ℂ := fun b => κ (1, b)
  have hn : u ≠ 0 ∨ v ≠ 0 := by
    by_contra! h
    apply hκ
    ext ⟨i, b⟩
    fin_cases i
    · exact congrFun h.1 b
    · exact congrFun h.2 b
    · exact hκ2 b
  obtain ⟨z, w, hzw, hzv, hwv⟩ := exists_two_distinct_nonzero_affine_rays u v hn
  obtain ⟨P, hP, hPP, hPr, _, hproj⟩ := fixed_row_exists_common_cut_projection R
  have hq (s t : ℂ) : cutForm (twoSiteVectorSource (u + s • v) R *
      (firstSiteFactorBlock Y 1 - conj s • firstSiteFactorBlock Y 0 +
        t • firstSiteFactorBlock Y 2)ᴴ) = 0 := by
    have he := (thinFirstSite_free_input_factor_rank_cut_zero X Y hC hz hrow s t).2
    rw [hX, thinTensorSource_pencil] at he
    exact he
  have hc (j : Fin 3) : ∃ a b d : ℂ,
      R * (firstSiteFactorBlock (firstSiteFactorBlock Y 0) j)ᴴ = a • P ∧
      R * (firstSiteFactorBlock (firstSiteFactorBlock Y 1) j)ᴴ = b • P ∧
      R * (firstSiteFactorBlock (firstSiteFactorBlock Y 2) j)ᴴ = d • P := by
    obtain ⟨α, hα⟩ := hproj (u + z • v) _ hzv (hq z 0) j
    obtain ⟨β, hβ⟩ := hproj (u + w • v) _ hwv (hq w 0) j
    obtain ⟨γ, hγ⟩ := hproj (u + z • v) _ hzv (hq z 1) j
    rw [fixedRow_partner_pencil_block] at hα hβ hγ
    simp only [map_zero, map_one,
      zero_smul, one_smul, add_zero] at hα hβ hγ
    exact matrix_affine_projection_coefficients _ _ _ P z w α β γ hzw hα hβ hγ
  refine ⟨P, hP, hPP, hPr, ?_⟩
  intro i j
  obtain ⟨a, b, d, ha, hb, hd⟩ := hc j
  fin_cases i
  · exact ⟨a, ha⟩
  · exact ⟨b, hb⟩
  · exact ⟨d, hd⟩

end ThreeCopyQutritWerner
