module

public import ThreeCopyQutritWerner.JointShadowMoments
public import ThreeCopyQutritWerner.PartialTraceLinear

@[expose] public section


/-! Exact original-coordinate algebra for the common shadow identity. -/

noncomputable section

open scoped BigOperators Matrix ComplexConjugate

namespace ThreeCopyQutritWerner

variable {a b c : Type*} [Fintype a] [Fintype b] [Fintype c]

/-- Original overlaps after tracing one physical site. -/
def jointShadowCrossA (D E : Matrix (a × b × c) (a × b × c) ℂ) : ℝ :=
  (hsInner (ptrace₁ D) (ptrace₁ E)).re +
    (hsInner (ptrace₂ D) (ptrace₂ E)).re + (hsInner (ptrace₃ D) (ptrace₃ E)).re

/-- Original overlaps after tracing two physical sites. -/
def jointShadowCrossB (D E : Matrix (a × b × c) (a × b × c) ℂ) : ℝ :=
  (hsInner (ptrace₁₂ D) (ptrace₁₂ E)).re +
    (hsInner (ptrace₁₃ D) (ptrace₁₃ E)).re + (hsInner (ptrace₂₃ D) (ptrace₂₃ E)).re

/-- The manuscript's actual three-physical-register shadow polynomial. -/
def jointShadowS3 (M : Matrix (a × b × c) (a × b × c) ℂ) : ℝ :=
  invN M - invA M + invB M

/-- Exact polarization of all three one-site partial-trace norms. -/
theorem jointShadow_invA_sub (D E : Matrix (a × b × c) (a × b × c) ℂ) :
    invA (D - E) = invA D + invA E - 2 * jointShadowCrossA D E := by
  have h1 : ptrace₁ (D - E) = ptrace₁ D - ptrace₁ E := ptrace₁LinearMap.map_sub D E
  have h2 : ptrace₂ (D - E) = ptrace₂ D - ptrace₂ E := ptrace₂LinearMap.map_sub D E
  have h3 : ptrace₃ (D - E) = ptrace₃ D - ptrace₃ E := ptrace₃LinearMap.map_sub D E
  unfold invA jointShadowCrossA
  rw [h1, h2, h3, frobSq_sub, frobSq_sub, frobSq_sub]
  ring

/-- Exact polarization of all three two-site partial-trace norms. -/
theorem jointShadow_invB_sub (D E : Matrix (a × b × c) (a × b × c) ℂ) :
    invB (D - E) = invB D + invB E - 2 * jointShadowCrossB D E := by
  have h1 : ptrace₁₂ (D - E) = ptrace₁₂ D - ptrace₁₂ E := ptrace₁₂LinearMap.map_sub D E
  have h2 : ptrace₁₃ (D - E) = ptrace₁₃ D - ptrace₁₃ E := ptrace₁₃LinearMap.map_sub D E
  have h3 : ptrace₂₃ (D - E) = ptrace₂₃ D - ptrace₂₃ E := ptrace₂₃LinearMap.map_sub D E
  unfold invB jointShadowCrossB
  rw [h1, h2, h3, frobSq_sub, frobSq_sub, frobSq_sub]
  ring

/-- The full shadow polynomial of D−E retains all original cross contractions. -/
theorem jointShadowS3_sub (D E : Matrix (a × b × c) (a × b × c) ℂ) :
    jointShadowS3 (D - E) =
      invN D + invN E - 2 * (hsInner D E).re -
      (invA D + invA E - 2 * jointShadowCrossA D E) +
      (invB D + invB E - 2 * jointShadowCrossB D E) := by
  rw [jointShadowS3, jointShadow_invA_sub, jointShadow_invB_sub]
  simp only [invN, frobSq_sub]

variable {l : Type*} [Fintype l]

/-- The sixteen literal swap terms, now bound to all existing physical invariants. -/
theorem jointShadowProjection_physical_identity
    (X Y : Matrix (a × b × c) l ℂ) :
    16 * vecNormSq (jointShadowProjection (jointShadowSourceTensor X Y)) =
      frobSq X * frobSq Y + invN (X * Yᴴ) - invA (X * Yᴴ) +
      invB (X * Yᴴ) - invT (X * Yᴴ) - (hsInner (X * Xᴴ) (Y * Yᴴ)).re +
      jointShadowCrossA (X * Xᴴ) (Y * Yᴴ) - jointShadowCrossB (X * Xᴴ) (Y * Yᴴ) := by
  rw [jointShadowProjection_sixteen_terms,
    jointShadowMoment_empty, jointShadowMoment_full,
    jointShadowMoment_A, jointShadowMoment_B, jointShadowMoment_C,
    jointShadowMoment_AB, jointShadowMoment_AC, jointShadowMoment_BC,
    jointShadowMoment_ABC, jointShadowMoment_L, jointShadowMoment_LA,
    jointShadowMoment_LB, jointShadowMoment_LC, jointShadowMoment_LAB,
    jointShadowMoment_LAC, jointShadowMoment_LBC,
    jointShadowSource_norm, jointShadowSource_norm, jointShadowSource_trace]
  unfold invN invA invB invT jointShadowCrossA jointShadowCrossB
  ring

/-- Exact Frobenius cross norm expressed in the two original logical Grams. -/
theorem jointShadow_frobSq_cross_gram
    {m n : Type*} [Fintype m] [Fintype n]
    (X Y : Matrix m n ℂ) :
    (frobSq (X * Yᴴ) : ℂ) = ((Xᴴ * X) * (Yᴴ * Y)).trace := by
  rw [ofReal_frobSq_eq_trace, Matrix.conjTranspose_mul,
    Matrix.conjTranspose_conjTranspose]
  calc
    ((Y * Xᴴ) * (X * Yᴴ)).trace = (Y * ((Xᴴ * X) * Yᴴ)).trace := by
      simp only [Matrix.mul_assoc]
    _ = (((Xᴴ * X) * Yᴴ) * Y).trace := Matrix.trace_mul_comm _ _
    _ = ((Xᴴ * X) * (Yᴴ * Y)).trace := by rw [Matrix.mul_assoc]

/-- Equal logical Grams give both exact endpoint/cross Frobenius equalities. -/
theorem jointShadow_balanced_norms
    {m n : Type*} [Fintype m] [Fintype n]
    (X Y : Matrix m n ℂ) (h : Xᴴ * X = Yᴴ * Y) :
    frobSq (X * Xᴴ) = frobSq (X * Yᴴ) ∧
      frobSq (Y * Yᴴ) = frobSq (X * Yᴴ) ∧ frobSq X = frobSq Y := by
  constructor
  · apply Complex.ofReal_injective
    rw [jointShadow_frobSq_cross_gram, jointShadow_frobSq_cross_gram, h]
  constructor
  · apply Complex.ofReal_injective
    rw [jointShadow_frobSq_cross_gram, jointShadow_frobSq_cross_gram, h]
  · apply Complex.ofReal_injective
    rw [ofReal_frobSq_eq_trace, ofReal_frobSq_eq_trace, h]

/-- Each positive source trace is the real squared norm of its actual purification. -/
theorem jointShadow_trace_source {m n : Type*} [Fintype m] [Fintype n]
    (X : Matrix m n ℂ) : (X * Xᴴ).trace = (frobSq X : ℂ) := by
  rw [Matrix.trace_mul_comm, ← ofReal_frobSq_eq_trace]

end ThreeCopyQutritWerner
