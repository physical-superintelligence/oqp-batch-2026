module

public import ThreeCopyQutritWerner.CertificateX2InputSorted

@[expose] public section


/-!
# Input stage: normal form of the key sums for Gram-plus-correction sources

For sources of the form `N k = A k (A k)ᵀ + K k C k (K k)ᵀ` (the corrected sources: `A = F / 2^80` with the
trial factor `F`, `K C Kᵀ` the exact correction on the 8 corrected keys and `0` elsewhere), the input-block
lookups are finite sums of products of entries of `V = GJ A` and `U = GJ K` (plus the partner terms for
S3 degree 2). With `x2EmbedS_sorted_concrete` / `x2EmbedA_sorted_concrete` this writes the input-stage
values on type-sorted label triples through `V` and `U` only: what remains for hT0 is the computation
(packed run checks of these sums against the input tables).
-/

open scoped BigOperators Matrix

namespace ThreeCopyQutritWerner
namespace X2

theorem x2Lookup_add {p q r : ℕ} (M₁ M₂ : Matrix (Fin p × Fin q × Fin r) (Fin p × Fin q × Fin r) ℚ)
    (a b : Fin 3 → ℕ) : x2Lookup (M₁ + M₂) a b = x2Lookup M₁ a b + x2Lookup M₂ a b := by
  unfold x2Lookup
  split_ifs
  · rw [Matrix.add_apply]
  · ring

theorem x2Lookup_smul {p q r : ℕ} (M : Matrix (Fin p × Fin q × Fin r) (Fin p × Fin q × Fin r) ℚ) (t : ℚ)
    (a b : Fin 3 → ℕ) : x2Lookup (t • M) a b = t * x2Lookup M a b := by
  unfold x2Lookup
  split_ifs
  · rw [Matrix.smul_apply, smul_eq_mul]
  · ring

theorem x2Lookup_zero {p q r : ℕ} (a b : Fin 3 → ℕ) :
    x2Lookup (0 : Matrix (Fin p × Fin q × Fin r) (Fin p × Fin q × Fin r) ℚ) a b = 0 := by
  unfold x2Lookup
  split_ifs <;> rfl

/-- Gram part of a lookup: `∑_c V(a, c) V(b, c) + ∑_{c, c'} U(a, c) C(c, c') U(b, c')`. -/
noncomputable def x2GramPart {p q r n m : ℕ} (V : Matrix (Fin p × Fin q × Fin r) (Fin n) ℚ)
    (U : Matrix (Fin p × Fin q × Fin r) (Fin m) ℚ) (C : Matrix (Fin m) (Fin m) ℚ) (a b : Fin 3 → ℕ) : ℚ :=
  ∑ c, x2Get3 V (a 0) (a 1) (a 2) c * x2Get3 V (b 0) (b 1) (b 2) c +
    ∑ c, ∑ c', x2Get3 U (a 0) (a 1) (a 2) c * C c c' * x2Get3 U (b 0) (b 1) (b 2) c'

/-- The input-block lookup of a Gram-plus-correction source block, through `V = GJ A`, `U = GJ K`. -/
theorem x2Lookup_inputBlock_gram (D : X2Data) (s : Fin 3) (N : X2Blocks s) (k : x2Key s) {n m : ℕ}
    (A : Matrix (x2Col s k) (Fin n) ℚ) (K : Matrix (x2Col s k) (Fin m) ℚ) (C : Matrix (Fin m) (Fin m) ℚ)
    (hN : N k = A * Aᵀ + K * C * Kᵀ) (a b : Fin 3 → ℕ) :
    x2Lookup (x2InputBlock D s N k) a b =
      x2GramPart (x2GJ D s k * A) (x2GJ D s k * K) C a b +
        if x2KeyDegree s k = 2 then
          (1 / 3 : ℚ) * x2GramPart (x2Partner (x2GJ D s k * A)) (x2Partner (x2GJ D s k * K)) C a b
        else 0 := by
  rw [x2InputBlock_eq D s N k A K C hN, x2Lookup_add, x2Lookup_gram]
  unfold x2GramPart
  split_ifs
  · rw [x2Lookup_smul, x2Lookup_gram]
  · rw [x2Lookup_zero]

/-- The key sum of a sector for Gram-plus-correction sources. -/
theorem x2KeySum_gram (s : Fin 3) (N : X2Blocks s) (n m : x2Key s → ℕ)
    (A : ∀ k, Matrix (x2Col s k) (Fin (n k)) ℚ) (K : ∀ k, Matrix (x2Col s k) (Fin (m k)) ℚ)
    (C : ∀ k, Matrix (Fin (m k)) (Fin (m k)) ℚ) (hN : ∀ k, N k = A k * (A k)ᵀ + K k * C k * (K k)ᵀ)
    (t : Fin 3 → Fin 8) (a b : Fin 3 → ℕ) :
    x2KeySum s N t a b =
      ∑ k : x2Key s, if x2KeyTypes s k = t then
        x2GramPart (x2GJ x2DataConcrete s k * A k) (x2GJ x2DataConcrete s k * K k) (C k) a b +
          (if x2KeyDegree s k = 2 then (1 / 3 : ℚ) * x2GramPart (x2Partner (x2GJ x2DataConcrete s k * A k))
            (x2Partner (x2GJ x2DataConcrete s k * K k)) (C k) a b else 0)
      else 0 := by
  unfold x2KeySum
  refine Finset.sum_congr rfl (fun k _ => ?_)
  by_cases h : x2KeyTypes s k = t
  · simp only [if_pos h]
    exact x2Lookup_inputBlock_gram x2DataConcrete s N k (A k) (K k) (C k) (hN k) a b
  · simp only [if_neg h]

end X2
end ThreeCopyQutritWerner
