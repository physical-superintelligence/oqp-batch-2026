module

public import CausalNonpurifiability.Definitions.SeparationCore
public import CausalNonpurifiability.Purification.Heisenberg

@[expose] public section


/-!
# `CausalNonpurifiability.Purification.Separation`

Steps 4–7 of the proof of Theorem 6.1 (manuscript Appendix A, `app:purcs`), in the two-part form
of `Purification/Sector.lean`.

Input: the Heisenberg-picture map `Φ† = heis U` of a unitary `U` (rows: future × inputs
`(A_I, B_I)`; columns: past × outputs `(A_O, B_O)`), the two statements of `eq:no-self`
(`Φ†(X ⊗ 1)` acts as the identity on `A_O`, `Φ†(1 ⊗ Y)` acts as the identity on `B_O`) and
`eq:LV-c` for `Φ†(Q)`, together with a family `Wf u v` of operators (the processes `W_τ` for
`τ = |u⟩⟨v|`) whose entries are matrix elements of `Φ†`.

* Step 4 — `Separation.sliceA`, `Separation.sliceB`: the operators `a X t' t`, `b Y o' o` on the
  global past with `Φ†(X ⊗ 1) = a X ⊗ 1_{A_O}` and `Φ†(1 ⊗ Y) = b Y ⊗ 1_{B_O}`
  (`heis_kronecker_one_apply`, `heis_one_kronecker_apply`). Multiplicativity of `Φ†` gives
  `Φ†(X ⊗ Y) = a X · b Y = b Y · a X` (`heis_kronecker_apply`, `heis_kronecker_apply'`,
  `sliceA_mul_sliceB_comm`).
* Steps 5–6 — `Separation.devA`, `Separation.devB`: the parts of `a X`, `b Y` that depend on the
  other party's output. `eq:LV-c` is the product relation `devA * devB = 0` (`devA_mul_devB`,
  `devB_mul_devA`).
* Step 7 — `Separation.exists_split` applies `exists_sector_split`: the vector of the global past
  is a sum `v₁ + v₂` of two orthogonal parts; `Wf v₁ v₁` does not depend on Bob's output
  (`R_BO_wf`), `Wf v₂ v₂` does not depend on Alice's output (`R_AO_wf`), and the cross terms
  vanish (`wf_eq_zero_of_cross`).

**Proof route** (the statement proved is the one needed for Theorem 6.1): the manuscript splits
the global past into sectors `L_k ⊗ R_k` with the structure theorem for finite-dimensional
`*`-algebras (`eq:algebra-split`); here the two parts of `Purification/Sector.lean` are used.

The auxiliary statements are generic in the finite index types; the endpoint
`causallySeparable_of_heis_structure` is their `Fin`-coordinate form.
-/

set_option autoImplicit false
-- Generic-index lemmas carry the uniform `[Fintype _] [DecidableEq _]` assumptions of the section.
set_option linter.unusedSectionVars false

open Matrix
open scoped ComplexOrder Kronecker

namespace CausalNonpurifiability

noncomputable section

namespace Separation

variable {F A B P O T : Type} [Fintype F] [Fintype A] [Fintype B] [Fintype P] [Fintype O]
  [Fintype T] [DecidableEq F] [DecidableEq A] [DecidableEq B] [DecidableEq P] [DecidableEq O]
  [DecidableEq T]

/-! ### Hypotheses and definitions -/

variable (U : Matrix (F × (A × B)) (P × (O × T)) ℂ)

theorem sliceA_apply (o₀ : O) (X : Op A) (t' t : T) (x' x : P) :
    sliceA U o₀ X t' t x' x = heis U (X ⊗ₖ (1 : Op B)) (x', (o₀, t')) (x, (o₀, t)) := rfl

theorem sliceB_apply (t₀ : T) (Y : Op B) (o' o : O) (x' x : P) :
    sliceB U t₀ Y o' o x' x = heis U ((1 : Op A) ⊗ₖ Y) (x', (o', t₀)) (x, (o, t₀)) := rfl

theorem meanA_eq (o₀ : O) (X : Op A) :
    meanA U o₀ X = invCard T • ∑ t : T, sliceA U o₀ X t t := rfl

theorem meanB_eq (t₀ : T) (Y : Op B) :
    meanB U t₀ Y = invCard O • ∑ o : O, sliceB U t₀ Y o o := rfl

theorem devA_eq (o₀ : O) (X : Op A) (t' t : T) :
    devA U o₀ X t' t = sliceA U o₀ X t' t - (if t = t' then meanA U o₀ X else 0) := rfl

theorem devB_eq (t₀ : T) (Y : Op B) (o' o : O) :
    devB U t₀ Y o' o = sliceB U t₀ Y o' o - (if o = o' then meanB U t₀ Y else 0) := rfl

/-! ### Step 4: slices and products -/

/-- `Φ†(X ⊗ 1) = a X ⊗ 1_{A_O}`. -/
theorem heis_kronecker_one_apply (hS1 : NoSelfA U) (o₀ : O) (X : Op A) (x' x : P) (o' o : O)
    (t' t : T) :
    heis U (X ⊗ₖ (1 : Op B)) (x', (o', t')) (x, (o, t)) =
      if o = o' then sliceA U o₀ X t' t x' x else 0 := by
  have h0 := hS1 X x' x o₀ o₀ t' t
  rw [if_pos rfl] at h0
  rw [hS1 X x' x o' o t' t, sliceA_apply, h0]

/-- `Φ†(1 ⊗ Y) = b Y ⊗ 1_{B_O}`. -/
theorem heis_one_kronecker_apply (hS2 : NoSelfB U) (t₀ : T) (Y : Op B) (x' x : P) (o' o : O)
    (t' t : T) :
    heis U ((1 : Op A) ⊗ₖ Y) (x', (o', t')) (x, (o, t)) =
      if t = t' then sliceB U t₀ Y o' o x' x else 0 := by
  have h0 := hS2 Y x' x o' o t₀ t₀
  rw [if_pos rfl] at h0
  rw [hS2 Y x' x o' o t' t, sliceB_apply, h0]

/-- `Φ†(X ⊗ Y) = Φ†(X ⊗ 1) Φ†(1 ⊗ Y)`, entrywise: the slices multiply. -/
theorem heis_kronecker_apply (hU2 : U * Uᴴ = 1) (hS1 : NoSelfA U) (hS2 : NoSelfB U) (o₀ : O)
    (t₀ : T) (X : Op A) (Y : Op B) (x' x : P) (o' o : O) (t' t : T) :
    heis U (X ⊗ₖ Y) (x', (o', t')) (x, (o, t)) =
      (sliceA U o₀ X t' t * sliceB U t₀ Y o' o) x' x := by
  have hA := heis_kronecker_one_apply U hS1 o₀
  have hB := heis_one_kronecker_apply U hS2 t₀
  have hk : X ⊗ₖ Y = (X ⊗ₖ (1 : Op B)) * ((1 : Op A) ⊗ₖ Y) := by
    rw [← Matrix.mul_kronecker_mul, Matrix.mul_one, Matrix.one_mul]
  rw [hk, heis_mul U hU2, Matrix.mul_apply, Matrix.mul_apply, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun x'' _ => ?_
  rw [Fintype.sum_prod_type, Fintype.sum_eq_single o']
  · rw [Fintype.sum_eq_single t]
    · rw [hA X x' x'' o' o' t' t, hB Y x'' x o' o t t, if_pos rfl, if_pos rfl]
    · intro t'' ht''
      rw [hB Y x'' x o' o t'' t, if_neg (Ne.symm ht''), mul_zero]
  · intro o'' ho''
    refine Finset.sum_eq_zero fun t'' _ => ?_
    rw [hA X x' x'' o' o'' t' t'', if_neg ho'', zero_mul]

/-- `Φ†(X ⊗ Y) = Φ†(1 ⊗ Y) Φ†(X ⊗ 1)`, entrywise: the slices multiply in the other order. -/
theorem heis_kronecker_apply' (hU2 : U * Uᴴ = 1) (hS1 : NoSelfA U) (hS2 : NoSelfB U) (o₀ : O)
    (t₀ : T) (X : Op A) (Y : Op B) (x' x : P) (o' o : O) (t' t : T) :
    heis U (X ⊗ₖ Y) (x', (o', t')) (x, (o, t)) =
      (sliceB U t₀ Y o' o * sliceA U o₀ X t' t) x' x := by
  have hA := heis_kronecker_one_apply U hS1 o₀
  have hB := heis_one_kronecker_apply U hS2 t₀
  have hk : X ⊗ₖ Y = ((1 : Op A) ⊗ₖ Y) * (X ⊗ₖ (1 : Op B)) := by
    rw [← Matrix.mul_kronecker_mul, Matrix.mul_one, Matrix.one_mul]
  rw [hk, heis_mul U hU2, Matrix.mul_apply, Matrix.mul_apply, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun x'' _ => ?_
  rw [Fintype.sum_prod_type, Fintype.sum_eq_single o]
  · rw [Fintype.sum_eq_single t']
    · rw [hB Y x' x'' o' o t' t', hA X x'' x o o t' t, if_pos rfl, if_pos rfl]
    · intro t'' ht''
      rw [hB Y x' x'' o' o t' t'', if_neg ht'', zero_mul]
  · intro o'' ho''
    refine Finset.sum_eq_zero fun t'' _ => ?_
    rw [hA X x'' x o'' o t'' t, if_neg (Ne.symm ho''), mul_zero]

/-- Alice's slices commute with Bob's slices. -/
theorem sliceA_mul_sliceB_comm (hU2 : U * Uᴴ = 1) (hS1 : NoSelfA U) (hS2 : NoSelfB U) (o₀ : O)
    (t₀ : T) (X : Op A) (Y : Op B) (t' t : T) (o' o : O) :
    sliceA U o₀ X t' t * sliceB U t₀ Y o' o = sliceB U t₀ Y o' o * sliceA U o₀ X t' t := by
  ext x' x
  exact (heis_kronecker_apply U hU2 hS1 hS2 o₀ t₀ X Y x' x o' o t' t).symm.trans
    (heis_kronecker_apply' U hU2 hS1 hS2 o₀ t₀ X Y x' x o' o t' t)

/-! ### Products with the means, as entries of `Φ†(X ⊗ Y)` -/

theorem sliceA_mul_meanB_apply (hU2 : U * Uᴴ = 1) (hS1 : NoSelfA U) (hS2 : NoSelfB U) (o₀ : O)
    (t₀ : T) (X : Op A) (Y : Op B) (x' x : P) (t' t : T) :
    (sliceA U o₀ X t' t * meanB U t₀ Y) x' x =
      invCard O * ∑ o'', heis U (X ⊗ₖ Y) (x', (o'', t')) (x, (o'', t)) := by
  have hs : ∑ o'' : O, (sliceA U o₀ X t' t * sliceB U t₀ Y o'' o'') x' x =
      ∑ o'' : O, heis U (X ⊗ₖ Y) (x', (o'', t')) (x, (o'', t)) :=
    Finset.sum_congr rfl fun o'' _ =>
      (heis_kronecker_apply U hU2 hS1 hS2 o₀ t₀ X Y x' x o'' o'' t' t).symm
  rw [meanB_eq, Matrix.mul_smul, Matrix.mul_sum, Matrix.smul_apply, Matrix.sum_apply,
    smul_eq_mul, hs]

theorem meanA_mul_sliceB_apply (hU2 : U * Uᴴ = 1) (hS1 : NoSelfA U) (hS2 : NoSelfB U) (o₀ : O)
    (t₀ : T) (X : Op A) (Y : Op B) (x' x : P) (o' o : O) :
    (meanA U o₀ X * sliceB U t₀ Y o' o) x' x =
      invCard T * ∑ t'', heis U (X ⊗ₖ Y) (x', (o', t'')) (x, (o, t'')) := by
  have hs : ∑ t'' : T, (sliceA U o₀ X t'' t'' * sliceB U t₀ Y o' o) x' x =
      ∑ t'' : T, heis U (X ⊗ₖ Y) (x', (o', t'')) (x, (o, t'')) :=
    Finset.sum_congr rfl fun t'' _ =>
      (heis_kronecker_apply U hU2 hS1 hS2 o₀ t₀ X Y x' x o' o t'' t'').symm
  rw [meanA_eq, Matrix.smul_mul, Matrix.sum_mul, Matrix.smul_apply, Matrix.sum_apply,
    smul_eq_mul, hs]

theorem meanA_mul_meanB_apply (hU2 : U * Uᴴ = 1) (hS1 : NoSelfA U) (hS2 : NoSelfB U) (o₀ : O)
    (t₀ : T) (X : Op A) (Y : Op B) (x' x : P) :
    (meanA U o₀ X * meanB U t₀ Y) x' x =
      invCard O * ∑ o'', invCard T *
        ∑ t'', heis U (X ⊗ₖ Y) (x', (o'', t'')) (x, (o'', t'')) := by
  have hs : ∑ o'' : O, (meanA U o₀ X * sliceB U t₀ Y o'' o'') x' x =
      ∑ o'' : O, invCard T * ∑ t'' : T, heis U (X ⊗ₖ Y) (x', (o'', t'')) (x, (o'', t'')) :=
    Finset.sum_congr rfl fun o'' _ =>
      meanA_mul_sliceB_apply U hU2 hS1 hS2 o₀ t₀ X Y x' x o'' o''
  rw [meanB_eq, Matrix.mul_smul, Matrix.mul_sum, Matrix.smul_apply, Matrix.sum_apply,
    smul_eq_mul, hs]

/-! ### Commutation relations of the means and deviations -/

theorem meanA_mul_sliceB_comm (hU2 : U * Uᴴ = 1) (hS1 : NoSelfA U) (hS2 : NoSelfB U) (o₀ : O)
    (t₀ : T) (X : Op A) (Y : Op B) (o' o : O) :
    meanA U o₀ X * sliceB U t₀ Y o' o = sliceB U t₀ Y o' o * meanA U o₀ X := by
  have hs : ∑ t'' : T, sliceA U o₀ X t'' t'' * sliceB U t₀ Y o' o =
      ∑ t'' : T, sliceB U t₀ Y o' o * sliceA U o₀ X t'' t'' :=
    Finset.sum_congr rfl fun t'' _ =>
      sliceA_mul_sliceB_comm U hU2 hS1 hS2 o₀ t₀ X Y t'' t'' o' o
  rw [meanA_eq, Matrix.smul_mul, Matrix.mul_smul, Matrix.sum_mul, Matrix.mul_sum, hs]

theorem sliceA_mul_meanB_comm (hU2 : U * Uᴴ = 1) (hS1 : NoSelfA U) (hS2 : NoSelfB U) (o₀ : O)
    (t₀ : T) (X : Op A) (Y : Op B) (t' t : T) :
    sliceA U o₀ X t' t * meanB U t₀ Y = meanB U t₀ Y * sliceA U o₀ X t' t := by
  have hs : ∑ o'' : O, sliceA U o₀ X t' t * sliceB U t₀ Y o'' o'' =
      ∑ o'' : O, sliceB U t₀ Y o'' o'' * sliceA U o₀ X t' t :=
    Finset.sum_congr rfl fun o'' _ =>
      sliceA_mul_sliceB_comm U hU2 hS1 hS2 o₀ t₀ X Y t' t o'' o''
  rw [meanB_eq, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_sum, Matrix.sum_mul, hs]

/-- Alice's deviations commute with Bob's slices. -/
theorem devA_mul_sliceB_comm (hU2 : U * Uᴴ = 1) (hS1 : NoSelfA U) (hS2 : NoSelfB U) (o₀ : O)
    (t₀ : T) (X : Op A) (Y : Op B) (t' t : T) (o' o : O) :
    devA U o₀ X t' t * sliceB U t₀ Y o' o = sliceB U t₀ Y o' o * devA U o₀ X t' t := by
  rw [devA_eq U o₀ X t' t, Matrix.sub_mul, Matrix.mul_sub,
    sliceA_mul_sliceB_comm U hU2 hS1 hS2 o₀ t₀ X Y t' t o' o]
  by_cases ht : t = t'
  · rw [if_pos ht, meanA_mul_sliceB_comm U hU2 hS1 hS2 o₀ t₀ X Y o' o]
  · rw [if_neg ht, Matrix.zero_mul, Matrix.mul_zero]

/-- Alice's slices commute with Bob's deviations. -/
theorem sliceA_mul_devB_comm (hU2 : U * Uᴴ = 1) (hS1 : NoSelfA U) (hS2 : NoSelfB U) (o₀ : O)
    (t₀ : T) (X : Op A) (Y : Op B) (t' t : T) (o' o : O) :
    sliceA U o₀ X t' t * devB U t₀ Y o' o = devB U t₀ Y o' o * sliceA U o₀ X t' t := by
  rw [devB_eq U t₀ Y o' o, Matrix.mul_sub, Matrix.sub_mul,
    sliceA_mul_sliceB_comm U hU2 hS1 hS2 o₀ t₀ X Y t' t o' o]
  by_cases ho : o = o'
  · rw [if_pos ho, sliceA_mul_meanB_comm U hU2 hS1 hS2 o₀ t₀ X Y t' t]
  · rw [if_neg ho, Matrix.mul_zero, Matrix.zero_mul]

theorem devA_mul_meanB_comm (hU2 : U * Uᴴ = 1) (hS1 : NoSelfA U) (hS2 : NoSelfB U) (o₀ : O)
    (t₀ : T) (X : Op A) (Y : Op B) (t' t : T) :
    devA U o₀ X t' t * meanB U t₀ Y = meanB U t₀ Y * devA U o₀ X t' t := by
  have hs : ∑ o'' : O, devA U o₀ X t' t * sliceB U t₀ Y o'' o'' =
      ∑ o'' : O, sliceB U t₀ Y o'' o'' * devA U o₀ X t' t :=
    Finset.sum_congr rfl fun o'' _ =>
      devA_mul_sliceB_comm U hU2 hS1 hS2 o₀ t₀ X Y t' t o'' o''
  rw [meanB_eq, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_sum, Matrix.sum_mul, hs]

/-- The deviations of the two parties commute. -/
theorem devB_mul_devA_comm (hU2 : U * Uᴴ = 1) (hS1 : NoSelfA U) (hS2 : NoSelfB U) (o₀ : O)
    (t₀ : T) (X : Op A) (Y : Op B) (t' t : T) (o' o : O) :
    devB U t₀ Y o' o * devA U o₀ X t' t = devA U o₀ X t' t * devB U t₀ Y o' o := by
  rw [devB_eq U t₀ Y o' o, Matrix.sub_mul, Matrix.mul_sub,
    devA_mul_sliceB_comm U hU2 hS1 hS2 o₀ t₀ X Y t' t o' o]
  by_cases ho : o = o'
  · rw [if_pos ho, devA_mul_meanB_comm U hU2 hS1 hS2 o₀ t₀ X Y t' t]
  · rw [if_neg ho, Matrix.zero_mul, Matrix.mul_zero]

/-! ### Steps 5–6: `eq:LV-c` as a product relation -/

/-- **Key identity**: `eq:LV-c` for `Φ†(X ⊗ Y)` says that the product of the two deviations
vanishes. -/
theorem devA_mul_devB (hU2 : U * Uᴴ = 1) (hS1 : NoSelfA U) (hS2 : NoSelfB U) (hC : LVc U)
    (o₀ : O) (t₀ : T) (X : Op A) (Y : Op B) (t' t : T) (o' o : O) :
    devA U o₀ X t' t * devB U t₀ Y o' o = 0 := by
  ext x' x
  have hc := hC (X ⊗ₖ Y) x' x o' o t' t
  have h0 := heis_kronecker_apply U hU2 hS1 hS2 o₀ t₀ X Y x' x o' o t' t
  have h1 := sliceA_mul_meanB_apply U hU2 hS1 hS2 o₀ t₀ X Y x' x t' t
  have h2 := meanA_mul_sliceB_apply U hU2 hS1 hS2 o₀ t₀ X Y x' x o' o
  have h3 := meanA_mul_meanB_apply U hU2 hS1 hS2 o₀ t₀ X Y x' x
  rw [devA_eq U o₀ X t' t, devB_eq U t₀ Y o' o, Matrix.zero_apply]
  by_cases ht : t = t'
  · by_cases ho : o = o'
    · simp only [if_pos ht, if_pos ho] at hc
      simp only [if_pos ht, if_pos ho, sub_zero, Matrix.sub_mul, Matrix.mul_sub,
        Matrix.mul_zero, Matrix.zero_mul, Matrix.sub_apply, Matrix.zero_apply]
      linear_combination hc - h0 - h1 - h2 + h3
    · simp only [if_pos ht, if_neg ho] at hc
      simp only [if_pos ht, if_neg ho, sub_zero, Matrix.sub_mul, Matrix.mul_sub,
        Matrix.mul_zero, Matrix.zero_mul, Matrix.sub_apply, Matrix.zero_apply]
      linear_combination hc - h0 - h2
  · by_cases ho : o = o'
    · simp only [if_neg ht, if_pos ho, Finset.sum_const_zero, mul_zero] at hc
      simp only [if_neg ht, if_pos ho, sub_zero, Matrix.sub_mul, Matrix.mul_sub,
        Matrix.mul_zero, Matrix.zero_mul, Matrix.sub_apply, Matrix.zero_apply]
      linear_combination hc - h0 - h1
    · simp only [if_neg ht, if_neg ho] at hc
      simp only [if_neg ht, if_neg ho, sub_zero, Matrix.sub_mul, Matrix.mul_sub,
        Matrix.mul_zero, Matrix.zero_mul, Matrix.sub_apply, Matrix.zero_apply]
      linear_combination hc - h0

/-- The product of the deviations in the other order vanishes as well. -/
theorem devB_mul_devA (hU2 : U * Uᴴ = 1) (hS1 : NoSelfA U) (hS2 : NoSelfB U) (hC : LVc U)
    (o₀ : O) (t₀ : T) (X : Op A) (Y : Op B) (t' t : T) (o' o : O) :
    devB U t₀ Y o' o * devA U o₀ X t' t = 0 := by
  rw [devB_mul_devA_comm U hU2 hS1 hS2 o₀ t₀ X Y t' t o' o]
  exact devA_mul_devB U hU2 hS1 hS2 hC o₀ t₀ X Y t' t o' o

/-! ### Adjoints -/

theorem sliceA_conjTranspose (o₀ : O) (X : Op A) (t' t : T) :
    (sliceA U o₀ X t' t)ᴴ = sliceA U o₀ Xᴴ t t' := by
  ext x' x
  have h : (heis U (X ⊗ₖ (1 : Op B)))ᴴ = heis U (Xᴴ ⊗ₖ (1 : Op B)) := by
    rw [heis_conjTranspose, Matrix.conjTranspose_kronecker, Matrix.conjTranspose_one]
  have h2 := congrFun (congrFun h (x', (o₀, t))) (x, (o₀, t'))
  rw [Matrix.conjTranspose_apply] at h2
  rw [Matrix.conjTranspose_apply, sliceA_apply, sliceA_apply]
  exact h2

theorem sliceB_conjTranspose (t₀ : T) (Y : Op B) (o' o : O) :
    (sliceB U t₀ Y o' o)ᴴ = sliceB U t₀ Yᴴ o o' := by
  ext x' x
  have h : (heis U ((1 : Op A) ⊗ₖ Y))ᴴ = heis U ((1 : Op A) ⊗ₖ Yᴴ) := by
    rw [heis_conjTranspose, Matrix.conjTranspose_kronecker, Matrix.conjTranspose_one]
  have h2 := congrFun (congrFun h (x', (o, t₀))) (x, (o', t₀))
  rw [Matrix.conjTranspose_apply] at h2
  rw [Matrix.conjTranspose_apply, sliceB_apply, sliceB_apply]
  exact h2

theorem meanA_conjTranspose (o₀ : O) (X : Op A) : (meanA U o₀ X)ᴴ = meanA U o₀ Xᴴ := by
  have hs : ∑ t : T, (sliceA U o₀ X t t)ᴴ = ∑ t : T, sliceA U o₀ Xᴴ t t :=
    Finset.sum_congr rfl fun t _ => sliceA_conjTranspose U o₀ X t t
  rw [meanA_eq U o₀ X, meanA_eq U o₀ Xᴴ, Matrix.conjTranspose_smul, Matrix.conjTranspose_sum,
    star_invCard, hs]

theorem devA_conjTranspose (o₀ : O) (X : Op A) (t' t : T) :
    (devA U o₀ X t' t)ᴴ = devA U o₀ Xᴴ t t' := by
  rw [devA_eq U o₀ X t' t, devA_eq U o₀ Xᴴ t t', Matrix.conjTranspose_sub,
    sliceA_conjTranspose U o₀ X t' t]
  by_cases ht : t = t'
  · rw [if_pos ht, if_pos ht.symm, meanA_conjTranspose U o₀ X]
  · rw [if_neg ht, if_neg (fun h : t' = t => ht h.symm), Matrix.conjTranspose_zero]

/-! ### Step 7: the two parts of the global past -/

/-- The splitting of `Purification/Sector.lean` for the slices: every vector of the global past
is a sum `v₁ + v₂` such that Alice's deviations annihilate `v₁`, Bob's deviations annihilate
`v₂`, and the products of slices have no matrix elements between `v₁` and `v₂`. -/
theorem exists_split (hU2 : U * Uᴴ = 1) (hS1 : NoSelfA U) (hS2 : NoSelfB U) (hC : LVc U)
    (o₀ : O) (t₀ : T) (e₀ : P → ℂ) :
    ∃ v₁ v₂ : P → ℂ, e₀ = v₁ + v₂ ∧
      (∀ (X : Op A) (t' t : T), devA U o₀ X t' t *ᵥ v₁ = 0) ∧
      (∀ (Y : Op B) (o' o : O), devB U t₀ Y o' o *ᵥ v₂ = 0) ∧
      (∀ (X : Op A) (Y : Op B) (t' t : T) (o' o : O),
        star v₁ ⬝ᵥ ((sliceA U o₀ X t' t * sliceB U t₀ Y o' o) *ᵥ v₂) = 0) ∧
      (∀ (X : Op A) (Y : Op B) (t' t : T) (o' o : O),
        star v₂ ⬝ᵥ ((sliceA U o₀ X t' t * sliceB U t₀ Y o' o) *ᵥ v₁) = 0) := by
  obtain ⟨v₁, v₂, hsum, h1, h2, h3, h4⟩ := exists_sector_split
    (fun k : Op A × T × T => sliceA U o₀ k.1 k.2.1 k.2.2)
    (fun k : Op A × T × T => devA U o₀ k.1 k.2.1 k.2.2)
    (fun k : Op B × O × O => sliceB U t₀ k.1 k.2.1 k.2.2)
    (fun k : Op B × O × O => devB U t₀ k.1 k.2.1 k.2.2)
    (fun k => ⟨(k.1ᴴ, k.2.2, k.2.1), sliceA_conjTranspose U o₀ k.1 k.2.1 k.2.2⟩)
    (fun k => ⟨(k.1ᴴ, k.2.2, k.2.1), devA_conjTranspose U o₀ k.1 k.2.1 k.2.2⟩)
    (fun k => ⟨(k.1ᴴ, k.2.2, k.2.1), sliceB_conjTranspose U t₀ k.1 k.2.1 k.2.2⟩)
    (fun i j => sliceA_mul_sliceB_comm U hU2 hS1 hS2 o₀ t₀ i.1 j.1 i.2.1 i.2.2 j.2.1 j.2.2)
    (fun k j => devA_mul_sliceB_comm U hU2 hS1 hS2 o₀ t₀ k.1 j.1 k.2.1 k.2.2 j.2.1 j.2.2)
    (fun i g => sliceA_mul_devB_comm U hU2 hS1 hS2 o₀ t₀ i.1 g.1 i.2.1 i.2.2 g.2.1 g.2.2)
    (fun g k => devB_mul_devA U hU2 hS1 hS2 hC o₀ t₀ k.1 g.1 k.2.1 k.2.2 g.2.1 g.2.2)
    e₀
  exact ⟨v₁, v₂, hsum, fun X t' t => h1 (X, t', t), fun Y o' o => h2 (Y, o', o),
    fun X Y t' t o' o => h3 (X, t', t) (Y, o', o),
    fun X Y t' t o' o => h4 (X, t', t) (Y, o', o)⟩

/-! ### The family `Wf` -/

/-- `⟨v, M u⟩` as a double sum. -/
theorem star_dotProduct_mulVec_eq_sum (M : Op P) (u v : P → ℂ) :
    star v ⬝ᵥ (M *ᵥ u) = ∑ x', ∑ x, star (v x') * M x' x * u x := by
  simp only [dotProduct, Matrix.mulVec, Pi.star_apply, Finset.mul_sum]
  exact Finset.sum_congr rfl fun x' _ => Finset.sum_congr rfl fun x _ => by ring

/-- The entries of `Wf u v` are matrix elements of products of slices. -/
theorem wf_entry (hU2 : U * Uᴴ = 1) (hS1 : NoSelfA U) (hS2 : NoSelfB U) (o₀ : O) (t₀ : T)
    (Wf : (P → ℂ) → (P → ℂ) → Op (LabIdx A O B T)) (E₁ : A → A → Op A) (E₂ : B → B → Op B)
    (hentry : EntryForm U Wf E₁ E₂) (u v : P → ℂ) (i i' : A) (o o' : O) (j j' : B) (t t' : T) :
    Wf u v ((i, o), (j, t)) ((i', o'), (j', t')) =
      star v ⬝ᵥ ((sliceA U o₀ (E₁ i' i) t' t * sliceB U t₀ (E₂ j' j) o' o) *ᵥ u) := by
  rw [hentry u v i i' o o' j j' t t', star_dotProduct_mulVec_eq_sum]
  refine Finset.sum_comm.trans ?_
  refine Finset.sum_congr rfl fun x' _ => Finset.sum_congr rfl fun x _ => ?_
  rw [heis_kronecker_apply U hU2 hS1 hS2 o₀ t₀ (E₁ i' i) (E₂ j' j) x' x o' o t' t]

/-- A member of the family vanishes if the products of slices have no matrix elements between
its two vectors. -/
theorem wf_eq_zero_of_cross (hU2 : U * Uᴴ = 1) (hS1 : NoSelfA U) (hS2 : NoSelfB U) (o₀ : O)
    (t₀ : T) (Wf : (P → ℂ) → (P → ℂ) → Op (LabIdx A O B T)) (E₁ : A → A → Op A)
    (E₂ : B → B → Op B) (hentry : EntryForm U Wf E₁ E₂) (u v : P → ℂ)
    (h : ∀ (X : Op A) (Y : Op B) (t' t : T) (o' o : O),
      star v ⬝ᵥ ((sliceA U o₀ X t' t * sliceB U t₀ Y o' o) *ᵥ u) = 0) :
    Wf u v = 0 := by
  ext ⟨⟨i, o⟩, ⟨j, t⟩⟩ ⟨⟨i', o'⟩, ⟨j', t'⟩⟩
  rw [wf_entry U hU2 hS1 hS2 o₀ t₀ Wf E₁ E₂ hentry u v i i' o o' j j' t t', Matrix.zero_apply]
  exact h (E₁ i' i) (E₂ j' j) t' t o' o

theorem sliceA_mulVec_of_devA (o₀ : O) (X : Op A) (t' t : T) (v : P → ℂ)
    (h : devA U o₀ X t' t *ᵥ v = 0) :
    sliceA U o₀ X t' t *ᵥ v = if t = t' then meanA U o₀ X *ᵥ v else 0 := by
  have hsplit : sliceA U o₀ X t' t =
      devA U o₀ X t' t + (if t = t' then meanA U o₀ X else 0) := by
    rw [devA_eq U o₀ X t' t, sub_add_cancel]
  rw [hsplit, Matrix.add_mulVec, h, zero_add]
  by_cases ht : t = t'
  · rw [if_pos ht, if_pos ht]
  · rw [if_neg ht, if_neg ht, Matrix.zero_mulVec]

theorem sliceB_mulVec_of_devB (t₀ : T) (Y : Op B) (o' o : O) (v : P → ℂ)
    (h : devB U t₀ Y o' o *ᵥ v = 0) :
    sliceB U t₀ Y o' o *ᵥ v = if o = o' then meanB U t₀ Y *ᵥ v else 0 := by
  have hsplit : sliceB U t₀ Y o' o =
      devB U t₀ Y o' o + (if o = o' then meanB U t₀ Y else 0) := by
    rw [devB_eq U t₀ Y o' o, sub_add_cancel]
  rw [hsplit, Matrix.add_mulVec, h, zero_add]
  by_cases ho : o = o'
  · rw [if_pos ho, if_pos ho]
  · rw [if_neg ho, if_neg ho, Matrix.zero_mulVec]

/-- On the part annihilated by Alice's deviations the entries of `Wf` are diagonal and constant
in the index of `B_O`. -/
theorem wf_entry_AB (hU2 : U * Uᴴ = 1) (hS1 : NoSelfA U) (hS2 : NoSelfB U) (o₀ : O) (t₀ : T)
    (Wf : (P → ℂ) → (P → ℂ) → Op (LabIdx A O B T)) (E₁ : A → A → Op A) (E₂ : B → B → Op B)
    (hentry : EntryForm U Wf E₁ E₂) (v₁ : P → ℂ)
    (h1 : ∀ (X : Op A) (t' t : T), devA U o₀ X t' t *ᵥ v₁ = 0)
    (i i' : A) (o o' : O) (j j' : B) (t t' : T) :
    Wf v₁ v₁ ((i, o), (j, t)) ((i', o'), (j', t')) =
      if t = t' then
        star v₁ ⬝ᵥ (sliceB U t₀ (E₂ j' j) o' o *ᵥ (meanA U o₀ (E₁ i' i) *ᵥ v₁))
      else 0 := by
  rw [wf_entry U hU2 hS1 hS2 o₀ t₀ Wf E₁ E₂ hentry v₁ v₁ i i' o o' j j' t t',
    sliceA_mul_sliceB_comm U hU2 hS1 hS2 o₀ t₀ (E₁ i' i) (E₂ j' j) t' t o' o,
    ← Matrix.mulVec_mulVec,
    sliceA_mulVec_of_devA U o₀ (E₁ i' i) t' t v₁ (h1 (E₁ i' i) t' t)]
  by_cases ht : t = t'
  · rw [if_pos ht, if_pos ht]
  · rw [if_neg ht, if_neg ht, Matrix.mulVec_zero, dotProduct_zero]

/-- On the part annihilated by Bob's deviations the entries of `Wf` are diagonal and constant
in the index of `A_O`. -/
theorem wf_entry_BA (hU2 : U * Uᴴ = 1) (hS1 : NoSelfA U) (hS2 : NoSelfB U) (o₀ : O) (t₀ : T)
    (Wf : (P → ℂ) → (P → ℂ) → Op (LabIdx A O B T)) (E₁ : A → A → Op A) (E₂ : B → B → Op B)
    (hentry : EntryForm U Wf E₁ E₂) (v₂ : P → ℂ)
    (h2 : ∀ (Y : Op B) (o' o : O), devB U t₀ Y o' o *ᵥ v₂ = 0)
    (i i' : A) (o o' : O) (j j' : B) (t t' : T) :
    Wf v₂ v₂ ((i, o), (j, t)) ((i', o'), (j', t')) =
      if o = o' then
        star v₂ ⬝ᵥ (sliceA U o₀ (E₁ i' i) t' t *ᵥ (meanB U t₀ (E₂ j' j) *ᵥ v₂))
      else 0 := by
  rw [wf_entry U hU2 hS1 hS2 o₀ t₀ Wf E₁ E₂ hentry v₂ v₂ i i' o o' j j' t t',
    ← Matrix.mulVec_mulVec,
    sliceB_mulVec_of_devB U t₀ (E₂ j' j) o' o v₂ (h2 (E₂ j' j) o' o)]
  by_cases ho : o = o'
  · rw [if_pos ho, if_pos ho]
  · rw [if_neg ho, if_neg ho, Matrix.mulVec_zero, dotProduct_zero]

/-- `Wf v₁ v₁` is invariant under `R_{B_O}`: the first part has the order `A ≺ B`. -/
theorem R_BO_wf (hU2 : U * Uᴴ = 1) (hS1 : NoSelfA U) (hS2 : NoSelfB U) (o₀ : O) (t₀ : T)
    (Wf : (P → ℂ) → (P → ℂ) → Op (LabIdx A O B T)) (E₁ : A → A → Op A) (E₂ : B → B → Op B)
    (hentry : EntryForm U Wf E₁ E₂) (v₁ : P → ℂ)
    (h1 : ∀ (X : Op A) (t' t : T), devA U o₀ X t' t *ᵥ v₁ = 0) :
    R_BO (Wf v₁ v₁) = Wf v₁ v₁ := by
  haveI : Nonempty T := ⟨t₀⟩
  ext ⟨⟨i, o⟩, ⟨j, t⟩⟩ ⟨⟨i', o'⟩, ⟨j', t'⟩⟩
  obtain ⟨c, hc⟩ : ∃ c : ℂ, ∀ s s' : T,
      Wf v₁ v₁ ((i, o), (j, s)) ((i', o'), (j', s')) = if s = s' then c else 0 :=
    ⟨_, wf_entry_AB U hU2 hS1 hS2 o₀ t₀ Wf E₁ E₂ hentry v₁ h1 i i' o o' j j'⟩
  have hsum : ∑ z : T, Wf v₁ v₁ ((i, o), (j, z)) ((i', o'), (j', z)) =
      (Fintype.card T : ℂ) * c := by
    have h' : ∀ z ∈ (Finset.univ : Finset T),
        Wf v₁ v₁ ((i, o), (j, z)) ((i', o'), (j', z)) = c := fun z _ => by
      rw [hc z z, if_pos rfl]
    rw [Finset.sum_congr rfl h']
    simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  have key : R_BO (Wf v₁ v₁) ((i, o), (j, t)) ((i', o'), (j', t')) =
      if t = t' then invCard T * ∑ z, Wf v₁ v₁ ((i, o), (j, z)) ((i', o'), (j', z)) else 0 :=
    R_BO_apply (Wf v₁ v₁) ((i, o), (j, t)) ((i', o'), (j', t'))
  rw [key, hsum, hc t t']
  by_cases ht : t = t'
  · rw [if_pos ht, if_pos ht]
    linear_combination c * invCard_mul_card T
  · rw [if_neg ht, if_neg ht]

/-- `Wf v₂ v₂` is invariant under `R_{A_O}`: the second part has the order `B ≺ A`. -/
theorem R_AO_wf (hU2 : U * Uᴴ = 1) (hS1 : NoSelfA U) (hS2 : NoSelfB U) (o₀ : O) (t₀ : T)
    (Wf : (P → ℂ) → (P → ℂ) → Op (LabIdx A O B T)) (E₁ : A → A → Op A) (E₂ : B → B → Op B)
    (hentry : EntryForm U Wf E₁ E₂) (v₂ : P → ℂ)
    (h2 : ∀ (Y : Op B) (o' o : O), devB U t₀ Y o' o *ᵥ v₂ = 0) :
    R_AO (Wf v₂ v₂) = Wf v₂ v₂ := by
  haveI : Nonempty O := ⟨o₀⟩
  ext ⟨⟨i, o⟩, ⟨j, t⟩⟩ ⟨⟨i', o'⟩, ⟨j', t'⟩⟩
  obtain ⟨c, hc⟩ : ∃ c : ℂ, ∀ s s' : O,
      Wf v₂ v₂ ((i, s), (j, t)) ((i', s'), (j', t')) = if s = s' then c else 0 :=
    ⟨_, fun s s' => wf_entry_BA U hU2 hS1 hS2 o₀ t₀ Wf E₁ E₂ hentry v₂ h2 i i' s s' j j' t t'⟩
  have hsum : ∑ z : O, Wf v₂ v₂ ((i, z), (j, t)) ((i', z), (j', t')) =
      (Fintype.card O : ℂ) * c := by
    have h' : ∀ z ∈ (Finset.univ : Finset O),
        Wf v₂ v₂ ((i, z), (j, t)) ((i', z), (j', t')) = c := fun z _ => by
      rw [hc z z, if_pos rfl]
    rw [Finset.sum_congr rfl h']
    simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  have key : R_AO (Wf v₂ v₂) ((i, o), (j, t)) ((i', o'), (j', t')) =
      if o = o' then invCard O * ∑ z, Wf v₂ v₂ ((i, z), (j, t)) ((i', z), (j', t')) else 0 :=
    R_AO_apply (Wf v₂ v₂) ((i, o), (j, t)) ((i', o'), (j', t'))
  rw [key, hsum, hc o o']
  by_cases ho : o = o'
  · rw [if_pos ho, if_pos ho]
    linear_combination c * invCard_mul_card O
  · rw [if_neg ho, if_neg ho]

/-- Steps 4–7 for generic finite index types: the member `Wf e₀ e₀` of the family is the sum of
a member invariant under `R_{B_O}` and a member invariant under `R_{A_O}`. -/
theorem exists_ordered_split (hU2 : U * Uᴴ = 1) (hS1 : NoSelfA U) (hS2 : NoSelfB U)
    (hC : LVc U) (o₀ : O) (t₀ : T) (Wf : (P → ℂ) → (P → ℂ) → Op (LabIdx A O B T))
    (E₁ : A → A → Op A) (E₂ : B → B → Op B) (hentry : EntryForm U Wf E₁ E₂)
    (hadd : ∀ u₁ u₂ v₁ v₂ : P → ℂ,
      Wf (u₁ + u₂) (v₁ + v₂) = Wf u₁ v₁ + Wf u₁ v₂ + Wf u₂ v₁ + Wf u₂ v₂)
    (e₀ : P → ℂ) :
    ∃ v₁ v₂ : P → ℂ, Wf e₀ e₀ = Wf v₁ v₁ + Wf v₂ v₂ ∧ R_BO (Wf v₁ v₁) = Wf v₁ v₁ ∧
      R_AO (Wf v₂ v₂) = Wf v₂ v₂ := by
  obtain ⟨v₁, v₂, hsum, h1, h2, h3, h4⟩ := exists_split U hU2 hS1 hS2 hC o₀ t₀ e₀
  have h12 : Wf v₁ v₂ = 0 :=
    wf_eq_zero_of_cross U hU2 hS1 hS2 o₀ t₀ Wf E₁ E₂ hentry v₁ v₂ h4
  have h21 : Wf v₂ v₁ = 0 :=
    wf_eq_zero_of_cross U hU2 hS1 hS2 o₀ t₀ Wf E₁ E₂ hentry v₂ v₁ h3
  refine ⟨v₁, v₂, ?_, R_BO_wf U hU2 hS1 hS2 o₀ t₀ Wf E₁ E₂ hentry v₁ h1,
    R_AO_wf U hU2 hS1 hS2 o₀ t₀ Wf E₁ E₂ hentry v₂ h2⟩
  rw [hsum, hadd v₁ v₂ v₁ v₂, h12, h21, add_zero, add_zero]

end Separation

/-- **Steps 4–7 of the proof of Theorem 6.1** (Appendix A). Let `Φ† = heis U` for a matrix `U`
with `U Uᴴ = 1`, and assume `eq:no-self` for both parties (`hS1`, `hS2`) and `eq:LV-c` (`hC`) for
`Φ†`. Let `Wf u v` be a family of operators whose entries are matrix elements of `Φ†` (`hentry`),
which is additive in both vectors (`hadd`) and whose diagonal members are positive and satisfy
`eq:LV`. Then every valid diagonal member `Wf e₀ e₀` is causally separable. -/
theorem causallySeparable_of_heis_structure {D : Ports} {p f : ℕ}
    (U : Matrix (Fin (f + 1) × (Fin D.m × Fin D.n)) (Fin (p + 1) × (Fin D.d × Fin D.e)) ℂ)
    (hU2 : U * Uᴴ = 1)
    (Wf : (Fin (p + 1) → ℂ) → (Fin (p + 1) → ℂ) → PMat D)
    (E₁ : Fin D.m → Fin D.m → Op (Fin D.m)) (E₂ : Fin D.n → Fin D.n → Op (Fin D.n))
    (hS1 : ∀ (X : Op (Fin D.m)) (x' x : Fin (p + 1)) (o' o : Fin D.d) (t' t : Fin D.e),
      heis U (X ⊗ₖ (1 : Op (Fin D.n))) (x', (o', t')) (x, (o, t)) =
        if o = o' then invCard (Fin D.d) *
          ∑ o'', heis U (X ⊗ₖ (1 : Op (Fin D.n))) (x', (o'', t')) (x, (o'', t)) else 0)
    (hS2 : ∀ (Y : Op (Fin D.n)) (x' x : Fin (p + 1)) (o' o : Fin D.d) (t' t : Fin D.e),
      heis U ((1 : Op (Fin D.m)) ⊗ₖ Y) (x', (o', t')) (x, (o, t)) =
        if t = t' then invCard (Fin D.e) *
          ∑ t'', heis U ((1 : Op (Fin D.m)) ⊗ₖ Y) (x', (o', t'')) (x, (o, t'')) else 0)
    (hC : ∀ (Q : Op (Fin D.m × Fin D.n)) (x' x : Fin (p + 1)) (o' o : Fin D.d) (t' t : Fin D.e),
      heis U Q (x', (o', t')) (x, (o, t))
        - (if o = o' then invCard (Fin D.d) * ∑ o'', heis U Q (x', (o'', t')) (x, (o'', t)) else 0)
        - (if t = t' then invCard (Fin D.e) * ∑ t'', heis U Q (x', (o', t'')) (x, (o, t'')) else 0)
        + (if o = o' then invCard (Fin D.d) * ∑ o'', (if t = t' then invCard (Fin D.e) *
              ∑ t'', heis U Q (x', (o'', t'')) (x, (o'', t'')) else 0) else 0) = 0)
    (hentry : ∀ (u v : Fin (p + 1) → ℂ) (i i' : Fin D.m) (o o' : Fin D.d) (j j' : Fin D.n)
        (t t' : Fin D.e),
      Wf u v ((i, o), (j, t)) ((i', o'), (j', t')) =
        ∑ x, ∑ x', star (v x') *
          heis U (E₁ i' i ⊗ₖ E₂ j' j) (x', (o', t')) (x, (o, t)) * u x)
    (hLV : ∀ v, LVEquations (Wf v v))
    (hpsd : ∀ v, (Wf v v).PosSemidef)
    (hadd : ∀ u₁ u₂ v₁ v₂, Wf (u₁ + u₂) (v₁ + v₂) = Wf u₁ v₁ + Wf u₁ v₂ + Wf u₂ v₁ + Wf u₂ v₂)
    (e₀ : Fin (p + 1) → ℂ) (hW : Valid D (Wf e₀ e₀)) :
    CausallySeparable D (Wf e₀ e₀) := by
  obtain ⟨v₁, v₂, hsum, hAB, hBA⟩ :=
    Separation.exists_ordered_split U hU2 hS1 hS2 hC (⟨0, D.d_pos⟩ : Fin D.d)
      (⟨0, D.e_pos⟩ : Fin D.e) Wf E₁ E₂ hentry hadd e₀
  have hLV1 : InLV D (Wf v₁ v₁) :=
    (genLV_iff_lvEquations (Wf v₁ v₁)).mpr ⟨(hpsd v₁).1, hLV v₁⟩
  have hLV2 : InLV D (Wf v₂ v₂) :=
    (genLV_iff_lvEquations (Wf v₂ v₂)).mpr ⟨(hpsd v₂).1, hLV v₂⟩
  exact ⟨hW, Wf v₁ v₁, Wf v₂ v₂, ⟨hLV1, hpsd v₁, hAB⟩, ⟨hLV2, hpsd v₂, hBA⟩, hsum⟩

end

end CausalNonpurifiability
