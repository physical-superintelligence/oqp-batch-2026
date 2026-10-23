module

public import ThreeCopyQutritWerner.TwoCutSOS
public import ThreeCopyQutritWerner.TwoCutFactor

@[expose] public section


/-!
# The common four-register shadow projector

The logical replica swap is symmetric and each of the three physical replica
swaps is antisymmetric. All four act on the same two replicas. Positivity is
proved as a literal squared norm, with normalization 1/16.
-/

noncomputable section

open scoped BigOperators ComplexConjugate

namespace ThreeCopyQutritWerner

/-- A signed normalized replica involution on the original coordinate vector. -/
def jointShadowParity {ι : Type*} (e : ι ≃ ι) (s : ℝ) (f : ι → ℂ) : ι → ℂ :=
  fun p => (f p + (s : ℂ) * f (e p)) / 2

/-- Every real signed involution is selfadjoint for the original finite pairing. -/
theorem jointShadowParity_selfadjoint {ι : Type*} [Fintype ι]
    (e : ι ≃ ι) (he : ∀ p, e (e p) = p) (s : ℝ) (f g : ι → ℂ) :
    braket (jointShadowParity e s f) g = braket f (jointShadowParity e s g) := by
  have hperm : (∑ p, conj (f (e p)) * g p) = ∑ p, conj (f p) * g (e p) := by
    apply Fintype.sum_equiv e
    intro p
    rw [he]
  have hL : 2 * braket (jointShadowParity e s f) g =
      braket f g + (s : ℂ) * ∑ p, conj (f (e p)) * g p := by
    simp only [braket, Finset.mul_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro p _
    simp only [jointShadowParity, map_div₀, map_add, map_mul,
      Complex.conj_ofReal, map_ofNat]
    ring
  have hR : 2 * braket f (jointShadowParity e s g) =
      braket f g + (s : ℂ) * ∑ p, conj (f p) * g (e p) := by
    simp only [braket, Finset.mul_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro p _
    simp only [jointShadowParity]
    ring
  rw [hperm] at hL
  linear_combination (hL - hR) / 2

variable {l a b c : Type*}

/-- Exchange only the logical coordinates of the two four-party replicas. -/
def jointShadowSwapL : ((l × a × b × c) × (l × a × b × c)) ≃
    ((l × a × b × c) × (l × a × b × c)) where
  toFun p := ((p.2.1, p.1.2), (p.1.1, p.2.2))
  invFun p := ((p.2.1, p.1.2), (p.1.1, p.2.2))
  left_inv _ := rfl
  right_inv _ := rfl

/-- Exchange only the first physical coordinates. -/
def jointShadowSwapA : ((l × a × b × c) × (l × a × b × c)) ≃
    ((l × a × b × c) × (l × a × b × c)) where
  toFun p := ((p.1.1, p.2.2.1, p.1.2.2), (p.2.1, p.1.2.1, p.2.2.2))
  invFun p := ((p.1.1, p.2.2.1, p.1.2.2), (p.2.1, p.1.2.1, p.2.2.2))
  left_inv _ := rfl
  right_inv _ := rfl

/-- Exchange only the second physical coordinates. -/
def jointShadowSwapB : ((l × a × b × c) × (l × a × b × c)) ≃
    ((l × a × b × c) × (l × a × b × c)) where
  toFun p := ((p.1.1, p.1.2.1, p.2.2.2.1, p.1.2.2.2),
    (p.2.1, p.2.2.1, p.1.2.2.1, p.2.2.2.2))
  invFun p := ((p.1.1, p.1.2.1, p.2.2.2.1, p.1.2.2.2),
    (p.2.1, p.2.2.1, p.1.2.2.1, p.2.2.2.2))
  left_inv _ := rfl
  right_inv _ := rfl

/-- Exchange only the third physical coordinates. -/
def jointShadowSwapC : ((l × a × b × c) × (l × a × b × c)) ≃
    ((l × a × b × c) × (l × a × b × c)) where
  toFun p := ((p.1.1, p.1.2.1, p.1.2.2.1, p.2.2.2.2),
    (p.2.1, p.2.2.1, p.2.2.2.1, p.1.2.2.2))
  invFun p := ((p.1.1, p.1.2.1, p.1.2.2.1, p.2.2.2.2),
    (p.2.1, p.2.2.1, p.2.2.2.1, p.1.2.2.2))
  left_inv _ := rfl
  right_inv _ := rfl

/-- The actual product `(I+F_L)(I-F_A)(I-F_B)(I-F_C)/16`. -/
def jointShadowProjection (f : ((l × a × b × c) × (l × a × b × c)) → ℂ) :=
  jointShadowParity jointShadowSwapL 1
    (jointShadowParity jointShadowSwapA (-1)
      (jointShadowParity jointShadowSwapB (-1)
        (jointShadowParity jointShadowSwapC (-1) f)))

/-- The four local parities produce an actual idempotent. -/
theorem jointShadowProjection_idempotent
    (f : ((l × a × b × c) × (l × a × b × c)) → ℂ) :
    jointShadowProjection (jointShadowProjection f) = jointShadowProjection f := by
  funext p
  simp only [jointShadowProjection, jointShadowParity, jointShadowSwapL,
    jointShadowSwapA, jointShadowSwapB, jointShadowSwapC, Equiv.coe_fn_mk,
    Complex.ofReal_one, Complex.ofReal_neg]
  ring

variable [Fintype l] [Fintype a] [Fintype b] [Fintype c]

/-- The same actual product is selfadjoint, since its four local swaps commute. -/
theorem jointShadowProjection_selfadjoint
    (f g : ((l × a × b × c) × (l × a × b × c)) → ℂ) :
    braket (jointShadowProjection f) g = braket f (jointShadowProjection g) := by
  unfold jointShadowProjection
  rw [jointShadowParity_selfadjoint jointShadowSwapL (fun _ => rfl),
    jointShadowParity_selfadjoint jointShadowSwapA (fun _ => rfl),
    jointShadowParity_selfadjoint jointShadowSwapB (fun _ => rfl),
    jointShadowParity_selfadjoint jointShadowSwapC (fun _ => rfl)]
  congr 1
  funext p
  simp only [jointShadowParity, jointShadowSwapL, jointShadowSwapA,
    jointShadowSwapB, jointShadowSwapC, Equiv.coe_fn_mk,
    Complex.ofReal_one, Complex.ofReal_neg]
  ring

/-- The shadow expectation is the squared norm of the projected original vector. -/
theorem jointShadowProjection_expectation
    (f : ((l × a × b × c) × (l × a × b × c)) → ℂ) :
    (braket f (jointShadowProjection f)).re = vecNormSq (jointShadowProjection f) := by
  have h := jointShadowProjection_selfadjoint f (jointShadowProjection f)
  rw [jointShadowProjection_idempotent] at h
  rw [← h, braket_self, Complex.ofReal_re]

/-- Positivity of the exact common-four-register shadow remainder. -/
theorem jointShadowProjection_nonneg
    (f : ((l × a × b × c) × (l × a × b × c)) → ℂ) :
    0 ≤ (braket f (jointShadowProjection f)).re := by
  rw [jointShadowProjection_expectation]
  exact vecNormSq_nonneg _

end ThreeCopyQutritWerner
