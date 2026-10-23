module

public import CGLMPBounds.Defs.Scenario

@[expose] public section


/-!
# Local tables and linear Bell functionals

* `mem_localSet_iff` : a table is Bell-local iff it is a mixture of deterministic tables with a
  probability weight on the finitely many deterministic assignments (hidden-variable form).
* `bell c` : the linear functional `q ↦ ∑ c(a,b|x,y) q(a,b|x,y)`.
* `le_bell_of_mem_localSet`, `bell_le_of_mem_localSet` : a bound on all deterministic tables
  holds on the whole local set.
-/

namespace CGLMPBounds

noncomputable section

section Bell

variable {α β : Type*} [Fintype α] [Fintype β]

/-- The Bell functional with coefficient table `c`, as a linear map:
`bell c q = ∑_{x,y,a,b} c(a,b|x,y) q(a,b|x,y)`. -/
def bell (c : Table α β) : Table α β →ₗ[ℝ] ℝ where
  toFun q := ∑ x, ∑ y, ∑ a, ∑ b, c x y a b * q x y a b
  map_add' p q := by
    simp only [Pi.add_apply, mul_add, Finset.sum_add_distrib]
  map_smul' r q := by
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply, Finset.mul_sum]
    refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ =>
      Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
    ring

theorem bell_apply (c q : Table α β) :
    bell c q = ∑ x, ∑ y, ∑ a, ∑ b, c x y a b * q x y a b :=
  rfl

end Bell

variable {α β : Type*} [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β]

/-- Hidden-variable form of Bell locality: a table lies in the convex hull of the deterministic
tables iff it is their mixture under a probability weight on deterministic assignments. -/
theorem mem_localSet_iff {q : Table α β} :
    q ∈ localSet α β ↔ ∃ w : Strategy α β → ℝ, (∀ s, 0 ≤ w s) ∧ ∑ s, w s = 1 ∧
      q = ∑ s, w s • detTable s := by
  classical
  constructor
  · intro hq
    have key : localSet α β ⊆ {q : Table α β | ∃ w : Strategy α β → ℝ,
        (∀ s, 0 ≤ w s) ∧ ∑ s, w s = 1 ∧ q = ∑ s, w s • detTable s} := by
      unfold localSet
      refine convexHull_min ?_ ?_
      · rintro _ ⟨s₀, rfl⟩
        refine ⟨fun s => if s = s₀ then 1 else 0, fun s => ?_, ?_, ?_⟩
        · by_cases h : s = s₀ <;> simp [h]
        · simp
        · rw [Finset.sum_eq_single_of_mem s₀ (Finset.mem_univ _)]
          · simp
          · intro s _ hs
            simp [hs]
      · rintro _ ⟨w₁, h₁0, h₁1, rfl⟩ _ ⟨w₂, h₂0, h₂1, rfl⟩ a b ha hb hab
        refine ⟨fun s => a * w₁ s + b * w₂ s, fun s => ?_, ?_, ?_⟩
        · exact add_nonneg (mul_nonneg ha (h₁0 s)) (mul_nonneg hb (h₂0 s))
        · rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum, h₁1, h₂1]
          linarith
        · simp only [Finset.smul_sum, smul_smul, add_smul, Finset.sum_add_distrib]
    exact key hq
  · rintro ⟨w, hw0, hw1, rfl⟩
    exact (convex_convexHull ℝ _).sum_mem (fun s _ => hw0 s) hw1
      (fun s _ => subset_convexHull ℝ _ ⟨s, rfl⟩)

/-- The value of a Bell functional on a deterministic table. -/
theorem bell_detTable (c : Table α β) (s : Strategy α β) :
    bell c (detTable s) = ∑ x, ∑ y, c x y (s.1 x) (s.2 y) := by
  rw [bell_apply]
  refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => ?_
  have inner : ∀ a : α, ∑ b, c x y a b * detTable s x y a b
      = if a = s.1 x then c x y a (s.2 y) else 0 := by
    intro a
    rw [Finset.sum_eq_single_of_mem (s.2 y) (Finset.mem_univ _)]
    · by_cases ha : a = s.1 x <;> simp [detTable, ha]
    · intro b _ hb
      simp [detTable, hb]
  simp only [inner]
  simp

theorem bell_sum_weights (c : Table α β) (w : Strategy α β → ℝ) :
    bell c (∑ s, w s • detTable s) = ∑ s, w s * bell c (detTable s) := by
  rw [map_sum]
  simp only [map_smul, smul_eq_mul]

/-- A lower bound valid on every deterministic table holds on the local set. -/
theorem le_bell_of_mem_localSet {c : Table α β} {B : ℝ} (h : ∀ s, B ≤ bell c (detTable s))
    {q : Table α β} (hq : q ∈ localSet α β) : B ≤ bell c q := by
  obtain ⟨w, hw0, hw1, rfl⟩ := mem_localSet_iff.mp hq
  rw [bell_sum_weights]
  calc B = ∑ s, w s * B := by rw [← Finset.sum_mul, hw1, one_mul]
    _ ≤ ∑ s, w s * bell c (detTable s) :=
        Finset.sum_le_sum fun s _ => mul_le_mul_of_nonneg_left (h s) (hw0 s)

/-- An upper bound valid on every deterministic table holds on the local set. -/
theorem bell_le_of_mem_localSet {c : Table α β} {B : ℝ} (h : ∀ s, bell c (detTable s) ≤ B)
    {q : Table α β} (hq : q ∈ localSet α β) : bell c q ≤ B := by
  obtain ⟨w, hw0, hw1, rfl⟩ := mem_localSet_iff.mp hq
  rw [bell_sum_weights]
  calc ∑ s, w s * bell c (detTable s) ≤ ∑ s, w s * B :=
        Finset.sum_le_sum fun s _ => mul_le_mul_of_nonneg_left (h s) (hw0 s)
    _ = B := by rw [← Finset.sum_mul, hw1, one_mul]

end

end CGLMPBounds
