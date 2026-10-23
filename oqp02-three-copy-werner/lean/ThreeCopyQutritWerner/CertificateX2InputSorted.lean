module

public import ThreeCopyQutritWerner.CertificateX2InputJInv2

@[expose] public section


/-!
# Input stage: source tensors on type-sorted label triples

For the concrete data and ANY source `N` of sector 1 or 2: when the types of the three labels are
nondecreasing, `x2EmbedS` (and `x2EmbedA`) is the parity select of the plain sum `x2KeySum` of the
input-block lookups of the keys of that type triple (no average over site arrangements). With the
label symmetries `x2EmbedS_swap01/12`, `x2EmbedA_swap12` (CertificateX2InputSym) this reduces the
input-stage hypothesis hT0 to type-sorted label triples.
-/

open scoped BigOperators

namespace ThreeCopyQutritWerner
namespace X2

/-- Sum of the input-block lookups of the keys of a type triple. -/
noncomputable def x2KeySum (s : Fin 3) (N : X2Blocks s) (t : Fin 3 → Fin 8) (a b : Fin 3 → ℕ) : ℚ :=
  ∑ k : x2Key s, if x2KeyTypes s k = t then x2Lookup (x2InputBlock x2DataConcrete s N k) a b else 0

theorem x2EmbedS_sorted_concrete (s : Fin 3) (hs : s = 1 ∨ s = 2) (N : X2Blocks s) (l₀ l₁ l₂ : Fin 282)
    (h01 : (x2SLabel s l₀).1 ≤ (x2SLabel s l₁).1) (h12 : (x2SLabel s l₁).1 ≤ (x2SLabel s l₂).1) :
    x2EmbedS x2DataConcrete s N l₀ l₁ l₂ =
      x2SelS (fun x₀ y₀ => x2SelS (fun x₁ y₁ => x2SelS (fun x₂ y₂ =>
        x2KeySum s N ![(x2SLabel s l₀).1, (x2SLabel s l₁).1, (x2SLabel s l₂).1] ![x₀, x₁, x₂] ![y₀, y₁, y₂])
        (x2SLabel s l₂).2.1 (x2SLabel s l₂).2.2) (x2SLabel s l₁).2.1 (x2SLabel s l₁).2.2)
        (x2SLabel s l₀).2.1 (x2SLabel s l₀).2.2 := by
  have ht : x2Sorted ![(x2SLabel s l₀).1, (x2SLabel s l₁).1, (x2SLabel s l₂).1] := by
    unfold x2Sorted
    exact ⟨h01, h12⟩
  unfold x2EmbedS x2KeySum
  simp only [x2FullTensor_sorted_concrete s hs N _ _ _ ht]

theorem x2EmbedA_sorted_concrete (s : Fin 3) (hs : s = 1 ∨ s = 2) (N : X2Blocks s) (l₀ : Fin 282)
    (l₁ l₂ : Fin 231) (h01 : (x2SLabel s l₀).1 ≤ (x2ALabel s l₁).1) (h12 : (x2ALabel s l₁).1 ≤ (x2ALabel s l₂).1) :
    x2EmbedA x2DataConcrete s N l₀ l₁ l₂ =
      x2SelS (fun x₀ y₀ => x2SelA (fun x₁ y₁ => x2SelA (fun x₂ y₂ =>
        x2KeySum s N ![(x2SLabel s l₀).1, (x2ALabel s l₁).1, (x2ALabel s l₂).1] ![x₀, x₁, x₂] ![y₀, y₁, y₂])
        (x2ALabel s l₂).2.1 (x2ALabel s l₂).2.2) (x2ALabel s l₁).2.1 (x2ALabel s l₁).2.2)
        (x2SLabel s l₀).2.1 (x2SLabel s l₀).2.2 := by
  have ht : x2Sorted ![(x2SLabel s l₀).1, (x2ALabel s l₁).1, (x2ALabel s l₂).1] := by
    unfold x2Sorted
    exact ⟨h01, h12⟩
  unfold x2EmbedA x2KeySum
  simp only [x2FullTensor_sorted_concrete s hs N _ _ _ ht]

end X2
end ThreeCopyQutritWerner
