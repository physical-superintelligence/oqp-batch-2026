module

public import ThreeCopyQutritWerner.CertificateX2PackedNatAxpy

@[expose] public section


/-! Packed engine: glue from the natural linear-combination check to
`Fin`-indexed sums, in the integer form and in the rational form of the bridge's axis contractions
(`x2Axis0/1/2 M T = ∑ a, M i a * T a j k` with `M = num / den` and `T = ent / σ`). -/

open scoped BigOperators

namespace ThreeCopyQutritWerner
namespace X2

theorem lincomb_ofFn (W : ℕ) : ∀ {n : ℕ} (f : Fin n → ℤ) (E : Fin n → ℕ) (k : ℕ),
    lincomb W (List.ofFn f) (List.ofFn E) k = ∑ a : Fin n, f a * ent W (W - 1) (E a) k
  | 0, f, E, k => by simp [lincomb]
  | n + 1, f, E, k => by
    rw [List.ofFn_succ, List.ofFn_succ, Fin.sum_univ_succ]
    simp only [lincomb]
    rw [lincomb_ofFn W (fun i => f i.succ) (fun i => E i.succ) k]

theorem sScalars_ofFn (oA : ℕ) {n : ℕ} (g : Fin n → ℕ) :
    sScalars oA (List.ofFn g) = List.ofFn (fun a => (g a : ℤ) - 2 ^ oA) := by
  unfold sScalars
  rw [List.map_ofFn]
  rfl

/-- One contraction from one natural linear-combination check (integer form). -/
theorem natAxpy_contract (W L oA : ℕ) {n : ℕ} (g E : Fin n → ℕ) (outE : ℕ) (hW : 2 ≤ W)
    (hE : ∀ a, E a < 2 ^ (W * L))
    (hlin : ∀ k < L, |∑ a : Fin n, ((g a : ℤ) - 2 ^ oA) * ent W (W - 1) (E a) k| < 2 ^ (W - 1))
    (hcheck : natAxpyCheck W L oA (List.ofFn g) (List.ofFn E) outE
      (natAxpyCorr W L oA (List.ofFn E)) = true)
    (k : ℕ) (hk : k < L) :
    ∑ a : Fin n, ((g a : ℤ) - 2 ^ oA) * ent W (W - 1) (E a) k = ent W (W - 1) outE k := by
  have h := natAxpyCheck_sound W L oA (List.ofFn g) (List.ofFn E) outE hW (by simp)
    (by
      intro F hF
      obtain ⟨a, rfl⟩ := List.mem_ofFn.mp hF
      exact hE a)
    (by
      intro k' hk'
      rw [sScalars_ofFn, lincomb_ofFn]
      exact hlin k' hk')
    hcheck k hk
  rwa [sScalars_ofFn, lincomb_ofFn] at h

/-- The same contraction with rational scalings `num / den` and `ent / σ`. -/
theorem natAxpy_contract_rat (W L oA : ℕ) {n : ℕ} (g E : Fin n → ℕ) (outE : ℕ) (den σ : ℚ)
    (hW : 2 ≤ W) (hE : ∀ a, E a < 2 ^ (W * L))
    (hlin : ∀ k < L, |∑ a : Fin n, ((g a : ℤ) - 2 ^ oA) * ent W (W - 1) (E a) k| < 2 ^ (W - 1))
    (hcheck : natAxpyCheck W L oA (List.ofFn g) (List.ofFn E) outE
      (natAxpyCorr W L oA (List.ofFn E)) = true)
    (k : ℕ) (hk : k < L) :
    ∑ a : Fin n, (((g a : ℤ) - 2 ^ oA : ℤ) : ℚ) / den * ((ent W (W - 1) (E a) k : ℚ) / σ) =
      (ent W (W - 1) outE k : ℚ) / (den * σ) := by
  have h := natAxpy_contract W L oA g E outE hW hE hlin hcheck k hk
  have hq : ((∑ a : Fin n, ((g a : ℤ) - 2 ^ oA) * ent W (W - 1) (E a) k : ℤ) : ℚ) =
      (ent W (W - 1) outE k : ℚ) := by
    rw [h]
  rw [← hq, Int.cast_sum, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro a _
  push_cast
  ring

end X2
end ThreeCopyQutritWerner
