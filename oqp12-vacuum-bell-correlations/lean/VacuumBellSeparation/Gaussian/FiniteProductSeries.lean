module

public import Mathlib

@[expose] public section


/-!
# Absolutely convergent finite products of nonnegative series

The multi-index series is over all tuples of natural numbers, not a finite
cutoff. Its convergence and value follow inductively from nonnegative
Fubini and the finite-tuple equivalence.
-/

namespace VacuumBellSeparation.Gaussian

set_option maxHeartbeats 800000 in
theorem hasSum_fin_product_nonneg (m : ℕ) (f : Fin m → ℕ → ℝ) (s : Fin m → ℝ)
    (hf : ∀ j n, 0 ≤ f j n) (hs : ∀ j, HasSum (f j) (s j)) :
    HasSum (fun k : Fin m → ℕ => ∏ j, f j (k j)) (∏ j, s j) := by
  classical
  induction m with
  | zero =>
    letI : Fintype (Fin 0 → ℕ) := Fintype.ofSubsingleton (fun i => Fin.elim0 i)
    simpa using hasSum_fintype (fun k : Fin 0 → ℕ => ∏ j, f j (k j))
  | succ m ih =>
    have htail : HasSum (fun k : Fin m → ℕ => ∏ j, f j.succ (k j)) (∏ j : Fin m, s j.succ) :=
      ih (fun j => f j.succ) (fun j => s j.succ)
      (fun j n => hf j.succ n) (fun j => hs j.succ)
    have hnonneg (k : Fin m → ℕ) : 0 ≤ ∏ j, f j.succ (k j) :=
      Finset.prod_nonneg fun j _ => hf j.succ (k j)
    have habs : Summable (fun k : ℕ × (Fin m → ℕ) =>
        f 0 k.1 * ∏ j, f j.succ (k.2 j)) :=
      (hs 0).summable.mul_of_nonneg htail.summable (hf 0) hnonneg
    have hsum : HasSum (fun k : ℕ × (Fin m → ℕ) =>
        f 0 k.1 * ∏ j, f j.succ (k.2 j)) (s 0 * ∏ j : Fin m, s j.succ) :=
      (hs 0).mul htail habs
    apply (Fin.consEquiv (fun _ : Fin (m + 1) => ℕ)).hasSum_iff.mp
    simpa only [Function.comp_def, Fin.consEquiv_apply, Fin.prod_univ_succ,
      Fin.cons_zero, Fin.cons_succ] using hsum

end VacuumBellSeparation.Gaussian
