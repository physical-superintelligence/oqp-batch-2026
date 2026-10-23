module

public import CGLMPBounds.Scenario.Local
public import CGLMPBounds.TensorCHSH.Counting

@[expose] public section


/-!
# The thresholded CHSH-error witness on the local set

Manuscript locator: proof of Theorem A.3 (Appendix F.2). For `4k < M` and `h = M - 3k` the
witness `G_{M,k}(p) = (1/4) ∑_{x,y} [Pr_p(K_{xy} ≤ k) - Pr_p(K_{xy} ≥ h)]` has local bound at most
`1/2`. Here outcomes are `M`-bit strings and `bell (witnessTable M k h)` is `4 G_{M,k}`.
-/

namespace CGLMPBounds.TensorCHSH

noncomputable section

/-- Coefficient table of the (unnormalised) thresholded witness:
`1[K_{xy}(a,b) ≤ k] - 1[K_{xy}(a,b) ≥ h]`. -/
def witnessTable (m k h : ℕ) : Table (Fin m → Bool) (Fin m → Bool) :=
  fun x y a b =>
    (if errCount x y a b ≤ k then (1 : ℝ) else 0) - (if h ≤ errCount x y a b then (1 : ℝ) else 0)

/-- Local bound of the thresholded witness: `4 G_{M,k} ≤ 2` on the Bell-local set whenever
`4k < M` (with upper threshold `h = M - 3k`). -/
theorem bell_witnessTable_le_two {m k : ℕ} (hk : 4 * k < m)
    {q : Table (Fin m → Bool) (Fin m → Bool)}
    (hq : q ∈ localSet (Fin m → Bool) (Fin m → Bool)) :
    bell (witnessTable m k (m - 3 * k)) q ≤ 2 := by
  refine bell_le_of_mem_localSet (fun s => ?_) hq
  rw [bell_detTable]
  have h := witness_det_le_two hk s.1 s.2
  have h' : ((∑ x : Fin 2, ∑ y : Fin 2,
      ((if errCount x y (s.1 x) (s.2 y) ≤ k then (1 : ℤ) else 0)
        - (if m - 3 * k ≤ errCount x y (s.1 x) (s.2 y) then (1 : ℤ) else 0)) : ℤ) : ℝ)
      ≤ ((2 : ℤ) : ℝ) :=
    Int.cast_le.mpr h
  push_cast at h'
  simp only [witnessTable]
  exact h'

end

end CGLMPBounds.TensorCHSH
