module

public import CGLMPBounds.TensorCHSH.Witness
public import CGLMPBounds.Noise.Witness
public import CGLMPBounds.Noise.Uniform

@[expose] public section


/-!
# Critical visibility from the thresholded CHSH-error witness

Proof of Theorem A.3 (Appendix F.2): if `4k < M` and the witness value of the noise mixture at
visibility `v₀` exceeds its local bound, then `v_crit < v₀`. In the manuscript's normalisation
(`G_{M,k} = bell (witnessTable M k h) / 4`, local bound `1/2`) the hypothesis reads
`G_{M,k}(v₀ q + (1 - v₀) u) > 1/2`.
-/

namespace CGLMPBounds.TensorCHSH

noncomputable section

theorem critVisibility_lt_of_witnessTable {m k : ℕ} (hk : 4 * k < m)
    {q : Table (Fin m → Bool) (Fin m → Bool)} {v₀ : ℝ} (hv₀ : 0 < v₀)
    (h : 2 < v₀ * bell (witnessTable m k (m - 3 * k)) q
      + (1 - v₀) * bell (witnessTable m k (m - 3 * k))
          (uniformTable (Fin m → Bool) (Fin m → Bool))) :
    critVisibility q < v₀ :=
  critVisibility_lt_of_witness (fun _ hp => bell_witnessTable_le_two hk hp)
    (bell_witnessTable_le_two hk uniformTable_mem_localSet) hv₀ h

end

end CGLMPBounds.TensorCHSH
