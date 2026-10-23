module

public import CGLMPBounds.Defs.CircularPartition

@[expose] public section


/-! Literal source extension V_(j+d)=-i V_j used in D.2–D.3. -/

namespace CGLMPBounds.Partition
noncomputable section

def sourceCyclicExtension {d r : ℕ} (hd : 0 < d)
    (V : Fin d → Circulation.Mat r) (n : ℕ) : Circulation.Mat r :=
  (-Complex.I) ^ (n / d) • V ⟨n % d, Nat.mod_lt _ hd⟩

end
end CGLMPBounds.Partition
