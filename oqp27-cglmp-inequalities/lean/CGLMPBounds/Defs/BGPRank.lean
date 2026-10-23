module

public import CGLMPBounds.Defs.BGP

@[expose] public section


/-! Literal ordered Table G.2 data and augmented coordinates, without rank proofs. -/
namespace CGLMPBounds
open Finset

/-- The identifiers `ι(s)` of Table G.2, in order. -/
def bgpRankIds : Fin 48 → ℕ :=
  ![4, 6, 8, 20, 21, 22, 23, 34, 38, 42, 46, 54, 58, 62, 64, 65, 72, 81, 85, 89, 93, 96, 97, 98,
    99, 113, 121, 125, 128, 132, 136, 140, 149, 151, 156, 162, 163, 172, 188, 191, 200, 201, 202,
    203, 213, 215, 221, 226]

/-- The deterministic strategy `s = (a₀, a₁, b₀, b₁)` with identifier `ι = 64a₀ + 16a₁ + 4b₀ + b₁`
(`ι < 256`). -/
def bgpStrategyOfId (ι : ℕ) : Strategy (Fin 4) (Fin 4) :=
  (![⟨ι / 64 % 4, Nat.mod_lt _ (by norm_num)⟩, ⟨ι / 16 % 4, Nat.mod_lt _ (by norm_num)⟩],
    ![⟨ι / 4 % 4, Nat.mod_lt _ (by norm_num)⟩, ⟨ι % 4, Nat.mod_lt _ (by norm_num)⟩])

/-- The saturator of Table G.2 with index `i`. -/
def bgpRankStrategy (i : Fin 48) : Strategy (Fin 4) (Fin 4) := bgpStrategyOfId (bgpRankIds i)

/-- `A_i(s) = 1{a_{⌊i/3⌋} = i mod 3}`, `i < 6`. -/
def bgpAInd (s : Strategy (Fin 4) (Fin 4)) (i : ℕ) : ℤ :=
  if (s.1 (if i < 3 then 0 else 1)).val = i % 3 then 1 else 0

/-- `B_j(s) = 1{b_{⌊j/3⌋} = j mod 3}`, `j < 6`. -/
def bgpBInd (s : Strategy (Fin 4) (Fin 4)) (j : ℕ) : ℤ :=
  if (s.2 (if j < 3 then 0 else 1)).val = j % 3 then 1 else 0

/-- The augmented coordinate `z(s)_c`, `0 ≤ c ≤ 48`: `1`, then `A(s)`, then `B(s)`, then the products
`A_i(s) B_j(s)` in row-major order. -/
def bgpZ (s : Strategy (Fin 4) (Fin 4)) (c : ℕ) : ℤ :=
  if c = 0 then 1
  else if c ≤ 6 then bgpAInd s (c - 1)
  else if c ≤ 12 then bgpBInd s (c - 7)
  else bgpAInd s ((c - 13) / 6) * bgpBInd s ((c - 13) % 6)

/-- The columns of `Z_min`: columns `0, …, 46` and `48` of `z` (column 47 deleted). -/
def bgpRankCol (c : Fin 48) : ℕ := if c.val < 47 then c.val else 48

/-- The `48 × 48` matrix `Z_min` of (G.2). -/
def bgpRankZ (i c : Fin 48) : ℤ := bgpZ (bgpRankStrategy i) (bgpRankCol c)

end CGLMPBounds
