module

public import ThreeCopyQutritWerner.CertificateX2OutputOfTables
public import ThreeCopyQutritWerner.CertificateX2OutputTgtFamily

@[expose] public section


/-!
# Output stage: the residual block of an h block from the tables

`x2Residual_of_tables`: for the concrete data, if the tables of both source sectors satisfy the
global interface (`X2TableS`, `X2TableA`; their `transfer_slot`) and the per-fiber bounds, then two kernel checks
(`x2OutNum` of each sector against literals `O1`, `O2`) and the integer identity
`N k₀ = T8 k₁ - O1 k₂ - O2 k₃` (`T8 = x2TgtLit b`, proved target) give
`x2Residual x2DataConcrete Nm Na b = (1 / den) • N.map Int.cast`, the `heq` of the `x2_residualBlocks_posSemidef` at block `b`.
-/

open scoped Matrix

namespace ThreeCopyQutritWerner
namespace X2

/-- THE RESIDUAL OF ONE h BLOCK from the two sectors' tables (concrete data). -/
theorem x2Residual_of_tables (Nm : X2Blocks 1) (Na : X2Blocks 2) (b : x2Key 0)
    (W1 d1 bF1 q1 W2 d2 bF2 q2 : ℕ) (fibS1 fibA1 fibS2 fibA2 : ℕ → ℕ → ℕ)
    (hS1 : X2TableS x2DataConcrete 1 Nm W1 (q1 : ℚ) fibS1) (hA1 : X2TableA x2DataConcrete 1 Nm W1 (q1 : ℚ) fibA1)
    (hS2 : X2TableS x2DataConcrete 2 Na W2 (q2 : ℚ) fibS2) (hA2 : X2TableA x2DataConcrete 2 Na W2 (q2 : ℚ) fibA2)
    (hW1 : 12 ≤ W1) (hbF1 : bF1 + 3 ≤ W1) (hB1 : X2BlockBounds W1 bF1 b fibS1 fibA1)
    (hW2 : 12 ≤ W2) (hbF2 : bF2 + 3 ≤ W2) (hB2 : X2BlockBounds W2 bF2 b fibS2 fibA2)
    (hb11 : ((x2KeyMult 0 b 0 * x2KeyMult 0 b 1 * x2KeyMult 0 b 2 : ℕ) : ℤ) * (2 ^ 10 * 2 ^ (bF1 + 1)) <
      2 ^ (W1 - 1))
    (hb12 : ((x2KeyMult 0 b 0 * x2KeyMult 0 b 1 * x2KeyMult 0 b 2 : ℕ) : ℤ) *
      (((x2KeyMult 0 b 0 * x2KeyMult 0 b 1 * x2KeyMult 0 b 2 : ℕ) : ℤ) * (2 ^ 10 * 2 ^ (bF1 + 1)) * 2 ^ 10) <
        2 ^ (W1 - 1))
    (hb21 : ((x2KeyMult 0 b 0 * x2KeyMult 0 b 1 * x2KeyMult 0 b 2 : ℕ) : ℤ) * (2 ^ 10 * 2 ^ (bF2 + 1)) <
      2 ^ (W2 - 1))
    (hb22 : ((x2KeyMult 0 b 0 * x2KeyMult 0 b 1 * x2KeyMult 0 b 2 : ℕ) : ℤ) *
      (((x2KeyMult 0 b 0 * x2KeyMult 0 b 1 * x2KeyMult 0 b 2 : ℕ) : ℤ) * (2 ^ 10 * 2 ^ (bF2 + 1)) * 2 ^ 10) <
        2 ^ (W2 - 1))
    (O1 O2 Nl : Matrix (x2Col 0 b) (x2Col 0 b) ℤ)
    (hc1 : ∀ c c' : x2Col 0 b, x2OutNum W1 d1 b fibS1 fibA1 (x2JAll.getD (x2KeyGlobal 0 b) []) c c' = O1 c c')
    (hc2 : ∀ c c' : x2Col 0 b, x2OutNum W2 d2 b fibS2 fibA2 (x2JAll.getD (x2KeyGlobal 0 b) []) c c' = O2 c c')
    (den k0 k1 k2 k3 : ℕ) (hden : 0 < den) (hk0 : 0 < k0)
    (hk1 : 8 * k1 = den * k0) (hk2 : q1 * k2 = den * k0) (hk3 : q2 * k3 = den * k0)
    (hint : ∀ c c' : x2Col 0 b, Nl c c' * k0 = x2TgtLit b c c' * k1 - O1 c c' * k2 - O2 c c' * k3) :
    x2Residual x2DataConcrete Nm Na b = (1 / (den : ℚ)) • Nl.map (Int.cast : ℤ → ℚ) :=
  x2Residual_eq_fam x2DataConcrete Nm Na b (x2TgtLit b) O1 O2 Nl q1 q2 den k0 k1 k2 k3 hden hk0 hk1 hk2 hk3
    (x2Target_concrete b)
    (x2Out_of_tables 1 Nm b W1 d1 bF1 q1 fibS1 fibA1 hS1 hA1 hW1 hbF1 hB1 hb11 hb12 O1 hc1)
    (x2Out_of_tables 2 Na b W2 d2 bF2 q2 fibS2 fibA2 hS2 hA2 hW2 hbF2 hB2 hb21 hb22 O2 hc2) hint

end X2
end ThreeCopyQutritWerner
