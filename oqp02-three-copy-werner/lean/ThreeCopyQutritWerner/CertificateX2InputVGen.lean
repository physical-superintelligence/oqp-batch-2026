module

public import ThreeCopyQutritWerner.CertificateX2InputGen
public meta import ThreeCopyQutritWerner.CertificateX2InputGen
public import ThreeCopyQutritWerner.CertificateX2InputMeta
public meta import ThreeCopyQutritWerner.CertificateX2InputMeta

public meta section


/-!
# Input stage: build-time generation of the `GJ` and `V` columns

`x2_gj_cols name g s t₀ t₁ t₂ W` defines `name : List ℕ`, the columns of `GJ = (G ⊗ G ⊗ G) J` of image `g`
(sector `s`, local types `tᵢ`), offset-encoded with `W`-bit slots, computed in ordinary code by the
same masked-multiplication site stages as the kernel function `gjApply` (so the kernel check
`gjCheck` re-computes exactly these numbers). `x2_v_cols name gj g W` defines the columns of
`V = GJ F` (`F` the trial factor of image `g`) by packed integer linear combinations. Build-time data
only: every value is checked by the kernel (`gjCheck`, `vCheck`).
-/

namespace ThreeCopyQutritWerner.X2
open Lean Elab Command

/-- The low `n` slots of width `wi` re-packed at width `wo` (ordinary code, divide and conquer). -/
partial def spreadMeta (wi wo n P : Nat) : Nat :=
  if n ≤ 8 then
    (List.range n).foldl (fun acc i => acc + (((P >>> (wi * i)) &&& (2 ^ wi - 1)) <<< (wo * i))) 0
  else
    let h := n / 2
    spreadMeta wi wo h (P &&& (2 ^ (wi * h) - 1)) + (spreadMeta wi wo (n - h) (P >>> (wi * h)) <<< (wo * h))

/-- `∑_{i<m} f i` (ordinary code). -/
def natSumM (m : Nat) (f : Nat → Nat) : Nat := Id.run do
  let mut acc := 0
  for i in [0:m] do
    acc := acc + f i
  return acc

def repunitM (W L : Nat) : Nat := (2 ^ (W * L) - 1) / (2 ^ W - 1)

def offsetM (W o L : Nat) : Nat := 2 ^ o * repunitM W L

def siteMaskM (W A m B y : Nat) : Nat := (2 ^ (W * B) - 1) * 2 ^ (W * (B * y)) * repunitM (W * (m * B)) A

def siteSelM (W A m B y E : Nat) : Nat := (E &&& siteMaskM W A m B y) >>> (W * (B * y))

def sitePolyM (W B m : Nat) (h : Nat → Nat) : Nat := natSumM m (fun x => h x * 2 ^ (W * (B * x)))

def siteSumM (W A m B : Nat) (g : Nat → Nat → Nat) (E : Nat) : Nat :=
  natSumM m (fun y => siteSelM W A m B y E * sitePolyM W B m (fun x => g x y))

def siteRSM (W A m B : Nat) (r : Nat → Nat) : Nat := sitePolyM W B m r * repunitM W B * repunitM (W * (m * B)) A

def siteApplyM (W A m B : Nat) (gp gn : Nat → Nat → Nat) (E : Nat) : Nat :=
  let rsn := siteRSM W A m B (fun x => natSumM m (fun y => gn x y))
  let rsp := siteRSM W A m B (fun x => natSumM m (fun y => gp x y))
  (siteSumM W A m B gp E + offsetM W (W - 1) (A * (m * B)) + 2 ^ (W - 1) * rsn) -
    (siteSumM W A m B gn E + 2 ^ (W - 1) * rsp)

/-- Gram entries of sector `s`, type `t` from the raw metadata lists (offset `2^20`). -/
def gramEntryM (raw : Array Nat) (mt x y : Nat) : Int :=
  if x < mt ∧ y < mt then (raw.getD (x * mt + y) 1048576 : Int) - 1048576 else 0

def gjApplyM (W : Nat) (G0 G1 G2 : Array Nat) (m0 m1 m2 P : Nat) : Nat :=
  let n := m0 * m1 * m2
  let E := spreadMeta 11 W n P + (2 ^ (W - 1) - 2 ^ 10) * repunitM W n
  let gp := fun (raw : Array Nat) (mt : Nat) (x y : Nat) => (gramEntryM raw mt x y).toNat
  let gn := fun (raw : Array Nat) (mt : Nat) (x y : Nat) => (-(gramEntryM raw mt x y)).toNat
  let S2 := siteApplyM W (m0 * m1) m2 1 (gp G2 m2) (gn G2 m2) E
  let S1 := siteApplyM W m0 m1 m2 (gp G1 m1) (gn G1 m1) S2
  siteApplyM W 1 m0 (m1 * m2) (gp G0 m0) (gn G0 m0) S1

syntax (name := x2GJCols) "x2_gj_cols " ident num num num num num num : command

@[command_elab x2GJCols] def elabX2GJCols : CommandElab := fun stx => do
  match stx with
  | `(x2_gj_cols $out:ident $g:num $s:num $t0:num $t1:num $t2:num $W:num) =>
    let (g, s, t0, t1, t2, W) := (g.getNat, s.getNat, t0.getNat, t1.getNat, t2.getNat, W.getNat)
    let mult ← readNatListConst (Name.mkSimple s!"x2InMult_{s}")
    let G := fun (t : Nat) => readNatListConst (Name.mkSimple s!"x2InGram_{s}_{t}")
    let G0 ← G t0
    let G1 ← G t1
    let G2 ← G t2
    let (m0, m1, m2) := (mult[t0]!, mult[t1]!, mult[t2]!)
    let cols ← readNatListConst (Name.mkSimple s!"x2J_{g}")
    let vals := cols.toList.map (fun P => gjApplyM W G0 G1 G2 m0 m1 m2 P)
    addRawDef ((← getCurrNamespace) ++ out.getId) natListTy (mkNatListExpr vals)
  | _ => throwUnsupportedSyntax

syntax (name := x2VCols) "x2_v_cols " ident ident num num num : command

/-- `x2_v_cols out gj g W n`: columns of `V = GJ F` (`n` ambient slots). -/
@[command_elab x2VCols] def elabX2VCols : CommandElab := fun stx => do
  match stx with
  | `(x2_v_cols $out:ident $gj:ident $g:num $W:num $n:num) =>
    let (g, W, n) := (g.getNat, W.getNat, n.getNat)
    let gjs ← resolveNatList (← constValue (← resolveGlobalConstNoOverload gj))
    let r := gjs.size
    let off : Int := (offsetM W (W - 1) n : Int)
    let gjInt : Array Int := gjs.map (fun (Q : Nat) => (Q : Int) - off)
    let Fcols ← readNatListConst (Name.mkSimple s!"x2Trial_{g}")
    let vals := Fcols.toList.map (fun Fc => Id.run do
      let fs := slotsSigned Fc 80 r
      let mut acc : Int := 0
      for d in [0:r] do
        let a := fs[d]!
        if a != 0 then acc := acc + a * gjInt[d]!
      return (acc + off).toNat)
    addRawDef ((← getCurrNamespace) ++ out.getId) natListTy (mkNatListExpr vals)
  | _ => throwUnsupportedSyntax

end ThreeCopyQutritWerner.X2
