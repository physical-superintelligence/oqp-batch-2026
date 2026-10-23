module

public import ThreeCopyQutritWerner.CertificateX2CoreT0Gen
public meta import ThreeCopyQutritWerner.CertificateX2CoreT0Gen
public import ThreeCopyQutritWerner.CertificateX2Images
public meta import ThreeCopyQutritWerner.CertificateX2Images
public import ThreeCopyQutritWerner.CertificateX2FacesTrialData
public meta import ThreeCopyQutritWerner.CertificateX2FacesTrialData

public meta section


/-!
# Input stage: the symmetry-reduced input tables computed inside Lean

`x2_input_tables S A s ratio` computes, at build time and from data already in Lean (the images `J`
of CertificateX2Images, the trial factors `F = K Z` of CertificateX2FacesTrialData, the local Gram
matrices, the 8 corrections `K, Cnum`), the tables of
`8 · Sel⊗3(3 den_c · x2InputBlock)` of the corrected sources of sector `s` (`ratio = den_c / 2^160`),
in the layout of `x2_t0_chunk`:
* `S`: rows `d < 282`, entry `b ≤ d` packs the values at `(a, b, d)`, `a ≤ b`, in `b + 1` slots;
* `A`: rows `l₀ < 282`, entry `m₂ < 231` packs the values at `(l₀; m₁, m₂)`, `m₁ ≤ m₂`.
Slots of 232 bits, offset `2^231`. Build-time data, which the input stage relates to the bridge's
`x2EmbedS`/`x2EmbedA` by kernel checks; they feed `x2_core_f0_tab`, so that the tables are computed
during the build. The certificate's single-representative embedding is followed exactly (sum over the keys of a type
triple, the identity placement for S, the last site placement for A).
-/

namespace ThreeCopyQutritWerner.X2
open Lean Elab Command

/-- Signed slots (width `w`, offset `2^(w-1)`) of a packed natural with `k` slots. -/
def slotsSigned (P w k : Nat) : Array Int :=
  (unpackSlots P w k (#[] : Array Nat)).map (fun (x : Nat) => (x : Int) - ((2 ^ (w - 1) : Nat) : Int))

/-- The integer `Σ xs[i] 2^(w i)` (signed slots, `|xs[i]| < 2^(w-1)`). -/
def packSignedInt (xs : Array Int) (w : Nat) : Int :=
  let off : Int := ((2 ^ (w - 1) : Nat) : Int)
  let nat := packSlots (xs.map (fun v => (v + off).toNat)) w 0 xs.size
  (nat : Int) - off * ((repunit w xs.size : Nat) : Int)

/-- Signed slots of an integer with `k` slots of width `w` (inverse of `packSignedInt`). -/
def unpackSignedInt (z : Int) (w k : Nat) : Array Int :=
  let off : Int := ((2 ^ (w - 1) : Nat) : Int)
  slotsSigned (z + off * ((repunit w k : Nat) : Int)).toNat w k

/-- Rows `Σ_i M[x][i] · P[i]` (packed integers `P[i]`) for every row `x` of `M`. -/
def rowsTimesPacked (M : Array (Array Int)) (P : Array Int) : Array Int :=
  M.map (fun row => Id.run do
    let mut acc : Int := 0
    for i in [0:row.size] do
      let a := row[i]!
      if a != 0 then acc := acc + a * P[i]!
    return acc)

/-- Apply the local Gram matrices site by site to packed rows indexed by the flat ambient
`(x₀, x₁, x₂)` (row-major, dims `m`): row `x` becomes `Σ_{x'_a} G_a[x_a][x'_a] row(x with x_a := x'_a)`. -/
def gramRows (G : Array (Array (Array Int))) (m : Array Nat) (rows : Array Int) : Array Int := Id.run do
  let mut cur := rows
  let strides := #[m[1]! * m[2]!, m[2]!, 1]
  for a in [0:3] do
    let Ga := G[a]!
    let st := strides[a]!
    let ma := m[a]!
    let mut nxt : Array Int := Array.mkEmpty cur.size
    for x in [0:cur.size] do
      let xa := (x / st) % ma
      let base := x - xa * st
      let mut acc : Int := 0
      for y in [0:ma] do
        let g := (Ga[xa]!)[y]!
        if g != 0 then acc := acc + g * cur[base + y * st]!
      nxt := nxt.push acc
    cur := nxt
  return cur

/-- Index of the unordered pair `{a, b}` among the pairs `a ≤ b` of `m` units. -/
def pairIdxS (m a b : Nat) : Nat :=
  let lo := min a b
  let hi := max a b
  lo * m - lo * (lo - 1) / 2 + (hi - lo)

/-- Index of the pair `a < b` among the pairs of distinct units of `m` units. -/
def pairIdxA (m a b : Nat) : Nat :=
  let lo := min a b
  let hi := max a b
  lo * m - lo * (lo + 1) / 2 + (hi - lo - 1)

def readNatListConst (n : Name) : CommandElabM (Array Nat) := do
  resolveNatList (← constValue (← resolveGlobalConstNoOverload (mkIdent n)))

syntax (name := x2InputTables) "x2_input_tables " ident ident num num : command

@[command_elab x2InputTables] def elabX2InputTables : CommandElab := fun stx => do
  match stx with
  | `(x2_input_tables $preS:ident $preA:ident $sN:num $ratioN:num) =>
    let s := sN.getNat
    let ratio : Int := ratioN.getNat
    let ns ← getCurrNamespace
    let keys ← readNatListConst (Name.mkSimple s!"x2InKeys_{s}")
    let mult ← readNatListConst (Name.mkSimple s!"x2InMult_{s}")
    let soff ← readNatListConst (Name.mkSimple s!"x2InSOff_{s}")
    let aoff ← readNatListConst (Name.mkSimple s!"x2InAOff_{s}")
    let mut grams : Array (Array (Array Int)) := #[]
    for t in [0:8] do
      let mt := mult[t]!
      let raw ← readNatListConst (Name.mkSimple s!"x2InGram_{s}_{t}")
      let mut Gt : Array (Array Int) := #[]
      for i in [0:mt] do
        Gt := Gt.push ((List.range mt).toArray.map (fun j => (raw[i * mt + j]! : Int) - 1048576))
      grams := grams.push Gt
    -- key records: g t0 t1 t2 kind degree r corrected
    let nk := keys.size / 8
    let mut S : Array Int := Array.replicate 3777484 0
    let mut A : Array Int := Array.replicate (282 * 26796) 0
    let Wv := 192
    let Wu := 320
    let Wp := 400
    let mut k := 0
    while k < nk do
      let t0 := keys[8 * k + 1]!
      let t1 := keys[8 * k + 2]!
      let t2 := keys[8 * k + 3]!
      -- the keys of this type triple (consecutive in the global order)
      let mut grp : Array Nat := #[]
      let mut k2 := k
      while k2 < nk && keys[8 * k2 + 1]! == t0 && keys[8 * k2 + 2]! == t1 && keys[8 * k2 + 3]! == t2 do
        grp := grp.push k2
        k2 := k2 + 1
      k := k2
      let tau := #[t0, t1, t2]
      let m := tau.map (fun t => mult[t]!)
      let amb := m[0]! * m[1]! * m[2]!
      let G := tau.map (fun t => grams[t]!)
      -- parts of the summed input block: (scalars amb × q, packed columns over y)
      let mut parts : Array (Array (Array Int) × Array Int) := #[]
      for kk in grp do
        let g := keys[8 * kk]!
        let degree := keys[8 * kk + 5]!
        let r := keys[8 * kk + 6]!
        let corr := keys[8 * kk + 7]!
        let Jcols ← readNatListConst (Name.mkSimple s!"x2J_{g}")
        let Jc := Jcols.map (fun P => slotsSigned P 11 amb)          -- r columns over x
        let Jrows : Array (Array Int) := (List.range amb).toArray.map (fun x => Jc.map (fun col => col[x]!))
        let Fcols ← readNatListConst (Name.mkSimple s!"x2Trial_{g}")
        let n := Fcols.size
        if n > 0 then
          let Fc := Fcols.map (fun P => slotsSigned P 80 r)          -- n columns over i
          let Frows : Array Int := (List.range r).toArray.map (fun i => packSignedInt (Fc.map (fun col => col[i]!)) Wv)
          let V0 := rowsTimesPacked Jrows Frows                          -- packed rows over c
          let Vp := gramRows G m V0
          let V : Array (Array Int) := Vp.map (fun z => unpackSignedInt z Wv n)
          let Vcols : Array Int := (List.range n).toArray.map (fun c => packSignedInt (V.map (fun row => row[c]!)) Wp)
          parts := parts.push (V.map (fun row => row.map (fun v => 3 * ratio * v)), Vcols)
          if degree == 2 then
            -- partner: W2[x0,x1,x2] = V[x2,x0,x1] - V[x1,x2,x0]  (equal dims)
            let md := m[0]!
            let W2 : Array (Array Int) := (List.range amb).toArray.map (fun x =>
              let x0 := x / (md * md)
              let x1 := (x / md) % md
              let x2 := x % md
              let ia := (x2 * md + x0) * md + x1
              let ib := (x1 * md + x2) * md + x0
              (List.range n).toArray.map (fun c => (V[ia]!)[c]! - (V[ib]!)[c]!))
            let W2cols : Array Int := (List.range n).toArray.map (fun c => packSignedInt (W2.map (fun row => row[c]!)) Wp)
            parts := parts.push (W2.map (fun row => row.map (fun v => ratio * v)), W2cols)
        if corr == 1 then
          let Krows ← readNatListConst (Name.mkSimple s!"x2InK_{g}")
          let Crows ← readNatListConst (Name.mkSimple s!"x2InC_{g}")
          let kk2 := Crows.size
          let Kp : Array Int := Krows.map (fun P => packSignedInt (slotsSigned P 64 kk2) Wu)
          let U0 := rowsTimesPacked Jrows Kp
          let Up := gramRows G m U0
          let U : Array (Array Int) := Up.map (fun z => unpackSignedInt z Wu kk2)
          let Cp : Array Int := Crows.map (fun P => packSignedInt (slotsSigned P 192 kk2) Wu)
          let UC : Array (Array Int) := (rowsTimesPacked U Cp).map (fun z => unpackSignedInt z Wu kk2)
          let Ucols : Array Int := (List.range kk2).toArray.map (fun c => packSignedInt (U.map (fun row => row[c]!)) Wp)
          parts := parts.push (UC.map (fun row => row.map (fun v => 3 * v)), Ucols)
      -- scatter the rows of the summed input block of this type triple
      let m0 := m[0]!
      let m1 := m[1]!
      let m2 := m[2]!
      let so0 := soff[t0]!
      let so1 := soff[t1]!
      let so2 := soff[t2]!
      let ao0 := aoff[t0]!
      let ao1 := aoff[t1]!
      let ao2 := aoff[t2]!
      let last0 := t1 != t0 && t2 != t0
      let last1 := t2 != t1
      let eq12 := t1 == t2
      let eq02 := t0 == t2
      let eq01 := t0 == t1
      for x in [0:amb] do
        let mut rowx : Int := 0
        for (Am, Bc) in parts do
          let ax := Am[x]!
          for c in [0:ax.size] do
            let a := ax[c]!
            if a != 0 then rowx := rowx + a * Bc[c]!
        let vals := unpackSignedInt rowx Wp amb
        let x0 := x / (m1 * m2)
        let x1 := (x / m2) % m1
        let x2 := x % m2
        for y in [0:amb] do
          let v := vals[y]!
          if v != 0 then
            let y0 := y / (m1 * m2)
            let y1 := (y / m2) % m1
            let y2 := y % m2
            let d0 := x0 != y0
            let d1 := x1 != y1
            let d2 := x2 != y2
            let l0 := so0 + pairIdxS m0 x0 y0
            let l1 := so1 + pairIdxS m1 x1 y1
            let l2 := so2 + pairIdxS m2 x2 y2
            if l0 ≤ l1 && l1 ≤ l2 then
              let off := (if d0 then 1 else 0) + (if d1 then 1 else 0) + (if d2 then 1 else 0)
              let idx := l2 * (l2 + 1) * (l2 + 2) / 6 + l1 * (l1 + 1) / 2 + l0
              S := S.set! idx (S[idx]! + ((8 / 2 ^ off : Nat) : Int) * v)
            -- A placements: S at site sp, A at the other two sites (o0 < o1)
            -- sp = 0: o = (1, 2); sp = 1: o = (0, 2); sp = 2: o = (0, 1)
            if last0 && m1 ≥ 2 && m2 ≥ 2 && d1 && d2 then
              let mA := ao1 + pairIdxA m1 x1 y1
              let mB := ao2 + pairIdxA m2 x2 y2
              if !eq12 || mA ≥ mB then
                let sgn : Int := (if x1 < y1 then 1 else -1) * (if x2 < y2 then 1 else -1)
                let w : Int := if d0 then 1 else 2
                let lo := min mA mB
                let hi := max mA mB
                let idx := l0 * 26796 + hi * (hi + 1) / 2 + lo
                A := A.set! idx (A[idx]! + w * sgn * v)
            if last1 && m0 ≥ 2 && m2 ≥ 2 && d0 && d2 then
              let mA := ao0 + pairIdxA m0 x0 y0
              let mB := ao2 + pairIdxA m2 x2 y2
              if !eq02 || mA ≥ mB then
                let sgn : Int := (if x0 < y0 then 1 else -1) * (if x2 < y2 then 1 else -1)
                let w : Int := if d1 then 1 else 2
                let lo := min mA mB
                let hi := max mA mB
                let idx := l1 * 26796 + hi * (hi + 1) / 2 + lo
                A := A.set! idx (A[idx]! + w * sgn * v)
            if m0 ≥ 2 && m1 ≥ 2 && d0 && d1 then
              let mA := ao0 + pairIdxA m0 x0 y0
              let mB := ao1 + pairIdxA m1 x1 y1
              if !eq01 || mA ≥ mB then
                let sgn : Int := (if x0 < y0 then 1 else -1) * (if x1 < y1 then 1 else -1)
                let w : Int := if d2 then 1 else 2
                let lo := min mA mB
                let hi := max mA mB
                let idx := l2 * 26796 + hi * (hi + 1) / 2 + lo
                A := A.set! idx (A[idx]! + w * sgn * v)
    -- pack the tables (232-bit slots, offset 2^231)
    let WD := 232
    let offD : Int := ((2 ^ (WD - 1) : Nat) : Int)
    let mut rowsS : Array Expr := #[]
    let mut pos := 0
    for d in [0:282] do
      let mut row : Array Nat := #[]
      for b in [0:d + 1] do
        row := row.push (packSlots ((S.extract pos (pos + b + 1)).map (fun v => (v + offD).toNat)) WD 0 (b + 1))
        pos := pos + b + 1
      rowsS := rowsS.push (mkNatListExpr row.toList)
    let mut rowsA : Array Expr := #[]
    pos := 0
    for _l0 in [0:282] do
      let mut row : Array Nat := #[]
      for m2 in [0:231] do
        row := row.push (packSlots ((A.extract pos (pos + m2 + 1)).map (fun v => (v + offD).toNat)) WD 0 (m2 + 1))
        pos := pos + m2 + 1
      rowsA := rowsA.push (mkNatListExpr row.toList)
    let tabTy := mkApp (mkConst ``List [Level.zero]) natListTy
    let mkTab := fun (rows : Array Expr) => rows.toList.foldr
      (fun r acc => mkApp3 (mkConst ``List.cons [Level.zero]) natListTy r acc)
      (mkApp (mkConst ``List.nil [Level.zero]) natListTy)
    addRawDef (ns ++ preS.getId) tabTy (mkTab rowsS)
    addRawDef (ns ++ preA.getId) tabTy (mkTab rowsA)
  | _ => throwUnsupportedSyntax

end ThreeCopyQutritWerner.X2
