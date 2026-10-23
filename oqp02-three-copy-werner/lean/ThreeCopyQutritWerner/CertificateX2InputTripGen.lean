module

public import ThreeCopyQutritWerner.CertificateX2InputVGen
public meta import ThreeCopyQutritWerner.CertificateX2InputVGen

public meta section


/-!
# Input stage: build-time generation for whole type triples

Ordinary (meta) code that computes candidate data; nothing here is trusted, the kernel re-checks every value
(`ibBatchOK`, `tCell`/`t2Check`, `partnerCheck`, `vCheck`, `uaCheck`).
* `x2_ub_nest pre W m₀ m₁ m₂ lo hi (S F α) …`: for the row-batches `(a₀, a₁)`, `lo ≤ a₀ < hi`, the constants
  `pre_<a₀>_<a₁> : List (List ℕ)`: entry `[b₀][b₁]` is the upper triangle `a₂ ≤ b₂` of the `m₂ × m₂` block
  `IB((a₀, a₁, a₂), (b₀, b₁, b₂))`, `IB(x, ·) = ∑ α S_c(x) F_c` (offset-encoded `W`-bit slots).
* `x2_ub_table T pre m₀ m₁`: `T : List (List (List (List ℕ)))`, `T[a₀][a₁] = pre_<a₀>_<a₁>` (constant references).
* `x2_tt_gen TT T m₀ m₁ m₂ ord`: the T-table of a type triple from the stored blocks: `ord = 0` rows by the second
  label (`TT[i₁][i₀]`), `ord = 1` rows by the first label (`TT[i₀][i₁]`); block = `2 (U₁ + U₂ + U₃ + U₄)`.
* `x2_p_cols P V m`: partner columns `P(x) = V(rotA x) - V(rotB x)` of the columns `V`.
* `x2_vk_cols out gj Fs W n`: columns of `GJ F` for the packed factor columns `Fs` (80-bit slots).
* `x2_ua_cols out U As n kd`: columns of `U A` (`As`: columns of `A`, 256-bit slots).
-/

namespace ThreeCopyQutritWerner.X2
open Lean Elab Command

def natTabTy : Expr := mkApp (mkConst ``List [Level.zero]) natListTy
def nat3Ty : Expr := mkApp (mkConst ``List [Level.zero]) natTabTy
def nat4Ty : Expr := mkApp (mkConst ``List [Level.zero]) nat3Ty

/-- A list expression of elements of type `ty`. -/
def mkListOf (ty : Expr) (xs : List Expr) : Expr :=
  xs.foldr (fun x acc => mkApp3 (mkConst ``List.cons [Level.zero]) ty x acc) (mkApp (mkConst ``List.nil [Level.zero]) ty)

def mkNatTabExpr (rows : List (List Nat)) : Expr := mkListOf natListTy (rows.map mkNatListExpr)

/-- The rows of a constant of type `List (List ℕ)`. -/
def readNatTab (n : Name) : CommandElabM (Array (Array Nat)) := resolveNatTable n

syntax ubPart := "(" ident ident num ")"
syntax (name := x2UbNest) "x2_ub_nest " ident num num num num num num ubPart* : command

@[command_elab x2UbNest] def elabX2UbNest : CommandElab := fun stx => do
  match stx with
  | `(x2_ub_nest $pre:ident $W:num $m0:num $m1:num $m2:num $lo:num $hi:num $parts:ubPart*) =>
    let (W, m0, m1, m2, lo, hi) := (W.getNat, m0.getNat, m1.getNat, m2.getNat, lo.getNat, hi.getNat)
    let n := m0 * m1 * m2
    let off : Int := (offsetM W (W - 1) n : Int)
    let mut terms : Array (Array Int × Int × Int) := #[]
    for p in parts do
      match p with
      | `(ubPart| ($S:ident $F:ident $a:num)) =>
        let Ss ← resolveNatList (← constValue (← resolveGlobalConstNoOverload S))
        let Fs ← resolveNatList (← constValue (← resolveGlobalConstNoOverload F))
        for c in [0:Ss.size] do
          terms := terms.push (slotsSigned Ss[c]! W n, (Fs[c]! : Int) - off, (a.getNat : Int))
      | _ => throwUnsupportedSyntax
    let ns ← getCurrNamespace
    let offW : Int := ((2 ^ (W - 1) : Nat) : Int)
    for a0 in [lo:hi] do
      for a1 in [0:m1] do
        let mut rows : Array (Array Int) := #[]
        for a2 in [0:m2] do
          let x := (a0 * m1 + a1) * m2 + a2
          let mut acc : Int := 0
          for (sv, fv, al) in terms do
            let sx := sv[x]!
            if sx != 0 then acc := acc + al * sx * fv
          rows := rows.push (unpackSignedInt acc W n)
        let mut tab : Array (List Nat) := #[]
        for b0 in [0:m0] do
          let mut row : Array Nat := #[]
          for b1 in [0:m1] do
            let base := (b0 * m1 + b1) * m2
            let mut slots : Array Nat := #[]
            for a2 in [0:m2] do
              for b2 in [a2:m2] do
                slots := slots.push ((rows[a2]!)[base + b2]! + offW).toNat
            row := row.push (packSlots slots W 0 slots.size)
          tab := tab.push row.toList
        addRawDef (ns ++ Name.mkSimple s!"{pre.getId}_{a0}_{a1}") natTabTy (mkNatTabExpr tab.toList)
  | _ => throwUnsupportedSyntax

syntax (name := x2UbTable) "x2_ub_table " ident ident num num : command

@[command_elab x2UbTable] def elabX2UbTable : CommandElab := fun stx => do
  match stx with
  | `(x2_ub_table $T:ident $pre:ident $m0:num $m1:num) =>
    let (m0, m1) := (m0.getNat, m1.getNat)
    let ns ← getCurrNamespace
    let mut rows : Array Expr := #[]
    for a0 in [0:m0] do
      let mut row : Array Expr := #[]
      for a1 in [0:m1] do
        let nm ← resolveGlobalConstNoOverload (mkIdent (Name.mkSimple s!"{pre.getId}_{a0}_{a1}"))
        row := row.push (mkConst nm)
      rows := rows.push (mkListOf natTabTy row.toList)
    addRawDef (ns ++ T.getId) nat4Ty (mkListOf nat3Ty rows.toList)
  | _ => throwUnsupportedSyntax

/-- Elements of a list term whose elements are constants or literal sub-terms (resolved by `f`). -/
partial def resolveListWith {α : Type} (f : Expr → CommandElabM α) (e : Expr) (acc : Array α) :
    CommandElabM (Array α) := do
  match e.getAppFnArgs with
  | (``List.nil, _) => return acc
  | (``List.cons, #[_, hd, tl]) => resolveListWith f tl (acc.push (← f hd))
  | _ =>
    match e with
    | .const c _ => resolveListWith f (← constValue c) acc
    | _ => throwError "not a list: {e}"

def resolveTabExpr (e : Expr) : CommandElabM (Array (Array Nat)) :=
  resolveListWith (fun r => resolveNatList r) e #[]

/-- The pairs `a ≤ b < m` in upper-triangle order (ordinary code). -/
def pairsUM (m : Nat) : Array (Nat × Nat) := Id.run do
  let mut out : Array (Nat × Nat) := #[]
  for a in [0:m] do
    for b in [a:m] do
      out := out.push (a, b)
  return out

syntax (name := x2TTGen) "x2_tt_gen " ident ident num num num num : command

@[command_elab x2TTGen] def elabX2TTGen : CommandElab := fun stx => do
  match stx with
  | `(x2_tt_gen $out:ident $T:ident $m0:num $m1:num $m2:num $ord:num) =>
    let (m0, m1, m2, ord) := (m0.getNat, m1.getNat, m2.getNat, ord.getNat)
    let W := 256
    let L2 := m2 * (m2 + 1) / 2
    let off : Int := (offsetM W (W - 1) L2 : Int)
    let Tn ← resolveGlobalConstNoOverload T
    -- U[a0][a1][b0][b1] as signed packed integers
    let ub : Array (Array (Array (Array Int))) ← resolveListWith (fun r0 =>
        resolveListWith (fun r1 => do
          let tab ← resolveTabExpr r1
          return tab.map (fun row => row.map (fun (v : Nat) => (v : Int) - off))) r0 #[]) (← constValue Tn) #[]
    let get := fun (a0 a1 b0 b1 : Nat) => ((((ub[a0]!)[a1]!)[b0]!)[b1]!)
    let p0s := pairsUM m0
    let p1s := pairsUM m1
    let cell := fun (p0 p1 : Nat × Nat) =>
      let v : Int := 2 * (get p0.1 p1.1 p0.2 p1.2 + get p0.2 p1.1 p0.1 p1.2 + get p0.1 p1.2 p0.2 p1.1 +
        get p0.2 p1.2 p0.1 p1.1)
      (v + off).toNat
    let rows : List (List Nat) :=
      if ord == 0 then p1s.toList.map (fun p1 => p0s.toList.map (fun p0 => cell p0 p1))
      else p0s.toList.map (fun p0 => p1s.toList.map (fun p1 => cell p0 p1))
    addRawDef ((← getCurrNamespace) ++ out.getId) natTabTy (mkNatTabExpr rows)
  | _ => throwUnsupportedSyntax

syntax (name := x2PCols) "x2_p_cols " ident ident num : command

@[command_elab x2PCols] def elabX2PCols : CommandElab := fun stx => do
  match stx with
  | `(x2_p_cols $out:ident $V:ident $m:num) =>
    let m := m.getNat
    let W := 256
    let n := m * m * m
    let Vs ← resolveNatList (← constValue (← resolveGlobalConstNoOverload V))
    let offW : Nat := 2 ^ (W - 1)
    let vals := Vs.toList.map (fun P => Id.run do
      let sl := unpackSlots P W n #[]
      let mut outS : Array Nat := #[]
      for x in [0:n] do
        let x0 := x / (m * m)
        let x1 := (x / m) % m
        let x2 := x % m
        let ia := (x2 * m + x0) * m + x1
        let ib := (x1 * m + x2) * m + x0
        outS := outS.push (sl[ia]! + offW - sl[ib]!)
      return packSlots outS W 0 n)
    addRawDef ((← getCurrNamespace) ++ out.getId) natListTy (mkNatListExpr vals)
  | _ => throwUnsupportedSyntax

syntax (name := x2VKCols) "x2_vk_cols " ident ident ident num num : command

/-- `x2_vk_cols out gj Fs W n`: columns of `GJ F` (`n` ambient slots), `F` given by packed 80-bit columns `Fs`. -/
@[command_elab x2VKCols] def elabX2VKCols : CommandElab := fun stx => do
  match stx with
  | `(x2_vk_cols $out:ident $gj:ident $Fs:ident $W:num $n:num) =>
    let (W, n) := (W.getNat, n.getNat)
    let gjs ← resolveNatList (← constValue (← resolveGlobalConstNoOverload gj))
    let r := gjs.size
    let off : Int := (offsetM W (W - 1) n : Int)
    let gjInt : Array Int := gjs.map (fun (Q : Nat) => (Q : Int) - off)
    let Fcols ← resolveNatList (← constValue (← resolveGlobalConstNoOverload Fs))
    let vals := Fcols.toList.map (fun Fc => Id.run do
      let fs := slotsSigned Fc 80 r
      let mut acc : Int := 0
      for d in [0:r] do
        let a := fs[d]!
        if a != 0 then acc := acc + a * gjInt[d]!
      return (acc + off).toNat)
    addRawDef ((← getCurrNamespace) ++ out.getId) natListTy (mkNatListExpr vals)
  | _ => throwUnsupportedSyntax

syntax (name := x2UACols) "x2_ua_cols " ident ident ident num num : command

/-- `x2_ua_cols out U As n kd`: columns `UA_c' = ∑_c A[c][c'] U_c` (`As`: columns of `A`, 256-bit slots). -/
@[command_elab x2UACols] def elabX2UACols : CommandElab := fun stx => do
  match stx with
  | `(x2_ua_cols $out:ident $U:ident $As:ident $n:num $kd:num) =>
    let (n, kd) := (n.getNat, kd.getNat)
    let W := 256
    let Us ← resolveNatList (← constValue (← resolveGlobalConstNoOverload U))
    let off : Int := (offsetM W (W - 1) n : Int)
    let uInt : Array Int := Us.map (fun (Q : Nat) => (Q : Int) - off)
    let Acols ← resolveNatList (← constValue (← resolveGlobalConstNoOverload As))
    let vals := Acols.toList.map (fun Ac => Id.run do
      let as := slotsSigned Ac 256 kd
      let mut acc : Int := 0
      for c in [0:kd] do
        let a := as[c]!
        if a != 0 then acc := acc + a * uInt[c]!
      return (acc + off).toNat)
    addRawDef ((← getCurrNamespace) ++ out.getId) natListTy (mkNatListExpr vals)
  | _ => throwUnsupportedSyntax

/-- The pairs `a < b < m` in row-major order (ordinary code). -/
def pairsAM (m : Nat) : Array (Nat × Nat) := Id.run do
  let mut out : Array (Nat × Nat) := #[]
  for a in [0:m] do
    for b in [a + 1:m] do
      out := out.push (a, b)
  return out

syntax (name := x2TTGenG) "x2_tt_genG " ident ident num num num num num num num num num num : command

/-- `x2_tt_genG out T m₀ m₁ m₂ ord k₀ k₁ s₁ s₂ s₃ s₄`: T-table with pair kinds `k₀`, `k₁` of the first two sites
(`0` = S pairs `a ≤ b`, `1` = A pairs `a < b`), block `∑ (sᵢ - 4) Uᵢ`, rows by the second label (`ord = 0`) or by
the first (`ord = 1`). -/
@[command_elab x2TTGenG] def elabX2TTGenG : CommandElab := fun stx => do
  match stx with
  | `(x2_tt_genG $out:ident $T:ident $m0:num $m1:num $m2:num $ord:num $k0:num $k1:num $s1:num $s2:num $s3:num $s4:num) =>
    let (m0, m1, m2, ord, k0, k1) := (m0.getNat, m1.getNat, m2.getNat, ord.getNat, k0.getNat, k1.getNat)
    let sc : Array Int := #[(s1.getNat : Int) - 4, (s2.getNat : Int) - 4, (s3.getNat : Int) - 4, (s4.getNat : Int) - 4]
    let W := 256
    let L2 := m2 * (m2 + 1) / 2
    let off : Int := (offsetM W (W - 1) L2 : Int)
    let Tn ← resolveGlobalConstNoOverload T
    let ub : Array (Array (Array (Array Int))) ← resolveListWith (fun r0 =>
        resolveListWith (fun r1 => do
          let tab ← resolveTabExpr r1
          return tab.map (fun row => row.map (fun (v : Nat) => (v : Int) - off))) r0 #[]) (← constValue Tn) #[]
    let get := fun (a0 a1 b0 b1 : Nat) => ((((ub[a0]!)[a1]!)[b0]!)[b1]!)
    let p0s := if k0 == 0 then pairsUM m0 else pairsAM m0
    let p1s := if k1 == 0 then pairsUM m1 else pairsAM m1
    let cell := fun (p0 p1 : Nat × Nat) =>
      let v : Int := sc[0]! * get p0.1 p1.1 p0.2 p1.2 + sc[1]! * get p0.2 p1.1 p0.1 p1.2 +
        sc[2]! * get p0.1 p1.2 p0.2 p1.1 + sc[3]! * get p0.2 p1.2 p0.1 p1.1
      (v + off).toNat
    let rows : List (List Nat) :=
      if ord == 0 then p1s.toList.map (fun p1 => p0s.toList.map (fun p0 => cell p0 p1))
      else p0s.toList.map (fun p0 => p1s.toList.map (fun p1 => cell p0 p1))
    addRawDef ((← getCurrNamespace) ++ out.getId) natTabTy (mkNatTabExpr rows)
  | _ => throwUnsupportedSyntax

end ThreeCopyQutritWerner.X2
