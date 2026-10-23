module

public import ThreeCopyQutritWerner.CertificateX2CoreLemmas
public meta import ThreeCopyQutritWerner.CertificateX2CoreLemmas
public import ThreeCopyQutritWerner.CertificateX2PackedStage
public meta import ThreeCopyQutritWerner.CertificateX2PackedStage

public meta section


/-!
# Contraction core: build-time data generation

Commands that compute the candidate outputs of a contraction stage in ordinary (meta) code and
define them as raw literals. Nothing here is trusted: every generated value is a candidate that
the kernel re-checks with `rowCheck` / `slotRow` (`CertificateX2CoreLemmas`).

* `x2_core_synth_rows pre W L C b seed lo hi`: synthetic rows `pre_j` (`C` fibers of `L` slots,
  entries in `[-2^b, 2^b)`), for tests of the pipeline at full size.
* `x2_core_table pre J`: `pre : List (List ℕ) := [pre_0, ..., pre_(J-1)]` (constant references).
* `x2_core_stageA_rows pre W L oA R F lo hi`: rows `j` of `F`, output `k` = sparse combination of
  the row with scalar row `k` of `R` (`x2Axis2`).
* `x2_core_stageB_rows pre W L oA R F lo hi`: rows `k` = combinations of column `k` of `F`
  (`x2Axis1`).
* `x2_core_cols pre W m oA R`: packed columns of `R` (offset `2^(W-1)`, `m` slots).
* `x2_core_stageC_rows pre W n m Cs F lo hi`: rows `k` of `F`, each fiber's slots against `Cs`
  (`x2Axis0`).
-/

namespace ThreeCopyQutritWerner.X2
open Lean Elab Command

/-- Expected output of a sparse check (computable). -/
def natAxpySpOut (W L oA : ℕ) (as Fs : List ℕ) : ℕ :=
  natAxpyOut W L oA ((spPairs (2 ^ oA) as Fs).map Prod.fst) ((spPairs (2 ^ oA) as Fs).map Prod.snd)

/-- Expected output of a slot check, with the shifted columns and correction precomputed. -/
def slotOutPre (W n m : ℕ) (CsF : List ℕ) (corr : ℕ) (x : ℕ) : ℕ :=
  (natDot (digs W n x) CsF + corr) % 2 ^ (W * m)

/-- A natural number term: raw literal or `OfNat.ofNat` numeral. -/
def natOfExpr? (e : Expr) : Option Nat :=
  match e with
  | .lit (.natVal n) => some n
  | _ =>
    match e.getAppFnArgs with
    | (``OfNat.ofNat, #[_, .lit (.natVal n), _]) => some n
    | _ => none

/-- Elements of a list term of naturals (cons cells may be constant references). -/
partial def resolveNatListAux (e : Expr) (acc : Array Nat) : CommandElabM (Array Nat) := do
  match e.getAppFnArgs with
  | (``List.nil, _) => return acc
  | (``List.cons, #[_, hd, tl]) =>
    match natOfExpr? hd with
    | some n => resolveNatListAux tl (acc.push n)
    | none => throwError "not a natural literal: {hd}"
  | _ =>
    match e with
    | .const c _ => resolveNatListAux (← constValue c) acc
    | _ => throwError "not a list of naturals: {e}"

/-- Literal elements of a list term. -/
def resolveNatList (e : Expr) : CommandElabM (Array Nat) := resolveNatListAux e #[]

/-- Rows of a table term (rows may be constant references). -/
partial def resolveNatTableExpr (e : Expr) (acc : Array (Array Nat)) :
    CommandElabM (Array (Array Nat)) := do
  match e.getAppFnArgs with
  | (``List.nil, _) => return acc
  | (``List.cons, #[_, hd, tl]) => resolveNatTableExpr tl (acc.push (← resolveNatList hd))
  | _ =>
    match e with
    | .const c _ => resolveNatTableExpr (← constValue c) acc
    | _ => throwError "not a table: {e}"

/-- Rows of a table constant. -/
def resolveNatTable (n : Name) : CommandElabM (Array (Array Nat)) := do
  resolveNatTableExpr (← constValue n) #[]

def natListTy : Expr := mkApp (mkConst ``List [Level.zero]) (mkConst ``Nat)

syntax (name := x2CoreSynthRows) "x2_core_synth_rows " ident num num num num num num num : command
syntax (name := x2CoreTable) "x2_core_table " ident num : command
syntax (name := x2CoreStageARows) "x2_core_stageA_rows " ident num num num ident ident num num : command
syntax (name := x2CoreStageBRows) "x2_core_stageB_rows " ident num num num ident ident num num : command
syntax (name := x2CoreCols) "x2_core_cols " ident num num num ident : command
syntax (name := x2CorePackRows) "x2_core_pack_rows " ident num num ident : command
syntax (name := x2CoreMatmulRows) "x2_core_matmul_rows " ident num num num ident ident : command
syntax (name := x2CoreRowselect) "x2_core_rowselect " ident ident ident : command
syntax (name := x2CoreSubtable) "x2_core_subtable " ident ident num num : command
syntax (name := x2CoreStageCRows) "x2_core_stageC_rows " ident num num num ident ident num num : command

def rowName (pre : Name) (j : Nat) : Name := Name.mkSimple (pre.toString ++ "_" ++ toString j)

@[command_elab x2CoreSynthRows] def elabX2CoreSynthRows : CommandElab := fun stx => do
  match stx with
  | `(x2_core_synth_rows $pre:ident $W:num $L:num $C:num $b:num $seed:num $lo:num $hi:num) =>
    let (W, L, C, b, seed) := (W.getNat, L.getNat, C.getNat, b.getNat, seed.getNat)
    let ns ← getCurrNamespace
    let total := W * L
    let modulus := 1 <<< total
    -- low `b+1` bits of every slot: entries `v + 2^b` in `[0, 2^(b+1))`
    let lowMask := ((1 <<< (b + 1)) - 1) * repunit W L
    let shift := offset W (W - 1) L - offset W b L
    let mul : Nat := 3 ^ (total + 7) % modulus ||| 1
    let mut x : Nat := (seed * 0x9E3779B97F4A7C15 + 12345) % modulus
    for j in [lo.getNat:hi.getNat] do
      let mut row : Array Nat := #[]
      for c in [0:C] do
        x := (x * mul + (j * C + c + seed)) % modulus
        row := row.push ((x &&& lowMask) + shift)
      addRawDef (ns ++ rowName pre.getId j) natListTy (mkNatListExpr row.toList)
  | _ => throwUnsupportedSyntax

@[command_elab x2CoreTable] def elabX2CoreTable : CommandElab := fun stx => do
  match stx with
  | `(x2_core_table $pre:ident $J:num) =>
    let ns ← getCurrNamespace
    let rows := (List.range J.getNat).map fun j => mkConst (ns ++ rowName pre.getId j)
    let val := rows.foldr (fun r acc => mkApp3 (mkConst ``List.cons [Level.zero]) natListTy r acc)
      (mkApp (mkConst ``List.nil [Level.zero]) natListTy)
    addRawDef (ns ++ pre.getId) (mkApp (mkConst ``List [Level.zero]) natListTy) val
  | _ => throwUnsupportedSyntax

@[command_elab x2CoreStageARows] def elabX2CoreStageARows : CommandElab := fun stx => do
  match stx with
  | `(x2_core_stageA_rows $pre:ident $W:num $L:num $oA:num $R:ident $F:ident $lo:num $hi:num) =>
    let (W, L, oA) := (W.getNat, L.getNat, oA.getNat)
    let ns ← getCurrNamespace
    let Rt ← resolveNatTable (← resolveGlobalConstNoOverload R)
    let Ft ← resolveNatTable (← resolveGlobalConstNoOverload F)
    for j in [lo.getNat:hi.getNat] do
      let row := Ft[j]!.toList
      let outs := Rt.toList.map fun r => natAxpySpOut W L oA r.toList row
      addRawDef (ns ++ rowName pre.getId j) natListTy (mkNatListExpr outs)
  | _ => throwUnsupportedSyntax

@[command_elab x2CoreStageBRows] def elabX2CoreStageBRows : CommandElab := fun stx => do
  match stx with
  | `(x2_core_stageB_rows $pre:ident $W:num $L:num $oA:num $R:ident $F:ident $lo:num $hi:num) =>
    let (W, L, oA) := (W.getNat, L.getNat, oA.getNat)
    let ns ← getCurrNamespace
    let Rt ← resolveNatTable (← resolveGlobalConstNoOverload R)
    let Ft ← resolveNatTable (← resolveGlobalConstNoOverload F)
    for k in [lo.getNat:hi.getNat] do
      let col := Ft.toList.map fun row => row.getD k 0
      let outs := Rt.toList.map fun r => natAxpySpOut W L oA r.toList col
      addRawDef (ns ++ rowName pre.getId k) natListTy (mkNatListExpr outs)
  | _ => throwUnsupportedSyntax

@[command_elab x2CoreCols] def elabX2CoreCols : CommandElab := fun stx => do
  match stx with
  | `(x2_core_cols $pre:ident $W:num $m:num $oA:num $R:ident) =>
    let (W, m, oA) := (W.getNat, m.getNat, oA.getNat)
    let ns ← getCurrNamespace
    let Rt ← resolveNatTable (← resolveGlobalConstNoOverload R)
    let n := (Rt[0]!).size
    let cols := (List.range n).map fun a =>
      (List.range m).foldl (fun acc i =>
        acc + ((Rt[i]!)[a]! + 2 ^ (W - 1) - 2 ^ oA) * 2 ^ (W * i)) 0
    addRawDef (ns ++ pre.getId) natListTy (mkNatListExpr cols)
  | _ => throwUnsupportedSyntax

@[command_elab x2CoreStageCRows] def elabX2CoreStageCRows : CommandElab := fun stx => do
  match stx with
  | `(x2_core_stageC_rows $pre:ident $W:num $n:num $m:num $Cs:ident $F:ident $lo:num $hi:num) =>
    let (W, n, m) := (W.getNat, n.getNat, m.getNat)
    let ns ← getCurrNamespace
    let cs := (← resolveNatList (← constValue (← resolveGlobalConstNoOverload Cs))).toList
    let csF := natFibers W m cs
    let corr := natAxpyCorr W m (W - 1) cs
    let Ft ← resolveNatTable (← resolveGlobalConstNoOverload F)
    for k in [lo.getNat:hi.getNat] do
      let outs := (Ft[k]!).toList.map fun x => slotOutPre W n m csF corr x
      addRawDef (ns ++ rowName pre.getId k) natListTy (mkNatListExpr outs)
  | _ => throwUnsupportedSyntax

/-- `x2_core_pack_rows pre W oB B`: the rows of the table `B` (entries `B c k + 2^oB`) as packed
fibers of width `W`, offset `2^(W-1)` (to be checked against `B` by the kernel). -/
@[command_elab x2CorePackRows] def elabX2CorePackRows : CommandElab := fun stx => do
  match stx with
  | `(x2_core_pack_rows $pre:ident $W:num $oB:num $B:ident) =>
    let (W, oB) := (W.getNat, oB.getNat)
    let ns ← getCurrNamespace
    let Bt ← resolveNatTable (← resolveGlobalConstNoOverload B)
    let rows := Bt.toList.map fun row =>
      (row.toList.zipIdx.foldl (fun acc (x, k) => acc + (x + 2 ^ (W - 1) - 2 ^ oB) * 2 ^ (W * k)) 0)
    addRawDef (ns ++ pre.getId) natListTy (mkNatListExpr rows)
  | _ => throwUnsupportedSyntax

/-- `x2_core_matmul_rows pre W p oA A Brows`: candidate packed rows of `A * B` (`A` by rows of offset
scalars, `B` by packed rows of `p` slots). -/
@[command_elab x2CoreMatmulRows] def elabX2CoreMatmulRows : CommandElab := fun stx => do
  match stx with
  | `(x2_core_matmul_rows $pre:ident $W:num $p:num $oA:num $A:ident $Br:ident) =>
    let (W, p, oA) := (W.getNat, p.getNat, oA.getNat)
    let ns ← getCurrNamespace
    let At ← resolveNatTable (← resolveGlobalConstNoOverload A)
    let br := (← resolveNatList (← constValue (← resolveGlobalConstNoOverload Br))).toList
    let outs := At.toList.map fun r => natAxpySpOut W p oA r.toList br
    addRawDef (ns ++ pre.getId) natListTy (mkNatListExpr outs)
  | _ => throwUnsupportedSyntax

/-- `x2_core_rowselect pre T sel`: the rows `T[sel[0]], T[sel[1]], ...` as a raw literal table. -/
@[command_elab x2CoreRowselect] def elabX2CoreRowselect : CommandElab := fun stx => do
  match stx with
  | `(x2_core_rowselect $pre:ident $T:ident $sel:ident) =>
    let ns ← getCurrNamespace
    let Tt ← resolveNatTable (← resolveGlobalConstNoOverload T)
    let sl := (← resolveNatList (← constValue (← resolveGlobalConstNoOverload sel))).toList
    let rows := sl.map fun i => mkNatListExpr (Tt[i]!).toList
    let val := rows.foldr (fun r acc => mkApp3 (mkConst ``List.cons [Level.zero]) natListTy r acc)
      (mkApp (mkConst ``List.nil [Level.zero]) natListTy)
    addRawDef (ns ++ pre.getId) (mkApp (mkConst ``List [Level.zero]) natListTy) val
  | _ => throwUnsupportedSyntax

/-- `x2_core_subtable pre T r c`: the first `r` rows and `c` columns of the table `T`, as raw
literals (test configurations of reduced size). -/
@[command_elab x2CoreSubtable] def elabX2CoreSubtable : CommandElab := fun stx => do
  match stx with
  | `(x2_core_subtable $pre:ident $T:ident $r:num $c:num) =>
    let ns ← getCurrNamespace
    let Tt ← resolveNatTable (← resolveGlobalConstNoOverload T)
    let rows := (Tt.toList.take r.getNat).map fun row => mkNatListExpr (row.toList.take c.getNat)
    let val := rows.foldr (fun r acc => mkApp3 (mkConst ``List.cons [Level.zero]) natListTy r acc)
      (mkApp (mkConst ``List.nil [Level.zero]) natListTy)
    addRawDef (ns ++ pre.getId) (mkApp (mkConst ``List [Level.zero]) natListTy) val
  | _ => throwUnsupportedSyntax

end ThreeCopyQutritWerner.X2
