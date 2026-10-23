module

public import Lean
public meta import Lean

public meta section


/-! Packed engine: direct data transport for packed naturals.

`x2_nat_list name "path"` defines `name : List ℕ`, and `x2_nat_defs pre "path"` defines
`pre_0, pre_1, ... : ℕ`, from a file of hexadecimal naturals (one per line, optional `0x`;
path relative to the package root). The values become raw kernel literals directly: no
numeral is elaborated as a term. The file only selects which term is defined; it supplies no
theorem or proof, and every statement about the data is checked by the kernel. -/

namespace ThreeCopyQutritWerner.X2
open Lean Elab Command

/-- Value of one hexadecimal digit (other characters count as `0`). -/
def hexDigitVal (c : Char) : Nat :=
  if '0' ≤ c ∧ c ≤ '9' then c.toNat - '0'.toNat
  else if 'a' ≤ c ∧ c ≤ 'f' then c.toNat - 'a'.toNat + 10
  else if 'A' ≤ c ∧ c ≤ 'F' then c.toNat - 'A'.toNat + 10
  else 0

/-- Divide-and-conquer conversion of the hexadecimal digits `a[i, j)`. -/
partial def hexArr (a : Array Char) (i j : Nat) : Nat :=
  if j ≤ i + 64 then
    (List.range (j - i)).foldl (fun acc k => acc * 16 + hexDigitVal (a.getD (i + k) '0')) 0
  else
    let m := (i + j) / 2
    (hexArr a i m <<< (4 * (j - m))) + hexArr a m j

/-- Whether a character is a hexadecimal digit. -/
def isHexChar (c : Char) : Bool :=
  ('0' ≤ c && c ≤ '9') || ('a' ≤ c && c ≤ 'f') || ('A' ≤ c && c ≤ 'F')

/-- Split text into lines of hexadecimal digits (other characters ignored, so an `0x` prefix
only adds a leading zero) and convert each nonempty line. -/
def parseHexLines (text : String) : List Nat :=
  let step := fun (st : Array Nat × Array Char) (c : Char) =>
    if c == '\n' then
      if st.2.size == 0 then st else (st.1.push (hexArr st.2 0 st.2.size), #[])
    else if isHexChar c then (st.1, st.2.push c) else st
  let st := text.foldl step (#[], #[])
  let st := if st.2.size == 0 then st else (st.1.push (hexArr st.2 0 st.2.size), #[])
  st.1.toList

/-- Read the naturals of a hexadecimal data file (path relative to the package root). -/
def readHexNats (path : String) : CommandElabM (List Nat) := do
  let file := System.FilePath.mk (← getFileName)
  let root := (file.parent.bind (·.parent)).getD "."
  let p := System.FilePath.mk path
  let full := if p.isAbsolute then p else root / p
  let text ← IO.FS.readFile full
  return parseHexLines text

/-- Add a noncomputable definition with a closed value. -/
def addRawDef (declName : Name) (ty val : Expr) : CommandElabM Unit := do
  liftCoreM <| addDecl (forceExpose := true) <| Declaration.defnDecl {
    name := declName, levelParams := [], type := ty, value := val,
    hints := ReducibilityHints.abbrev, safety := DefinitionSafety.safe }
  modifyEnv (addNoncomputable · declName)

/-- Split text into lines, and each line into hexadecimal naturals separated by any
non-hexadecimal character other than `x` (so `0x` prefixes are harmless). -/
def parseHexTable (text : String) : List (List Nat) :=
  let flush := fun (row : Array Nat) (cur : Array Char) =>
    if cur.size == 0 then row else row.push (hexArr cur 0 cur.size)
  let step := fun (st : Array (List Nat) × Array Nat × Array Char) (c : Char) =>
    if c == '\n' then
      let row := flush st.2.1 st.2.2
      if row.size == 0 then (st.1, #[], #[]) else (st.1.push row.toList, #[], #[])
    else if isHexChar c then (st.1, st.2.1, st.2.2.push c)
    else if c == 'x' then st
    else (st.1, flush st.2.1 st.2.2, #[])
  let st := text.foldl step (#[], #[], #[])
  let row := flush st.2.1 st.2.2
  let st1 := if row.size == 0 then st.1 else st.1.push row.toList
  st1.toList

syntax (name := x2NatList) "x2_nat_list " ident str : command
syntax (name := x2NatTable) "x2_nat_table " ident str : command
syntax (name := x2NatDefs) "x2_nat_defs " ident str : command

@[command_elab x2NatList] def elabX2NatList : CommandElab := fun stx => do
  match stx with
  | `(x2_nat_list $id:ident $path:str) =>
    let vals ← readHexNats path.getString
    let natTy := mkConst ``Nat
    let nil := mkApp (mkConst ``List.nil [levelZero]) natTy
    let val := vals.foldr (fun n acc =>
      mkApp3 (mkConst ``List.cons [levelZero]) natTy (mkRawNatLit n) acc) nil
    addRawDef ((← getCurrNamespace) ++ id.getId) (mkApp (mkConst ``List [levelZero]) natTy) val
  | _ => throwUnsupportedSyntax

@[command_elab x2NatTable] def elabX2NatTable : CommandElab := fun stx => do
  match stx with
  | `(x2_nat_table $id:ident $path:str) =>
    let file := System.FilePath.mk (← getFileName)
    let root := (file.parent.bind (·.parent)).getD "."
    let p := System.FilePath.mk path.getString
    let full := if p.isAbsolute then p else root / p
    let rows := parseHexTable (← IO.FS.readFile full)
    let natTy := mkConst ``Nat
    let listTy := mkApp (mkConst ``List [levelZero]) natTy
    let mkList := fun (ty : Expr) (xs : List Expr) =>
      xs.foldr (fun x acc => mkApp3 (mkConst ``List.cons [levelZero]) ty x acc)
        (mkApp (mkConst ``List.nil [levelZero]) ty)
    let val := mkList listTy (rows.map fun r => mkList natTy (r.map mkRawNatLit))
    addRawDef ((← getCurrNamespace) ++ id.getId) (mkApp (mkConst ``List [levelZero]) listTy) val
  | _ => throwUnsupportedSyntax

@[command_elab x2NatDefs] def elabX2NatDefs : CommandElab := fun stx => do
  match stx with
  | `(x2_nat_defs $id:ident $path:str) =>
    let vals ← readHexNats path.getString
    let ns ← getCurrNamespace
    let mut k := 0
    for n in vals do
      addRawDef (ns ++ Name.mkSimple (id.getId.toString ++ "_" ++ toString k)) (mkConst ``Nat)
        (mkRawNatLit n)
      k := k + 1
  | _ => throwUnsupportedSyntax

end ThreeCopyQutritWerner.X2
