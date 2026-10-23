module

public import ThreeCopyQutritWerner.CertificateX2PackedLiteral
public meta import ThreeCopyQutritWerner.CertificateX2PackedLiteral
public import ThreeCopyQutritWerner.CertificateX2PackedNatAxpy
public meta import ThreeCopyQutritWerner.CertificateX2PackedNatAxpy

public meta section


/-! Packed engine: build-time generation of intermediate data.

`x2_stage_axpy out W L oA scalars fibers` reads the raw-literal constants `scalars : List (List ℕ)`
(offset scalars, one row per output) and `fibers : List ℕ` from the environment, computes each output
`(natDot row (natFibers W L fibers) + natAxpyCorr W L oA fibers) % 2^(W L)` in ordinary (meta) code,
and defines `out : List ℕ` as raw literals. Nothing is trusted: the generated values are only a
candidate, and `natAxpyCheck` (with `natAxpyCheck_sound`) checks every one in the kernel. Intermediate
tensors therefore never live in source files. -/

namespace ThreeCopyQutritWerner.X2
open Lean Elab Command

/-- The output a natural linear-combination check expects (computable). -/
def natAxpyOut (W L oA : ℕ) (as' Es : List ℕ) : ℕ :=
  (natDot as' (natFibers W L Es) + natAxpyCorr W L oA Es) % 2 ^ (W * L)

/-- Raw natural literals of a list term (`List.cons`/`List.nil` with literal heads). -/
partial def natListOfExpr (e : Expr) (acc : Array Nat := #[]) : Option (Array Nat) :=
  match e.getAppFnArgs with
  | (``List.nil, _) => some acc
  | (``List.cons, #[_, hd, tl]) =>
    match hd with
    | .lit (.natVal n) => natListOfExpr tl (acc.push n)
    | _ => none
  | _ => none

/-- Rows of a list-of-lists term of raw literals. -/
partial def natTableOfExpr (e : Expr) (acc : Array (List Nat) := #[]) : Option (Array (List Nat)) :=
  match e.getAppFnArgs with
  | (``List.nil, _) => some acc
  | (``List.cons, #[_, hd, tl]) =>
    match natListOfExpr hd with
    | some r => natTableOfExpr tl (acc.push r.toList)
    | none => none
  | _ => none

def constValue (n : Name) : CommandElabM Expr := do
  let some info := (← getEnv).find? n | throwError "unknown constant {n}"
  let some v := info.value? | throwError "constant {n} has no value"
  return v

def mkNatListExpr (xs : List Nat) : Expr :=
  let natTy := mkConst ``Nat
  xs.foldr (fun n acc => mkApp3 (mkConst ``List.cons [levelZero]) natTy (mkRawNatLit n) acc)
    (mkApp (mkConst ``List.nil [levelZero]) natTy)

syntax (name := x2StageAxpy) "x2_stage_axpy " ident num num num ident ident : command

@[command_elab x2StageAxpy] def elabX2StageAxpy : CommandElab := fun stx => do
  match stx with
  | `(x2_stage_axpy $out:ident $W:num $L:num $oA:num $sc:ident $fb:ident) =>
    let ns ← getCurrNamespace
    let scName ← resolveGlobalConstNoOverload sc
    let fbName ← resolveGlobalConstNoOverload fb
    let some rows := natTableOfExpr (← constValue scName)
      | throwError "scalars must be a list of lists of raw literals"
    let some fibs := natListOfExpr (← constValue fbName)
      | throwError "fibers must be a list of raw literals"
    let w := W.getNat
    let l := L.getNat
    let o := oA.getNat
    let outs := rows.toList.map fun r => natAxpyOut w l o r fibs.toList
    addRawDef (ns ++ out.getId) (mkApp (mkConst ``List [levelZero]) (mkConst ``Nat))
      (mkNatListExpr outs)
  | _ => throwUnsupportedSyntax

end ThreeCopyQutritWerner.X2
