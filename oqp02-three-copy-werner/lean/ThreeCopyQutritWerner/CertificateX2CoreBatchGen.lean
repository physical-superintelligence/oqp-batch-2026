module

public import ThreeCopyQutritWerner.CertificateX2CoreBatch
public meta import ThreeCopyQutritWerner.CertificateX2CoreBatch
public import ThreeCopyQutritWerner.CertificateX2CoreGen
public meta import ThreeCopyQutritWerner.CertificateX2CoreGen

public meta section


/-!
# Contraction core: build-time generation for the batched stages

Candidates only; the kernel re-checks every generated value (`regroupOK`, `slotCheck`).
* `x2_core_regroup pre W n B G J lo hi`: rows `pre_K'` (`lo ≤ K' < hi`) of the regrouped table,
  entry `b < J` = `regroupFiber W n B G K' b`.
* `x2_core_stageC_sub pre W n m B Cs O J tj tk lo hi`: rows `pre_k` (`lo ≤ k < hi`), entry `j < J` =
  the slot contraction of the sub-fiber `runOf W n ((k % B) n) (O[k / B][j])` against the packed
  columns `Cs` (`m` slots) when `tj[j] ≤ tk[k]`, else `0`.
* `x2_nat_rawlist name n₁ n₂ ...`: a list of naturals as a raw literal (long `[...]` literals elaborate
  to `have` chains, which the generators do not read).
Batched axis-2 and axis-1 stages use `x2_core_stageA_rows` with `L = B n`.
-/

namespace ThreeCopyQutritWerner.X2
open Lean Elab Command

syntax (name := x2CoreRegroup) "x2_core_regroup " ident num num num ident num num num : command
syntax (name := x2NatRawList) "x2_nat_rawlist " ident num* : command
syntax (name := x2CoreStageCSub) "x2_core_stageC_sub " ident num num num num ident ident num ident ident num num : command

@[command_elab x2NatRawList] def elabX2NatRawList : CommandElab := fun stx => do
  match stx with
  | `(x2_nat_rawlist $pre:ident $xs:num*) =>
    let ns ← getCurrNamespace
    addRawDef (ns ++ pre.getId) natListTy (mkNatListExpr (xs.toList.map (·.getNat)))
  | _ => throwUnsupportedSyntax

@[command_elab x2CoreRegroup] def elabX2CoreRegroup : CommandElab := fun stx => do
  match stx with
  | `(x2_core_regroup $pre:ident $W:num $n:num $B:num $G:ident $J:num $lo:num $hi:num) =>
    let (W, n, B, J) := (W.getNat, n.getNat, B.getNat, J.getNat)
    let ns ← getCurrNamespace
    let Gt ← resolveNatTable (← resolveGlobalConstNoOverload G)
    let mask := 2 ^ (W * n) - 1
    for kc in [lo.getNat:hi.getNat] do
      let row := (List.range J).map fun b =>
        concatFibers W n ((List.range B).map fun q =>
          ((Gt[b / B]!)[kc * B + q]! >>> (W * ((b % B) * n))) &&& mask)
      addRawDef (ns ++ rowName pre.getId kc) natListTy (mkNatListExpr row)
  | _ => throwUnsupportedSyntax

@[command_elab x2CoreStageCSub] def elabX2CoreStageCSub : CommandElab := fun stx => do
  match stx with
  | `(x2_core_stageC_sub $pre:ident $W:num $n:num $m:num $B:num $Cs:ident $O:ident $J:num $tj:ident
      $tk:ident $lo:num $hi:num) =>
    let (W, n, m, B, J) := (W.getNat, n.getNat, m.getNat, B.getNat, J.getNat)
    let ns ← getCurrNamespace
    let cs := (← resolveNatList (← constValue (← resolveGlobalConstNoOverload Cs))).toList
    let csF := natFibers W m cs
    let corr := natAxpyCorr W m (W - 1) cs
    let Ot ← resolveNatTable (← resolveGlobalConstNoOverload O)
    let tjs ← resolveNatList (← constValue (← resolveGlobalConstNoOverload tj))
    let tks ← resolveNatList (← constValue (← resolveGlobalConstNoOverload tk))
    let mask := 2 ^ (W * n) - 1
    for k in [lo.getNat:hi.getNat] do
      let outs := (List.range J).map fun j =>
        if tjs.getD j 0 ≤ tks.getD k 0 then
          slotOutPre W n m csF corr (((Ot[k / B]!)[j]! >>> (W * ((k % B) * n))) &&& mask)
        else 0
      addRawDef (ns ++ rowName pre.getId k) natListTy (mkNatListExpr outs)
  | _ => throwUnsupportedSyntax

end ThreeCopyQutritWerner.X2
