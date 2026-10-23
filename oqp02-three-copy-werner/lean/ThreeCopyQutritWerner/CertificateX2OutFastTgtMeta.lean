module

public import ThreeCopyQutritWerner.CertificateX2OutFastTgt
public meta import ThreeCopyQutritWerner.CertificateX2OutFastTgt
public import ThreeCopyQutritWerner.CertificateX2OutFastMeta
public meta import ThreeCopyQutritWerner.CertificateX2OutFastMeta

public meta section


/-!
# Output stage: build-time candidates for the target chunk checks

`x2_out_tgt_lits pre W t₀ t₁ t₂ r Jd J`: for an h block of types `t₀ t₁ t₂` with `r` image columns, digit lists `Jd` and image columns `J`, defines `pre_LT :
List (List ℕ)`, entry `a` = the candidate output of the target chunk `a` (`x2FTOC`). Nothing here is trusted: every
literal enters a statement checked by the kernel (`x2FTOK`).
-/

namespace ThreeCopyQutritWerner.X2
open Lean Elab Command

/-- Columns of the target chunk `a` (the values of `x2FTXC` for a block of types `t₀ t₁ t₂`). -/
def xfFTXC (W : ℕ) (t0 t1 t2 : Fin 8) (a : ℕ) : List ℕ :=
  let m0 := x2Mult 0 t0
  let m1 := x2Mult 0 t1
  let m2 := x2Mult 0 t2
  let P0 := ((List.range m0).map fun y0 => packCol W m0 (fun x0 => x2TgtM t0 x0 y0)).toArray
  let M1 := ((List.range m1).map fun x1 => ((List.range m1).map fun y1 => x2TgtM t1 x1 y1).toArray).toArray
  let M2 := ((List.range m2).map fun y2 => x2TgtM t2 a y2).toArray
  (List.range m0).flatMap fun y0 => (List.range m1).flatMap fun y1 => (List.range m2).map fun y2 =>
    concatFibers W m0 (((List.range m1).map fun x1 =>
      scaleRun W m0 ((M1.getD x1 #[]).getD y1 0 * M2.getD y2 0) (P0.getD y0 0)).map (runOf W m0 0))

def xfFTOC (W : ℕ) (t0 t1 t2 : Fin 8) (r : ℕ) (Jd : List (List ℕ)) (J : List ℕ) (a : ℕ) : List ℕ :=
  let m0 := x2Mult 0 t0
  let m1 := x2Mult 0 t1
  let m2 := x2Mult 0 t2
  xfChunkOC W r (m1 * m0) Jd (xfFTXC W t0 t1 t2 a)
    (xfRows W m1 m2 J ((List.range m1).flatMap fun x1 => (List.range m0).map fun x0 => (x0, x1, a)))


syntax (name := x2OutTgtLitsCmd) "x2_out_tgt_lits " ident num num num num num ident ident : command

@[command_elab x2OutTgtLitsCmd] def elabX2OutTgtLits : CommandElab := fun stx => do
  match stx with
  | `(x2_out_tgt_lits $pre:ident $W:num $t0:num $t1:num $t2:num $r:num $jd:ident $jc:ident) =>
    let W := W.getNat
    let (t0, t1, t2) := (xfTy t0.getNat, xfTy t1.getNat, xfTy t2.getNat)
    let r := r.getNat
    let Jd := (← xfNatTableAux (← xfConstValue (← resolveGlobalConstNoOverload jd)) #[]).toList
    let J := (← xfNatListAux (← xfConstValue (← resolveGlobalConstNoOverload jc)) #[]).toList
    let LT := (List.range (x2Mult 0 t2)).map fun a => xfFTOC W t0 t1 t2 r Jd J a
    addRawDef ((← getCurrNamespace) ++ Name.mkSimple (pre.getId.toString ++ "_LT")) (xfListTy (xfListTy xfNatTy))
      (xfNatTableExpr LT)
  | _ => throwUnsupportedSyntax

end ThreeCopyQutritWerner.X2
