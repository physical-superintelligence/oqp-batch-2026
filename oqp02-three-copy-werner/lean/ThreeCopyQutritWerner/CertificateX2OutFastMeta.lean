module

public import ThreeCopyQutritWerner.CertificateX2OutFast
public meta import ThreeCopyQutritWerner.CertificateX2OutFast
public import ThreeCopyQutritWerner.CertificateX2PackedLiteral
public meta import ThreeCopyQutritWerner.CertificateX2PackedLiteral

public meta section


/-!
# Output stage: build-time candidates for the chunk checks

Commands that compute candidate literals in ordinary (meta) code and define them as raw kernel literals. Nothing here is
trusted: every literal enters a statement that the kernel checks (`x2F0OK`, `x2F1OK`, `x2F2OK`, `xf_jd_ok`).

* `x2_out_jd name J r N`: `name : List (List ℕ)` = the digit lists `digs 11 N (J.getD c 0)`, `c < r`, of the packed image
  columns `J` (a raw literal list).
* `x2_out_lits pre W t₀ t₁ t₂ r TS TA Jd J`: for an h block of types `t₀ t₁ t₂` with `r` image columns, tables `TS`,
  `TA` (row tables whose rows are raw literals or constant references), digit lists `Jd` and image columns `J`, defines
  `pre_L0`, `pre_L1`, `pre_L2 : List (List ℕ)`: entry `a` = the candidate output of the part-`P` chunk `a` (the values
  of `x2F0OC`, `x2F1OC`, `x2F2OC`, computed without the block tables, see below).
* `x2_out_slab pre "file" K0 nK J0 nJ R`: test tables from a slab data file (fiber of row `K0 + k`, entry `J0 + j` on line
  `k nJ + j`): rows `pre_0 .. pre_(R-1)` (rows outside the slab empty, entries before `J0` zero) and `pre`.
-/

namespace ThreeCopyQutritWerner.X2
open Lean Elab Command

/-- A natural number term: raw literal or `OfNat.ofNat` numeral. -/
def xfNatOfExpr? (e : Expr) : Option Nat :=
  match e with
  | .lit (.natVal n) => some n
  | _ =>
    match e.getAppFnArgs with
    | (``OfNat.ofNat, #[_, .lit (.natVal n), _]) => some n
    | _ => none

/-- The value of a definition. -/
def xfConstValue (n : Name) : CommandElabM Expr := do
  match (← getEnv).find? n with
  | some (.defnInfo d) => return d.value
  | some (.thmInfo d) => return d.value
  | _ => throwError "x2_out: no definition {n}"

/-- Elements of a list term of naturals (cons cells may be constant references). -/
partial def xfNatListAux (e : Expr) (acc : Array Nat) : CommandElabM (Array Nat) := do
  match e.getAppFnArgs with
  | (``List.nil, _) => return acc
  | (``List.cons, #[_, hd, tl]) =>
    match xfNatOfExpr? hd with
    | some n => xfNatListAux tl (acc.push n)
    | none => throwError "x2_out: not a natural literal: {hd}"
  | _ =>
    match e with
    | .const c _ => xfNatListAux (← xfConstValue c) acc
    | _ => throwError "x2_out: not a list of naturals: {e}"

/-- Rows of a table term (rows may be constant references). -/
partial def xfNatTableAux (e : Expr) (acc : Array (List Nat)) : CommandElabM (Array (List Nat)) := do
  match e.getAppFnArgs with
  | (``List.nil, _) => return acc
  | (``List.cons, #[_, hd, tl]) => xfNatTableAux tl (acc.push (← xfNatListAux hd #[]).toList)
  | _ =>
    match e with
    | .const c _ => xfNatTableAux (← xfConstValue c) acc
    | _ => throwError "x2_out: not a table: {e}"

def xfNatTy : Expr := mkConst ``Nat
def xfListTy (ty : Expr) : Expr := mkApp (mkConst ``List [levelZero]) ty

/-- A list term from element terms. -/
def xfMkList (ty : Expr) (xs : List Expr) : Expr :=
  xs.foldr (fun x acc => mkApp3 (mkConst ``List.cons [levelZero]) ty x acc) (mkApp (mkConst ``List.nil [levelZero]) ty)

def xfNatListExpr (xs : List Nat) : Expr := xfMkList xfNatTy (xs.map mkRawNatLit)

def xfNatTableExpr (rows : List (List Nat)) : Expr := xfMkList (xfListTy xfNatTy) (rows.map xfNatListExpr)

/-! ### Build-time candidates without recomputation (compiled code does not share subterms)

Same values as `x2F0OC`, `x2F1OC`, `x2F2OC`, `x2FTOC` (the kernel recomputes them in the checks), with the triangles
of each table row, the combined sub-fibers of each column group and the natural axpy data computed once. -/

/-- `x2ChunkOC` with the shifted fibers and the correction of the `Y` stage computed once. -/
def xfChunkOC (W r L : ℕ) (Jd : List (List ℕ)) (XC JR : List ℕ) : List ℕ :=
  let XF := natFibers W L XC
  let XK := natAxpyCorr W L 10 XC
  let JF := natFibers W r JR
  let JK := natAxpyCorr W r (W - 1) JR
  let maskL := 2 ^ (W * L) - 1
  let maskR := 2 ^ (W * r) - 1
  (List.range r).map fun c' =>
    let Y := Nat.land (natDot (Jd.getD c' []) XF + XK) maskL
    Nat.land (natDot (digs W L Y) JF + JK) maskR

/-! Block data enter the build-time code as explicit types `t₀ t₁ t₂` and column count `r`: compiled code evaluates
`![...]` lookups strictly (exponential in the index), so the 414-entry block tables (`x2KeyTypes`, `x2KeySize`) must not
be evaluated here; the 8-entry type tables (`x2Mult`, `x2SOff`, `x2AOff`, `x2UOff0`) are cheap. -/

/-- Image rows `jRowF` at the ambient points `(x₀, x₁, x₂)` listed by `pts` (flat index with `m₁`, `m₂`). -/
def xfRows (W m1 m2 : ℕ) (J : List ℕ) (pts : List (ℕ × ℕ × ℕ)) : List ℕ :=
  pts.map fun p => jRowF W J ((p.1 * m1 + p.2.1) * m2 + p.2.2)

/-- Columns of the part-0 chunk `a` (the values of `x2F0XC` for a block of types `t₀ t₁ t₂`). -/
def xfF0XC (W : ℕ) (t0 t1 t2 : Fin 8) (TS TA : List (List ℕ)) (a : ℕ) : List ℕ :=
  let m0 := x2Mult 0 t0
  let m1 := x2Mult 0 t1
  let m2 := x2Mult 0 t2
  let u0 := x2UOff0 t0
  let RS := ((List.range m2).map fun y2 => triSOf W (m0 * m0) u0 t1 TS (x2SIdx 0 t2 a y2)).toArray
  let RA := ((List.range m2).map fun y2 => triAOf W (m0 * m0) u0 t1 TA (x2AIdx 0 t2 a y2)).toArray
  let G := ((List.range m2).map fun y2 => ((List.range m1).map fun y1 =>
      (List.range m1).map fun x1 => runComb W (m0 * m0) (triS (RS.getD y2 []) x1 y1) (triA (RA.getD y2 []) x1 y1)
        (sgnZ x1 y1 * sgnZ a y2)).toArray).toArray
  (List.range m0).flatMap fun y0 => (List.range m1).flatMap fun y1 => (List.range m2).map fun y2 =>
    concatFibers W m0 ((((G.getD y2 #[]).getD y1 [])).map (runOf W m0 (y0 * m0)))

def xfF1XC (W : ℕ) (t0 t1 t2 : Fin 8) (TA : List (List ℕ)) (a : ℕ) : List ℕ :=
  let m0 := x2Mult 0 t0
  let m1 := x2Mult 0 t1
  let m2 := x2Mult 0 t2
  let u1 := x2UOff0 t1
  let RA := ((List.range m2).map fun y2 => triAOf W (m1 * m1) u1 t0 TA (x2AIdx 0 t2 a y2)).toArray
  let off := offset W (W - 1) (m1 * m1)
  let G := ((List.range m2).map fun y2 => ((List.range m0).map fun y0 =>
      (List.range m0).map fun x0 => runComb W (m1 * m1) off (triA (RA.getD y2 []) x0 y0) (sgnZ x0 y0 * sgnZ a y2)).toArray).toArray
  (List.range m0).flatMap fun y0 => (List.range m1).flatMap fun y1 => (List.range m2).map fun y2 =>
    concatFibers W m1 ((((G.getD y2 #[]).getD y0 [])).map (runOf W m1 (y1 * m1)))

def xfF2XC (W : ℕ) (t0 t1 t2 : Fin 8) (TA : List (List ℕ)) (a : ℕ) : List ℕ :=
  let m0 := x2Mult 0 t0
  let m1 := x2Mult 0 t1
  let m2 := x2Mult 0 t2
  let u2 := x2UOff0 t2
  let RA := ((List.range m1).map fun y1 => triAOf W (m2 * m2) u2 t0 TA (x2AIdx 0 t1 a y1)).toArray
  let off := offset W (W - 1) (m2 * m2)
  let G := ((List.range m1).map fun y1 => ((List.range m0).map fun y0 =>
      (List.range m0).map fun x0 => runComb W (m2 * m2) off (triA (RA.getD y1 []) x0 y0) (sgnZ x0 y0 * sgnZ a y1)).toArray).toArray
  (List.range m0).flatMap fun y0 => (List.range m1).flatMap fun y1 => (List.range m2).map fun y2 =>
    concatFibers W m2 ((((G.getD y1 #[]).getD y0 [])).map (runOf W m2 (y2 * m2)))

def xfF0OC (W : ℕ) (t0 t1 t2 : Fin 8) (r : ℕ) (TS TA : List (List ℕ)) (Jd : List (List ℕ)) (J : List ℕ) (a : ℕ) :
    List ℕ :=
  let m0 := x2Mult 0 t0
  let m1 := x2Mult 0 t1
  let m2 := x2Mult 0 t2
  xfChunkOC W r (m1 * m0) Jd (xfF0XC W t0 t1 t2 TS TA a)
    (xfRows W m1 m2 J ((List.range m1).flatMap fun x1 => (List.range m0).map fun x0 => (x0, x1, a)))

def xfF1OC (W : ℕ) (t0 t1 t2 : Fin 8) (r : ℕ) (TA : List (List ℕ)) (Jd : List (List ℕ)) (J : List ℕ) (a : ℕ) :
    List ℕ :=
  let m0 := x2Mult 0 t0
  let m1 := x2Mult 0 t1
  let m2 := x2Mult 0 t2
  xfChunkOC W r (m0 * m1) Jd (xfF1XC W t0 t1 t2 TA a)
    (xfRows W m1 m2 J ((List.range m0).flatMap fun x0 => (List.range m1).map fun x1 => (x0, x1, a)))

def xfF2OC (W : ℕ) (t0 t1 t2 : Fin 8) (r : ℕ) (TA : List (List ℕ)) (Jd : List (List ℕ)) (J : List ℕ) (a : ℕ) :
    List ℕ :=
  let m0 := x2Mult 0 t0
  let m1 := x2Mult 0 t1
  let m2 := x2Mult 0 t2
  xfChunkOC W r (m0 * m2) Jd (xfF2XC W t0 t1 t2 TA a)
    (xfRows W m1 m2 J ((List.range m0).flatMap fun x0 => (List.range m2).map fun x2 => (x0, a, x2)))

/-- A type index. -/
def xfTy (t : ℕ) : Fin 8 := ⟨t % 8, Nat.mod_lt _ (by decide)⟩

/-- The h block with index `i`. -/
def xfKey (i : ℕ) : x2Key 0 := ⟨i % x2NumKeys 0, Nat.mod_lt _ (by decide)⟩

syntax (name := x2OutJdCmd) "x2_out_jd " ident ident num num : command
syntax (name := x2OutLitsCmd) "x2_out_lits " ident num num num num num ident ident ident ident : command
syntax (name := x2OutLitsPartCmd) "x2_out_lits_part " ident num num num num num num ident ident ident ident : command
syntax (name := x2OutSlabCmd) "x2_out_slab " ident str num num num num num : command

@[command_elab x2OutJdCmd] def elabX2OutJd : CommandElab := fun stx => do
  match stx with
  | `(x2_out_jd $nm:ident $jc:ident $r:num $n:num) =>
    let cols := (← xfNatListAux (← xfConstValue (← resolveGlobalConstNoOverload jc)) #[]).toList
    let rows := (List.range r.getNat).map fun c => digs 11 n.getNat (cols.getD c 0)
    addRawDef ((← getCurrNamespace) ++ nm.getId) (xfListTy (xfListTy xfNatTy)) (xfNatTableExpr rows)
  | _ => throwUnsupportedSyntax

@[command_elab x2OutLitsCmd] def elabX2OutLits : CommandElab := fun stx => do
  match stx with
  | `(x2_out_lits $pre:ident $W:num $t0:num $t1:num $t2:num $r:num $ts:ident $ta:ident $jd:ident $jc:ident) =>
    let W := W.getNat
    let (t0, t1, t2) := (xfTy t0.getNat, xfTy t1.getNat, xfTy t2.getNat)
    let r := r.getNat
    let TS := (← xfNatTableAux (← xfConstValue (← resolveGlobalConstNoOverload ts)) #[]).toList
    let TA := (← xfNatTableAux (← xfConstValue (← resolveGlobalConstNoOverload ta)) #[]).toList
    let Jd := (← xfNatTableAux (← xfConstValue (← resolveGlobalConstNoOverload jd)) #[]).toList
    let J := (← xfNatListAux (← xfConstValue (← resolveGlobalConstNoOverload jc)) #[]).toList
    let ns ← getCurrNamespace
    let L0 := (List.range (x2Mult 0 t2)).map fun a => xfF0OC W t0 t1 t2 r TS TA Jd J a
    addRawDef (ns ++ Name.mkSimple (pre.getId.toString ++ "_L0")) (xfListTy (xfListTy xfNatTy)) (xfNatTableExpr L0)
    let L1 := (List.range (x2Mult 0 t2)).map fun a => xfF1OC W t0 t1 t2 r TA Jd J a
    addRawDef (ns ++ Name.mkSimple (pre.getId.toString ++ "_L1")) (xfListTy (xfListTy xfNatTy)) (xfNatTableExpr L1)
    let L2 := (List.range (x2Mult 0 t1)).map fun a => xfF2OC W t0 t1 t2 r TA Jd J a
    addRawDef (ns ++ Name.mkSimple (pre.getId.toString ++ "_L2")) (xfListTy (xfListTy xfNatTy)) (xfNatTableExpr L2)
  | _ => throwUnsupportedSyntax

/-- `x2_out_lits_part pre P W t₀ t₁ t₂ r TS TA Jd J`: only `pre_L<P>` (for modules holding one part's chunks). -/
@[command_elab x2OutLitsPartCmd] def elabX2OutLitsPart : CommandElab := fun stx => do
  match stx with
  | `(x2_out_lits_part $pre:ident $P:num $W:num $t0:num $t1:num $t2:num $r:num $ts:ident $ta:ident $jd:ident $jc:ident) =>
    let W := W.getNat
    let (t0, t1, t2) := (xfTy t0.getNat, xfTy t1.getNat, xfTy t2.getNat)
    let r := r.getNat
    let P := P.getNat
    let TS ← if P == 0 then do
        let v ← xfConstValue (← resolveGlobalConstNoOverload ts)
        let rows ← xfNatTableAux v #[]
        pure rows.toList
      else pure []
    let TA := (← xfNatTableAux (← xfConstValue (← resolveGlobalConstNoOverload ta)) #[]).toList
    let Jd := (← xfNatTableAux (← xfConstValue (← resolveGlobalConstNoOverload jd)) #[]).toList
    let J := (← xfNatListAux (← xfConstValue (← resolveGlobalConstNoOverload jc)) #[]).toList
    let L := if P == 0 then (List.range (x2Mult 0 t2)).map fun a => xfF0OC W t0 t1 t2 r TS TA Jd J a
      else if P == 1 then (List.range (x2Mult 0 t2)).map fun a => xfF1OC W t0 t1 t2 r TA Jd J a
      else (List.range (x2Mult 0 t1)).map fun a => xfF2OC W t0 t1 t2 r TA Jd J a
    addRawDef ((← getCurrNamespace) ++ Name.mkSimple (pre.getId.toString ++ "_L" ++ toString P))
      (xfListTy (xfListTy xfNatTy)) (xfNatTableExpr L)
  | _ => throwUnsupportedSyntax

@[command_elab x2OutSlabCmd] def elabX2OutSlab : CommandElab := fun stx => do
  match stx with
  | `(x2_out_slab $pre:ident $path:str $k0:num $nk:num $j0:num $nj:num $R:num) =>
    let vals := (← readHexNats path.getString).toArray
    let (k0, nk, j0, nj, R) := (k0.getNat, nk.getNat, j0.getNat, nj.getNat, R.getNat)
    let ns ← getCurrNamespace
    let rowName := fun (k : Nat) => ns ++ Name.mkSimple (pre.getId.toString ++ "_" ++ toString k)
    for k in [0:R] do
      let row : List Nat :=
        if k0 ≤ k ∧ k < k0 + nk then
          (List.range (j0 + nj)).map fun j => if j0 ≤ j then vals.getD ((k - k0) * nj + (j - j0)) 0 else 0
        else []
      addRawDef (rowName k) (xfListTy xfNatTy) (xfNatListExpr row)
    let rows := (List.range R).map fun k => mkConst (rowName k)
    addRawDef (ns ++ pre.getId) (xfListTy (xfListTy xfNatTy)) (xfMkList (xfListTy xfNatTy) rows)
  | _ => throwUnsupportedSyntax

syntax (name := x2OutSynthCmd) "x2_out_synth " ident num num num num num num num num : command

/-- Divide-and-conquer concatenation of 64-bit words `w (i₀ + i)`, `i < n`. -/
partial def xfWords (w : Nat → Nat) (i0 n : Nat) : Nat :=
  if n ≤ 16 then (List.range n).foldr (fun i acc => (acc <<< 64) + w (i0 + i)) 0
  else
    let h := n / 2
    xfWords w i0 h + (xfWords w (i0 + h) (n - h) <<< (64 * h))

/-- `x2_out_synth pre R C k0 nk j0 nj bits seed`: synthetic test tables (W = 384, 513 slots): rows `pre_k`, `k < R`;
row `k ∈ [k0, k0 + nk)` has `j0 + nj` entries (zero before `j0`), the others are empty; entries in `[-2^bits, 2^bits)`. -/
@[command_elab x2OutSynthCmd] def elabX2OutSynth : CommandElab := fun stx => do
  match stx with
  | `(x2_out_synth $pre:ident $R:num $cc:num $k0:num $nk:num $j0:num $nj:num $bits:num $seed:num) =>
    let _ := cc
    let (R, k0, nk, j0, nj, bits, seed) := (R.getNat, k0.getNat, nk.getNat, j0.getNat, nj.getNat, bits.getNat, seed.getNat)
    let W := 384
    let Ls := 513
    let fb := W * Ls
    let words := (fb + 64 * 65536) / 64
    let lcg := fun (i : Nat) => ((i + seed + 1) * 6364136223846793005 + 1442695040888963407) % 18446744073709551616
    let big := xfWords lcg 0 words
    let bigBits := 64 * words
    let rep := repunit W Ls
    let mask := (2 ^ (bits + 1) - 1) * rep
    let base := offset W (W - 1) Ls - 2 ^ bits * rep
    let ns ← getCurrNamespace
    let rowName := fun (k : Nat) => ns ++ Name.mkSimple (pre.getId.toString ++ "_" ++ toString k)
    for k in [0:R] do
      let row : List Nat :=
        if k0 ≤ k ∧ k < k0 + nk then
          (List.range (j0 + nj)).map fun j =>
            if j0 ≤ j then
              let sh := ((k * 997 + j * 131 + seed) * 64) % (bigBits - fb)
              base + ((big >>> sh) &&& mask)
            else 0
        else []
      addRawDef (rowName k) (xfListTy xfNatTy) (xfNatListExpr row)
    let rows := (List.range R).map fun k => mkConst (rowName k)
    addRawDef (ns ++ pre.getId) (xfListTy (xfListTy xfNatTy)) (xfMkList (xfListTy xfNatTy) rows)
  | _ => throwUnsupportedSyntax

/-- The digit lists of the image columns, from a kernel check of their equality with `digs`. -/
theorem xf_jd_ok (Jd : List (List ℕ)) (Jcols : List ℕ) (r N : ℕ)
    (h : Jd = (List.range r).map fun c => digs 11 N (Jcols.getD c 0)) :
    ∀ c < r, Jd.getD c [] = digs 11 N (Jcols.getD c 0) := by
  intro c hc
  rw [h, List.getD_eq_getElem _ _ (by simpa using hc), List.getElem_map, List.getElem_range]

end ThreeCopyQutritWerner.X2
