module

public import ThreeCopyQutritWerner.CertificateX2CoreBatchGen
public meta import ThreeCopyQutritWerner.CertificateX2CoreBatchGen

public meta section


/-!
# Contraction core: input super-fibers from exact offline data

`x2_core_f0_bin pre W n B kind "path" WD r C` defines `pre_r`, super-row `r` of the core's input
table: entry `c < C` is the super-fiber of the fibers `(j, c)`, `j = r B + q`, `q < B` (slot `q n + i`
holds the value at `(i, j, c)` plus `2^(W-1)`), read from a binary file of symmetry-reduced exact
values (entries of `WD` bits, value plus `2^(WD-1)`, little-endian):
* `kind = 0` (S tensor, symmetric in its three labels): entry `(a, b, d)`, `a ≤ b ≤ d < 282`, at
  position `d (d+1) (d+2) / 6 + b (b+1) / 2 + a`;
* `kind = 1` (A tensor, symmetric in its two A-labels): entry `(l₀, m₁, m₂)`, `m₁ ≤ m₂ < 231`, at
  position `l₀ 26796 + m₂ (m₂+1) / 2 + m₁`.
The values are build-time data: the core proves the transfer of whatever table is generated, and the
input stage (the hypothesis `hT0` of the transfer theorems) identifies it with
the bridge's `x2EmbedS`/`x2EmbedA`.
-/

namespace ThreeCopyQutritWerner.X2
open Lean Elab Command

/-- Little-endian bytes `a[i, j)` as a natural (divide and conquer). -/
partial def bytesNatLE (a : ByteArray) (i j : Nat) : Nat :=
  if j - i ≤ 32 then
    (List.range (j - i)).foldr (fun k acc => acc * 256 + (a.get! (i + k)).toNat) 0
  else
    let m := i + (j - i) / 2
    bytesNatLE a i m + (bytesNatLE a m j <<< (8 * (m - i)))

/-- Position of the S entry at the sorted labels of `(i, j, c)`. -/
def symIdxS (i j c : Nat) : Nat :=
  let x := min i j
  let y := max i j
  let a := min x c
  let d := max y c
  let b := i + j + c - a - d
  d * (d + 1) * (d + 2) / 6 + b * (b + 1) / 2 + a

/-- Position of the A entry `(i; j, c)` (A-labels unordered). -/
def symIdxA (i j c : Nat) : Nat :=
  let m := min j c
  let M := max j c
  i * 26796 + M * (M + 1) / 2 + m

syntax (name := x2CoreF0Bin) "x2_core_f0_bin " ident num num num num str num num num : command

@[command_elab x2CoreF0Bin] def elabX2CoreF0Bin : CommandElab := fun stx => do
  match stx with
  | `(x2_core_f0_bin $pre:ident $W:num $n:num $B:num $kind:num $path:str $WD:num $r:num $C:num) =>
    let (W, n, B, kind, WD, r, C) :=
      (W.getNat, n.getNat, B.getNat, kind.getNat, WD.getNat, r.getNat, C.getNat)
    unless W % 8 == 0 && WD % 8 == 0 && WD < W do throwError "x2_core_f0_bin: widths"
    let file := System.FilePath.mk (← getFileName)
    let root := (file.parent.bind (·.parent)).getD "."
    let p := System.FilePath.mk path.getString
    let full := if p.isAbsolute then p else root / p
    let data ← IO.FS.readBinFile full
    let wb := W / 8
    let db := WD / 8
    let L := B * n
    let corr := (2 ^ (W - 1) - 2 ^ (WD - 1)) * repunit W L
    let mut row : Array Nat := #[]
    for c in [0:C] do
      let mut buf := ByteArray.mk (Array.replicate (L * wb) 0)
      for q in [0:B] do
        let j := r * B + q
        for i in [0:n] do
          let idx := if kind == 0 then symIdxS i j c else symIdxA i j c
          unless db * (idx + 1) ≤ data.size do throwError "x2_core_f0_bin: index {idx} out of the file"
          buf := data.copySlice (db * idx) buf ((q * n + i) * wb) db
      row := row.push (bytesNatLE buf 0 buf.size + corr)
    addRawDef ((← getCurrNamespace) ++ rowName pre.getId r) natListTy (mkNatListExpr row.toList)
  | _ => throwUnsupportedSyntax

/-! ### The same data through Lean constants (chunks loaded in separate builds) -/

/-- The `k` slots (width `w`) of a packed natural, appended to `acc` (divide and conquer). -/
partial def unpackSlots (P w k : Nat) (acc : Array Nat) : Array Nat :=
  if k ≤ 8 then
    ((List.range k).foldl (fun (st : Array Nat × Nat) _ => (st.1.push (st.2 % 2 ^ w), st.2 >>> w))
      (acc, P)).1
  else
    let h := k / 2
    unpackSlots (P >>> (w * h)) w (k - h) (unpackSlots (P % 2 ^ (w * h)) w h acc)

/-- The packed natural with slots `xs[lo, hi)` (slot `lo` lowest; divide and conquer). -/
partial def packSlots (xs : Array Nat) (w lo hi : Nat) : Nat :=
  if hi - lo ≤ 8 then
    (List.range (hi - lo)).foldr (fun k acc => (acc <<< w) + xs[lo + k]!) 0
  else
    let m := lo + (hi - lo) / 2
    packSlots xs w lo m + (packSlots xs w m hi <<< (w * (m - lo)))

/-- `x2_t0_chunk name kind "path" WD lo hi`: rows `lo ≤ r < hi` of a binary chunk file as a table
of packed naturals (`WD`-bit slots): S layout (`kind = 0`, row `d`, entries `b ≤ d` of `b + 1` slots)
or A layout (`kind = 1`, row `l₀`, entries `m₂ < 231` of `m₂ + 1` slots). -/
syntax (name := x2T0Chunk) "x2_t0_chunk " ident num str num num num : command

@[command_elab x2T0Chunk] def elabX2T0Chunk : CommandElab := fun stx => do
  match stx with
  | `(x2_t0_chunk $pre:ident $kind:num $path:str $WD:num $lo:num $hi:num) =>
    let (kind, WD, lo, hi) := (kind.getNat, WD.getNat, lo.getNat, hi.getNat)
    let file := System.FilePath.mk (← getFileName)
    let root := (file.parent.bind (·.parent)).getD "."
    let p := System.FilePath.mk path.getString
    let full := if p.isAbsolute then p else root / p
    let data ← IO.FS.readBinFile full
    let db := WD / 8
    let mut pos := 0
    let mut rows : Array Expr := #[]
    for r in [lo:hi] do
      let lens := if kind == 0 then (List.range (r + 1)).map (· + 1) else (List.range 231).map (· + 1)
      let mut row : Array Nat := #[]
      for k in lens do
        unless pos + db * k ≤ data.size do throwError "x2_t0_chunk: file too short"
        row := row.push (bytesNatLE data pos (pos + db * k))
        pos := pos + db * k
      rows := rows.push (mkNatListExpr row.toList)
    unless pos == data.size do throwError "x2_t0_chunk: {data.size - pos} bytes left over"
    let val := rows.toList.foldr (fun r acc => mkApp3 (mkConst ``List.cons [Level.zero]) natListTy r acc)
      (mkApp (mkConst ``List.nil [Level.zero]) natListTy)
    addRawDef ((← getCurrNamespace) ++ pre.getId) (mkApp (mkConst ``List [Level.zero]) natListTy) val
  | _ => throwUnsupportedSyntax

/-- `x2_core_f0_tab pre W n B kind WD r C ch₁ ch₂ ...`: as `x2_core_f0_bin`, reading the entries
from the chunk tables `ch₁, ch₂, ...` (in row order) instead of a file. -/
syntax (name := x2CoreF0Tab) "x2_core_f0_tab " ident num num num num num num num ident* : command

@[command_elab x2CoreF0Tab] def elabX2CoreF0Tab : CommandElab := fun stx => do
  match stx with
  | `(x2_core_f0_tab $pre:ident $W:num $n:num $B:num $kind:num $WD:num $r:num $C:num $chs:ident*) =>
    let (W, n, B, kind, WD, r, C) :=
      (W.getNat, n.getNat, B.getNat, kind.getNat, WD.getNat, r.getNat, C.getNat)
    let mut flat : Array Nat := #[]
    let mut row0 := 0
    for ch in chs do
      let tab ← resolveNatTable (← resolveGlobalConstNoOverload ch)
      for row in tab do
        let rr := row0
        let mut k := 0
        for P in row do
          let len := if kind == 0 then k + 1 else k + 1
          flat := unpackSlots P WD len flat
          k := k + 1
        row0 := rr + 1
    let L := B * n
    let shift := 2 ^ (W - 1) - 2 ^ (WD - 1)
    let mut out : Array Nat := #[]
    for c in [0:C] do
      let mut slots : Array Nat := Array.mkEmpty L
      for q in [0:B] do
        let j := r * B + q
        for i in [0:n] do
          let idx := if kind == 0 then symIdxS i j c else symIdxA i j c
          unless idx < flat.size do throwError "x2_core_f0_tab: index {idx} out of the data"
          slots := slots.push (flat[idx]! + shift)
      out := out.push (packSlots slots W 0 L)
    addRawDef ((← getCurrNamespace) ++ rowName pre.getId r) natListTy (mkNatListExpr out.toList)
  | _ => throwUnsupportedSyntax

end ThreeCopyQutritWerner.X2
