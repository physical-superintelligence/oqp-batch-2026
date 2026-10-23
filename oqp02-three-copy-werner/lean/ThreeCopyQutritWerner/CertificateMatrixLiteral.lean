module

public import Lean
public meta import Lean
public import Mathlib.LinearAlgebra.Matrix.Notation
public import Mathlib.Algebra.FiniteSupport.Basic
public import Mathlib.Algebra.GroupWithZero.Action.Regular
public import Mathlib.Algebra.GroupWithZero.Indicator
public import Mathlib.Algebra.Module.Submodule.EqLocus
public import Mathlib.Algebra.Module.Torsion.Field
public import Mathlib.Algebra.Order.BigOperators.Ring.Finset
public import Mathlib.Algebra.Polynomial.Basic
public import Mathlib.Algebra.Ring.Hom.InjSurj
public import Mathlib.Data.List.Enum
public import Mathlib.Tactic.Basify.Attr

public meta section


/-! Source transport for exact integer matrix literals. The elaborator reconstructs
an ordinary matrix term; it supplies no theorem or proof and uses no native oracle.
Every proof concerning the resulting data remains checked by the Lean kernel. -/

namespace ThreeCopyQutritWerner
open Lean Elab Term
meta section

private def certificateMatrixDecoder : String :=
  "\"\"\"Decode one pinned integer matrix term; no compiler, evaluation or source mutation.\"\"\"\nfrom pathlib import Path\nimport hashlib,lzma,re,sys\n\ndef decode(root:Path,relative:str,expected:str)->str:\n    if re.fullmatch(r'verification/matrix-literals/[0-9a-f]{64}\\.xz',relative) is None:\n        raise ValueError('Invalid matrix payload path')\n    if re.fullmatch(r'[0-9a-f]{64}',expected) is None:\n        raise ValueError('Invalid matrix term digest')\n    path=root/relative\n    if path.is_symlink() or not path.resolve().is_relative_to(root.resolve()):\n        raise ValueError('Matrix payload escapes source root')\n    with path.open(\"rb\") as stream:\n        packed=stream.read(16*1024*1024+1)\n    if len(packed)>16*1024*1024 or hashlib.sha256(packed).hexdigest()!=path.stem:\n        raise ValueError('Matrix payload digest or size mismatch')\n    dec=lzma.LZMADecompressor(format=lzma.FORMAT_XZ,memlimit=256*1024*1024)\n    raw=dec.decompress(packed,max_length=16*1024*1024+1)\n    if len(raw)>16*1024*1024 or not dec.eof or dec.unused_data:\n        raise ValueError('Invalid or oversized single matrix stream')\n    if hashlib.sha256(raw).hexdigest()!=expected:\n        raise ValueError('Matrix term digest mismatch')\n    text=raw.decode('ascii')\n    if re.fullmatch(r'!!\\[\\s*-?[0-9]+(?:\\s*[,;]\\s*-?[0-9]+)*\\s*\\]',text) is None:\n        raise ValueError('Payload is not a literal integer matrix')\n    rows=text[3:-1].split(';')\n    if len({len(row.split(','))for row in rows})!=1:\n        raise ValueError('Ragged matrix literal')\n    return text\n\nif __name__=='__main__':\n    if len(sys.argv)!=3:raise ValueError('Expected payload path and raw digest')\n    sys.stdout.write(decode(Path.cwd(),sys.argv[1],sys.argv[2]))\n"

/-- A hash-bound compressed spelling of a literal integer matrix. -/
syntax (name := certificateMatrixLiteral) "certificate_matrix% " str str : term

@[term_elab certificateMatrixLiteral]
def elabCertificateMatrixLiteral : TermElab := fun stx expectedType? => do
  match stx with
  | `(certificate_matrix% $path:str $digest:str) =>
    let output ← IO.Process.output {
      cmd := "python3"
      args := #["-c", certificateMatrixDecoder, path.getString, digest.getString] }
    unless output.exitCode == 0 do
      throwError "integer matrix transport failed: {output.stderr}"
    let term ← Lean.ofExcept <|
      Lean.Parser.runParserCategory (← getEnv) `term output.stdout
    elabTerm term expectedType?
  | _ => throwUnsupportedSyntax

end
end ThreeCopyQutritWerner
