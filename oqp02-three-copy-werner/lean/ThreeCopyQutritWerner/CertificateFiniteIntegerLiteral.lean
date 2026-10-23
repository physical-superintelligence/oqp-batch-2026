module

public import Lean
public meta import Lean
public import Mathlib.Data.Fin.VecNotation
public import Mathlib.Algebra.FiniteSupport.Basic
public import Mathlib.Algebra.GroupWithZero.Action.Regular
public import Mathlib.Algebra.GroupWithZero.Indicator
public import Mathlib.Algebra.Module.Submodule.EqLocus
public import Mathlib.Algebra.Module.Torsion.Field
public import Mathlib.Algebra.Order.BigOperators.Ring.Finset
public import Mathlib.Algebra.Polynomial.Basic
public import Mathlib.Data.List.Enum
public import Mathlib.LinearAlgebra.Span.Basic
public import Mathlib.Tactic.Basify.Attr

public meta section


/-! Exact transport of closed finite integer data literals. The elaborator
returns ordinary Lean data syntax; it supplies no theorem or proof oracle. -/
namespace ThreeCopyQutritWerner
open Lean Elab Term
meta section

private def certificateFiniteIntegerDecoder : String :=
  "\"\"\"Return one exact, hash-bound ordinary finite integer data literal.\n\nOnly lists of bounded natural/integer pairs, or a 729-vector of lists of\nsix-digit ternary words paired with integers, are accepted. No identifiers,\ncommands, proofs, applications, or executable payload are in this grammar.\n\"\"\"\nfrom pathlib import Path\nimport hashlib,json,lzma,re,sys\n\nLIMIT=16*1024*1024\nSHAPES={'pairs513':513,'pairs181':181,'words729':1}\n\ndef require(ok,message):\n    if not ok:raise ValueError(message)\n\ndef unpack(root,relative,expected):\n    require(isinstance(relative,str) and re.fullmatch(r'verification/finite-integer-literals/[0-9a-f]{64}\\.xz',relative) is not None,'Invalid finite literal path')\n    require(isinstance(expected,str) and re.fullmatch(r'[0-9a-f]{64}',expected) is not None,'Invalid finite literal raw digest')\n    root=Path(root).resolve();path=root/relative\n    for item in [path,*path.parents]:\n        if item==root:break\n        require(not item.is_symlink(),'Symlink finite literal path')\n    require(path.is_file() and path.resolve().is_relative_to(root),'Missing or escaping finite literal')\n    with path.open('rb') as stream:packed=stream.read(LIMIT+1)\n    require(len(packed)<=LIMIT and hashlib.sha256(packed).hexdigest()==path.stem,'Finite literal packed size or digest mismatch')\n    dec=lzma.LZMADecompressor(format=lzma.FORMAT_XZ,memlimit=256*1024*1024)\n    raw=dec.decompress(packed,max_length=LIMIT+1)\n    require(len(raw)<=LIMIT and dec.eof and not dec.unused_data,'Invalid bounded single finite literal stream')\n    require(hashlib.sha256(raw).hexdigest()==expected,'Finite literal expanded digest mismatch')\n    obj=json.loads(raw.decode('ascii'))\n    require(type(obj) is dict and set(obj)=={'version','shape','entries'},'Invalid finite literal envelope')\n    require(type(obj['version']) is int and obj['version']==1,'Invalid finite literal version')\n    require(type(obj['shape']) is str and obj['shape'] in SHAPES,'Invalid finite literal shape')\n    require(type(obj['entries']) is list and len(obj['entries'])==SHAPES[obj['shape']] and all(type(s) is str for s in obj['entries']),'Invalid finite literal entry count or type')\n    require((json.dumps(obj,sort_keys=True,separators=(',',':'),ensure_ascii=True)+'\\n').encode('ascii')==raw,'Noncanonical finite literal envelope')\n    return obj,packed,raw\n\nclass LiteralParser:\n    def __init__(self,text):self.text=text;self.pos=0;self.terms=0\n    def ws(self):\n        while self.pos<len(self.text) and self.text[self.pos] in ' \\n':self.pos+=1\n    def take(self,token):\n        self.ws()\n        if self.text.startswith(token,self.pos):self.pos+=len(token);return True\n        return False\n    def need(self,token):require(self.take(token),'Invalid finite literal token')\n    def integer(self):\n        self.ws();m=re.match(r'-?(?:0|[1-9][0-9]*)',self.text[self.pos:])\n        require(m is not None and len(m[0])<=32 and m[0]!='-0','Invalid finite literal integer')\n        self.pos+=len(m[0]);return int(m[0])\n    def word(self):\n        self.need('![')\n        for i in range(6):\n            if i:self.need(',')\n            require(0<=self.integer()<3,'Invalid ternary word digit')\n        self.need(']')\n    def row(self,bound=None):\n        self.need('[');count=0\n        if self.take(']'):return\n        while True:\n            self.need('(')\n            if bound is None:self.word()\n            else:require(0<=self.integer()<bound,'Finite pair index out of bounds')\n            self.need(',');self.integer();self.need(')');count+=1;self.terms+=1\n            require(count<=(729 if bound is None else bound),'Finite literal row size limit')\n            if self.take(']'):break\n            self.need(',')\n    def validate(self,shape):\n        if shape=='words729':\n            self.need('![')\n            for i in range(729):\n                if i:self.need(',')\n                self.row()\n            self.need(']')\n        else:self.row(513 if shape=='pairs513' else 181)\n        self.ws();require(self.pos==len(self.text),'Trailing finite literal syntax')\n        return self.text\n\ndef decode(root,relative,expected,index):\n    require(type(index) is int and 0<=index<513,'Invalid finite literal index')\n    obj,_,_=unpack(root,relative,expected)\n    require(index<len(obj['entries']),'Finite literal index out of range')\n    return LiteralParser(obj['entries'][index]).validate(obj['shape'])\n\nif __name__=='__main__':\n    require(len(sys.argv)==4,'Expected finite literal path, digest and index')\n    require(re.fullmatch(r'0|[1-9][0-9]{0,2}',sys.argv[3]) is not None,'Invalid finite literal CLI index')\n    sys.stdout.write(decode(Path.cwd(),sys.argv[1],sys.argv[2],int(sys.argv[3])))\n"

/-- One original literal from an immutable, bounded data table. -/
syntax (name := certificateFiniteIntegerLiteral) "certificate_finite_integer% " str str num : term

@[term_elab certificateFiniteIntegerLiteral]
def elabCertificateFiniteIntegerLiteral : TermElab := fun stx expectedType? => do
  match stx with
  | `(certificate_finite_integer% $path:str $digest:str $index:num) =>
    let output ← IO.Process.output {
      cmd := "python3"
      args := #["-c", certificateFiniteIntegerDecoder, path.getString,
        digest.getString, toString index.getNat] }
    unless output.exitCode == 0 do
      throwError "finite integer literal transport failed: {output.stderr}"
    let term ← Lean.ofExcept <|
      Lean.Parser.runParserCategory (← getEnv) `term output.stdout
    elabTerm term expectedType?
  | _ => throwUnsupportedSyntax

end
end ThreeCopyQutritWerner
