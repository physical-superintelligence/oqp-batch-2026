module

public import ThreeCopyQutritWerner.CertificateX2InputFA2x0
public import ThreeCopyQutritWerner.CertificateX2InputFA2x1
public import ThreeCopyQutritWerner.CertificateX2InputFA2x2
public import ThreeCopyQutritWerner.CertificateX2InputFA2x3
public import ThreeCopyQutritWerner.CertificateX2InputFA2x4
public import ThreeCopyQutritWerner.CertificateX2InputFA2x5
public import ThreeCopyQutritWerner.CertificateX2InputFA2x6
public import ThreeCopyQutritWerner.CertificateX2InputFA2x7
public import ThreeCopyQutritWerner.CertificateX2InputFA2x8
public import ThreeCopyQutritWerner.CertificateX2InputFA2x9
public import ThreeCopyQutritWerner.CertificateX2InputFA2x10
public import ThreeCopyQutritWerner.CertificateX2InputFA2x11
public import ThreeCopyQutritWerner.CertificateX2InputFA2x12
public import ThreeCopyQutritWerner.CertificateX2InputFA2x13
public import ThreeCopyQutritWerner.CertificateX2InputFA2x14
public import ThreeCopyQutritWerner.CertificateX2InputFA2x15
public import ThreeCopyQutritWerner.CertificateX2InputFA2x16
public import ThreeCopyQutritWerner.CertificateX2InputFA2x17
public import ThreeCopyQutritWerner.CertificateX2InputFA2x18
public import ThreeCopyQutritWerner.CertificateX2InputFA2x19
public import ThreeCopyQutritWerner.CertificateX2InputFA2x20
public import ThreeCopyQutritWerner.CertificateX2InputFA2x21
public import ThreeCopyQutritWerner.CertificateX2InputFA2x22
public import ThreeCopyQutritWerner.CertificateX2InputFA2x23
public import ThreeCopyQutritWerner.CertificateX2InputFA2x24
public import ThreeCopyQutritWerner.CertificateX2InputFA2x25
public import ThreeCopyQutritWerner.CertificateX2InputFA2x26
public import ThreeCopyQutritWerner.CertificateX2InputFA2x27
public import ThreeCopyQutritWerner.CertificateX2InputFA2x28
public import ThreeCopyQutritWerner.CertificateX2InputFA2x29
public import ThreeCopyQutritWerner.CertificateX2InputFA2x30
public import ThreeCopyQutritWerner.CertificateX2InputFA2x31
public import ThreeCopyQutritWerner.CertificateX2InputFA2x32
public import ThreeCopyQutritWerner.CertificateX2InputFA2x33
public import ThreeCopyQutritWerner.CertificateX2InputFA2x34
public import ThreeCopyQutritWerner.CertificateX2InputFA2x35
public import ThreeCopyQutritWerner.CertificateX2InputFA2x36
public import ThreeCopyQutritWerner.CertificateX2InputFA2x37
public import ThreeCopyQutritWerner.CertificateX2InputFA2x38
public import ThreeCopyQutritWerner.CertificateX2InputFA2x39
public import ThreeCopyQutritWerner.CertificateX2InputFA2x40
public import ThreeCopyQutritWerner.CertificateX2InputFA2x41
public import ThreeCopyQutritWerner.CertificateX2InputFA2x42
public import ThreeCopyQutritWerner.CertificateX2InputFA2x43
public import ThreeCopyQutritWerner.CertificateX2InputFA2x44
public import ThreeCopyQutritWerner.CertificateX2InputFA2x45
public import ThreeCopyQutritWerner.CertificateX2InputFA2x46

@[expose] public section


/-! HT0 of the A2g transfer theorems, for every symmetric source in the source forms of sector 2. -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option exponentiation.threshold 1000000

open scoped Matrix

namespace ThreeCopyQutritWerner.X2.InHA2
open ThreeCopyQutritWerner ThreeCopyQutritWerner.X2

theorem f0len : ∀ r < 3, (CoreA2g.f0.getD r []).length = 231 := by decide +kernel
theorem segs : ∀ c : Fin 231, ∀ u v : Fin 8, segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 c) c u v = true := by
  intro c u v
  have hc := c.isLt
  have key : ∀ c0 : ℕ, c0 < 231 → segOKA 2 InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (colFibers CoreA2g.f0 c0) c0 u v = true := by
    intro c0 hc0
    interval_cases c0
    · exact InFA2.col0 u v
    · exact InFA2.col1 u v
    · exact InFA2.col2 u v
    · exact InFA2.col3 u v
    · exact InFA2.col4 u v
    · exact InFA2.col5 u v
    · exact InFA2.col6 u v
    · exact InFA2.col7 u v
    · exact InFA2.col8 u v
    · exact InFA2.col9 u v
    · exact InFA2.col10 u v
    · exact InFA2.col11 u v
    · exact InFA2.col12 u v
    · exact InFA2.col13 u v
    · exact InFA2.col14 u v
    · exact InFA2.col15 u v
    · exact InFA2.col16 u v
    · exact InFA2.col17 u v
    · exact InFA2.col18 u v
    · exact InFA2.col19 u v
    · exact InFA2.col20 u v
    · exact InFA2.col21 u v
    · exact InFA2.col22 u v
    · exact InFA2.col23 u v
    · exact InFA2.col24 u v
    · exact InFA2.col25 u v
    · exact InFA2.col26 u v
    · exact InFA2.col27 u v
    · exact InFA2.col28 u v
    · exact InFA2.col29 u v
    · exact InFA2.col30 u v
    · exact InFA2.col31 u v
    · exact InFA2.col32 u v
    · exact InFA2.col33 u v
    · exact InFA2.col34 u v
    · exact InFA2.col35 u v
    · exact InFA2.col36 u v
    · exact InFA2.col37 u v
    · exact InFA2.col38 u v
    · exact InFA2.col39 u v
    · exact InFA2.col40 u v
    · exact InFA2.col41 u v
    · exact InFA2.col42 u v
    · exact InFA2.col43 u v
    · exact InFA2.col44 u v
    · exact InFA2.col45 u v
    · exact InFA2.col46 u v
    · exact InFA2.col47 u v
    · exact InFA2.col48 u v
    · exact InFA2.col49 u v
    · exact InFA2.col50 u v
    · exact InFA2.col51 u v
    · exact InFA2.col52 u v
    · exact InFA2.col53 u v
    · exact InFA2.col54 u v
    · exact InFA2.col55 u v
    · exact InFA2.col56 u v
    · exact InFA2.col57 u v
    · exact InFA2.col58 u v
    · exact InFA2.col59 u v
    · exact InFA2.col60 u v
    · exact InFA2.col61 u v
    · exact InFA2.col62 u v
    · exact InFA2.col63 u v
    · exact InFA2.col64 u v
    · exact InFA2.col65 u v
    · exact InFA2.col66 u v
    · exact InFA2.col67 u v
    · exact InFA2.col68 u v
    · exact InFA2.col69 u v
    · exact InFA2.col70 u v
    · exact InFA2.col71 u v
    · exact InFA2.col72 u v
    · exact InFA2.col73 u v
    · exact InFA2.col74 u v
    · exact InFA2.col75 u v
    · exact InFA2.col76 u v
    · exact InFA2.col77 u v
    · exact InFA2.col78 u v
    · exact InFA2.col79 u v
    · exact InFA2.col80 u v
    · exact InFA2.col81 u v
    · exact InFA2.col82 u v
    · exact InFA2.col83 u v
    · exact InFA2.col84 u v
    · exact InFA2.col85 u v
    · exact InFA2.col86 u v
    · exact InFA2.col87 u v
    · exact InFA2.col88 u v
    · exact InFA2.col89 u v
    · exact InFA2.col90 u v
    · exact InFA2.col91 u v
    · exact InFA2.col92 u v
    · exact InFA2.col93 u v
    · exact InFA2.col94 u v
    · exact InFA2.col95 u v
    · exact InFA2.col96 u v
    · exact InFA2.col97 u v
    · exact InFA2.col98 u v
    · exact InFA2.col99 u v
    · exact InFA2.col100 u v
    · exact InFA2.col101 u v
    · exact InFA2.col102 u v
    · exact InFA2.col103 u v
    · exact InFA2.col104 u v
    · exact InFA2.col105 u v
    · exact InFA2.col106 u v
    · exact InFA2.col107 u v
    · exact InFA2.col108 u v
    · exact InFA2.col109 u v
    · exact InFA2.col110 u v
    · exact InFA2.col111 u v
    · exact InFA2.col112 u v
    · exact InFA2.col113 u v
    · exact InFA2.col114 u v
    · exact InFA2.col115 u v
    · exact InFA2.col116 u v
    · exact InFA2.col117 u v
    · exact InFA2.col118 u v
    · exact InFA2.col119 u v
    · exact InFA2.col120 u v
    · exact InFA2.col121 u v
    · exact InFA2.col122 u v
    · exact InFA2.col123 u v
    · exact InFA2.col124 u v
    · exact InFA2.col125 u v
    · exact InFA2.col126 u v
    · exact InFA2.col127 u v
    · exact InFA2.col128 u v
    · exact InFA2.col129 u v
    · exact InFA2.col130 u v
    · exact InFA2.col131 u v
    · exact InFA2.col132 u v
    · exact InFA2.col133 u v
    · exact InFA2.col134 u v
    · exact InFA2.col135 u v
    · exact InFA2.col136 u v
    · exact InFA2.col137 u v
    · exact InFA2.col138 u v
    · exact InFA2.col139 u v
    · exact InFA2.col140 u v
    · exact InFA2.col141 u v
    · exact InFA2.col142 u v
    · exact InFA2.col143 u v
    · exact InFA2.col144 u v
    · exact InFA2.col145 u v
    · exact InFA2.col146 u v
    · exact InFA2.col147 u v
    · exact InFA2.col148 u v
    · exact InFA2.col149 u v
    · exact InFA2.col150 u v
    · exact InFA2.col151 u v
    · exact InFA2.col152 u v
    · exact InFA2.col153 u v
    · exact InFA2.col154 u v
    · exact InFA2.col155 u v
    · exact InFA2.col156 u v
    · exact InFA2.col157 u v
    · exact InFA2.col158 u v
    · exact InFA2.col159 u v
    · exact InFA2.col160 u v
    · exact InFA2.col161 u v
    · exact InFA2.col162 u v
    · exact InFA2.col163 u v
    · exact InFA2.col164 u v
    · exact InFA2.col165 u v
    · exact InFA2.col166 u v
    · exact InFA2.col167 u v
    · exact InFA2.col168 u v
    · exact InFA2.col169 u v
    · exact InFA2.col170 u v
    · exact InFA2.col171 u v
    · exact InFA2.col172 u v
    · exact InFA2.col173 u v
    · exact InFA2.col174 u v
    · exact InFA2.col175 u v
    · exact InFA2.col176 u v
    · exact InFA2.col177 u v
    · exact InFA2.col178 u v
    · exact InFA2.col179 u v
    · exact InFA2.col180 u v
    · exact InFA2.col181 u v
    · exact InFA2.col182 u v
    · exact InFA2.col183 u v
    · exact InFA2.col184 u v
    · exact InFA2.col185 u v
    · exact InFA2.col186 u v
    · exact InFA2.col187 u v
    · exact InFA2.col188 u v
    · exact InFA2.col189 u v
    · exact InFA2.col190 u v
    · exact InFA2.col191 u v
    · exact InFA2.col192 u v
    · exact InFA2.col193 u v
    · exact InFA2.col194 u v
    · exact InFA2.col195 u v
    · exact InFA2.col196 u v
    · exact InFA2.col197 u v
    · exact InFA2.col198 u v
    · exact InFA2.col199 u v
    · exact InFA2.col200 u v
    · exact InFA2.col201 u v
    · exact InFA2.col202 u v
    · exact InFA2.col203 u v
    · exact InFA2.col204 u v
    · exact InFA2.col205 u v
    · exact InFA2.col206 u v
    · exact InFA2.col207 u v
    · exact InFA2.col208 u v
    · exact InFA2.col209 u v
    · exact InFA2.col210 u v
    · exact InFA2.col211 u v
    · exact InFA2.col212 u v
    · exact InFA2.col213 u v
    · exact InFA2.col214 u v
    · exact InFA2.col215 u v
    · exact InFA2.col216 u v
    · exact InFA2.col217 u v
    · exact InFA2.col218 u v
    · exact InFA2.col219 u v
    · exact InFA2.col220 u v
    · exact InFA2.col221 u v
    · exact InFA2.col222 u v
    · exact InFA2.col223 u v
    · exact InFA2.col224 u v
    · exact InFA2.col225 u v
    · exact InFA2.col226 u v
    · exact InFA2.col227 u v
    · exact InFA2.col228 u v
    · exact InFA2.col229 u v
    · exact InFA2.col230 u v
  exact key c.val hc

/-- hT0 of `X2.CoreA2g.transfer_unit` and `.transfer_global`, verbatim, for every symmetric source in the source forms of sector 2. -/
theorem hT0 (N : X2Blocks 2) (hN : ∀ k, (N k)ᵀ = N k) (hsrc : InDA2.SrcForm N) :
    ∀ (i : Fin 282) (j : Fin 231) (c : Fin 231), x2EmbedA x2DataConcrete 2 N i j c =
      (ent 384 (384 - 1) (x2Tab CoreA2g.f0 (j.val / 77) c) ((j.val % 77) * 282 + i.val) : ℚ) / 1108531032609225922165724911675932935547910848716289179910144000 :=
  hT0A_of_segs 2 N InDA2.TTaasD InDA2.TCaasD InDA2.TTsaaD InDA2.TCasaD InDA2.Zd (InDA2.dirSpecA N hN hsrc) labelDecompS_2 labelDecompA_2 typeOKA_2 CoreA2g.f0 segs

end ThreeCopyQutritWerner.X2.InHA2
