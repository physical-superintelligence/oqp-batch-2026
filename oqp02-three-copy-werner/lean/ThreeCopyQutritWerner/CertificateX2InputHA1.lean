module

public import ThreeCopyQutritWerner.CertificateX2InputFA1x0
public import ThreeCopyQutritWerner.CertificateX2InputFA1x1
public import ThreeCopyQutritWerner.CertificateX2InputFA1x2
public import ThreeCopyQutritWerner.CertificateX2InputFA1x3
public import ThreeCopyQutritWerner.CertificateX2InputFA1x4
public import ThreeCopyQutritWerner.CertificateX2InputFA1x5
public import ThreeCopyQutritWerner.CertificateX2InputFA1x6
public import ThreeCopyQutritWerner.CertificateX2InputFA1x7
public import ThreeCopyQutritWerner.CertificateX2InputFA1x8
public import ThreeCopyQutritWerner.CertificateX2InputFA1x9
public import ThreeCopyQutritWerner.CertificateX2InputFA1x10
public import ThreeCopyQutritWerner.CertificateX2InputFA1x11
public import ThreeCopyQutritWerner.CertificateX2InputFA1x12
public import ThreeCopyQutritWerner.CertificateX2InputFA1x13
public import ThreeCopyQutritWerner.CertificateX2InputFA1x14
public import ThreeCopyQutritWerner.CertificateX2InputFA1x15
public import ThreeCopyQutritWerner.CertificateX2InputFA1x16
public import ThreeCopyQutritWerner.CertificateX2InputFA1x17
public import ThreeCopyQutritWerner.CertificateX2InputFA1x18
public import ThreeCopyQutritWerner.CertificateX2InputFA1x19
public import ThreeCopyQutritWerner.CertificateX2InputFA1x20
public import ThreeCopyQutritWerner.CertificateX2InputFA1x21
public import ThreeCopyQutritWerner.CertificateX2InputFA1x22
public import ThreeCopyQutritWerner.CertificateX2InputFA1x23
public import ThreeCopyQutritWerner.CertificateX2InputFA1x24
public import ThreeCopyQutritWerner.CertificateX2InputFA1x25
public import ThreeCopyQutritWerner.CertificateX2InputFA1x26
public import ThreeCopyQutritWerner.CertificateX2InputFA1x27
public import ThreeCopyQutritWerner.CertificateX2InputFA1x28
public import ThreeCopyQutritWerner.CertificateX2InputFA1x29
public import ThreeCopyQutritWerner.CertificateX2InputFA1x30
public import ThreeCopyQutritWerner.CertificateX2InputFA1x31
public import ThreeCopyQutritWerner.CertificateX2InputFA1x32
public import ThreeCopyQutritWerner.CertificateX2InputFA1x33
public import ThreeCopyQutritWerner.CertificateX2InputFA1x34
public import ThreeCopyQutritWerner.CertificateX2InputFA1x35
public import ThreeCopyQutritWerner.CertificateX2InputFA1x36
public import ThreeCopyQutritWerner.CertificateX2InputFA1x37
public import ThreeCopyQutritWerner.CertificateX2InputFA1x38
public import ThreeCopyQutritWerner.CertificateX2InputFA1x39
public import ThreeCopyQutritWerner.CertificateX2InputFA1x40
public import ThreeCopyQutritWerner.CertificateX2InputFA1x41
public import ThreeCopyQutritWerner.CertificateX2InputFA1x42
public import ThreeCopyQutritWerner.CertificateX2InputFA1x43
public import ThreeCopyQutritWerner.CertificateX2InputFA1x44
public import ThreeCopyQutritWerner.CertificateX2InputFA1x45
public import ThreeCopyQutritWerner.CertificateX2InputFA1x46

@[expose] public section


/-! HT0 of the A1g transfer theorems, for every symmetric source in the source forms of sector 1. -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option exponentiation.threshold 1000000

open scoped Matrix

namespace ThreeCopyQutritWerner.X2.InHA1
open ThreeCopyQutritWerner ThreeCopyQutritWerner.X2

theorem f0len : ∀ r < 3, (CoreA1g.f0.getD r []).length = 231 := by decide +kernel
theorem segs : ∀ c : Fin 231, ∀ u v : Fin 8, segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 c) c u v = true := by
  intro c u v
  have hc := c.isLt
  have key : ∀ c0 : ℕ, c0 < 231 → segOKA 1 InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (colFibers CoreA1g.f0 c0) c0 u v = true := by
    intro c0 hc0
    interval_cases c0
    · exact InFA1.col0 u v
    · exact InFA1.col1 u v
    · exact InFA1.col2 u v
    · exact InFA1.col3 u v
    · exact InFA1.col4 u v
    · exact InFA1.col5 u v
    · exact InFA1.col6 u v
    · exact InFA1.col7 u v
    · exact InFA1.col8 u v
    · exact InFA1.col9 u v
    · exact InFA1.col10 u v
    · exact InFA1.col11 u v
    · exact InFA1.col12 u v
    · exact InFA1.col13 u v
    · exact InFA1.col14 u v
    · exact InFA1.col15 u v
    · exact InFA1.col16 u v
    · exact InFA1.col17 u v
    · exact InFA1.col18 u v
    · exact InFA1.col19 u v
    · exact InFA1.col20 u v
    · exact InFA1.col21 u v
    · exact InFA1.col22 u v
    · exact InFA1.col23 u v
    · exact InFA1.col24 u v
    · exact InFA1.col25 u v
    · exact InFA1.col26 u v
    · exact InFA1.col27 u v
    · exact InFA1.col28 u v
    · exact InFA1.col29 u v
    · exact InFA1.col30 u v
    · exact InFA1.col31 u v
    · exact InFA1.col32 u v
    · exact InFA1.col33 u v
    · exact InFA1.col34 u v
    · exact InFA1.col35 u v
    · exact InFA1.col36 u v
    · exact InFA1.col37 u v
    · exact InFA1.col38 u v
    · exact InFA1.col39 u v
    · exact InFA1.col40 u v
    · exact InFA1.col41 u v
    · exact InFA1.col42 u v
    · exact InFA1.col43 u v
    · exact InFA1.col44 u v
    · exact InFA1.col45 u v
    · exact InFA1.col46 u v
    · exact InFA1.col47 u v
    · exact InFA1.col48 u v
    · exact InFA1.col49 u v
    · exact InFA1.col50 u v
    · exact InFA1.col51 u v
    · exact InFA1.col52 u v
    · exact InFA1.col53 u v
    · exact InFA1.col54 u v
    · exact InFA1.col55 u v
    · exact InFA1.col56 u v
    · exact InFA1.col57 u v
    · exact InFA1.col58 u v
    · exact InFA1.col59 u v
    · exact InFA1.col60 u v
    · exact InFA1.col61 u v
    · exact InFA1.col62 u v
    · exact InFA1.col63 u v
    · exact InFA1.col64 u v
    · exact InFA1.col65 u v
    · exact InFA1.col66 u v
    · exact InFA1.col67 u v
    · exact InFA1.col68 u v
    · exact InFA1.col69 u v
    · exact InFA1.col70 u v
    · exact InFA1.col71 u v
    · exact InFA1.col72 u v
    · exact InFA1.col73 u v
    · exact InFA1.col74 u v
    · exact InFA1.col75 u v
    · exact InFA1.col76 u v
    · exact InFA1.col77 u v
    · exact InFA1.col78 u v
    · exact InFA1.col79 u v
    · exact InFA1.col80 u v
    · exact InFA1.col81 u v
    · exact InFA1.col82 u v
    · exact InFA1.col83 u v
    · exact InFA1.col84 u v
    · exact InFA1.col85 u v
    · exact InFA1.col86 u v
    · exact InFA1.col87 u v
    · exact InFA1.col88 u v
    · exact InFA1.col89 u v
    · exact InFA1.col90 u v
    · exact InFA1.col91 u v
    · exact InFA1.col92 u v
    · exact InFA1.col93 u v
    · exact InFA1.col94 u v
    · exact InFA1.col95 u v
    · exact InFA1.col96 u v
    · exact InFA1.col97 u v
    · exact InFA1.col98 u v
    · exact InFA1.col99 u v
    · exact InFA1.col100 u v
    · exact InFA1.col101 u v
    · exact InFA1.col102 u v
    · exact InFA1.col103 u v
    · exact InFA1.col104 u v
    · exact InFA1.col105 u v
    · exact InFA1.col106 u v
    · exact InFA1.col107 u v
    · exact InFA1.col108 u v
    · exact InFA1.col109 u v
    · exact InFA1.col110 u v
    · exact InFA1.col111 u v
    · exact InFA1.col112 u v
    · exact InFA1.col113 u v
    · exact InFA1.col114 u v
    · exact InFA1.col115 u v
    · exact InFA1.col116 u v
    · exact InFA1.col117 u v
    · exact InFA1.col118 u v
    · exact InFA1.col119 u v
    · exact InFA1.col120 u v
    · exact InFA1.col121 u v
    · exact InFA1.col122 u v
    · exact InFA1.col123 u v
    · exact InFA1.col124 u v
    · exact InFA1.col125 u v
    · exact InFA1.col126 u v
    · exact InFA1.col127 u v
    · exact InFA1.col128 u v
    · exact InFA1.col129 u v
    · exact InFA1.col130 u v
    · exact InFA1.col131 u v
    · exact InFA1.col132 u v
    · exact InFA1.col133 u v
    · exact InFA1.col134 u v
    · exact InFA1.col135 u v
    · exact InFA1.col136 u v
    · exact InFA1.col137 u v
    · exact InFA1.col138 u v
    · exact InFA1.col139 u v
    · exact InFA1.col140 u v
    · exact InFA1.col141 u v
    · exact InFA1.col142 u v
    · exact InFA1.col143 u v
    · exact InFA1.col144 u v
    · exact InFA1.col145 u v
    · exact InFA1.col146 u v
    · exact InFA1.col147 u v
    · exact InFA1.col148 u v
    · exact InFA1.col149 u v
    · exact InFA1.col150 u v
    · exact InFA1.col151 u v
    · exact InFA1.col152 u v
    · exact InFA1.col153 u v
    · exact InFA1.col154 u v
    · exact InFA1.col155 u v
    · exact InFA1.col156 u v
    · exact InFA1.col157 u v
    · exact InFA1.col158 u v
    · exact InFA1.col159 u v
    · exact InFA1.col160 u v
    · exact InFA1.col161 u v
    · exact InFA1.col162 u v
    · exact InFA1.col163 u v
    · exact InFA1.col164 u v
    · exact InFA1.col165 u v
    · exact InFA1.col166 u v
    · exact InFA1.col167 u v
    · exact InFA1.col168 u v
    · exact InFA1.col169 u v
    · exact InFA1.col170 u v
    · exact InFA1.col171 u v
    · exact InFA1.col172 u v
    · exact InFA1.col173 u v
    · exact InFA1.col174 u v
    · exact InFA1.col175 u v
    · exact InFA1.col176 u v
    · exact InFA1.col177 u v
    · exact InFA1.col178 u v
    · exact InFA1.col179 u v
    · exact InFA1.col180 u v
    · exact InFA1.col181 u v
    · exact InFA1.col182 u v
    · exact InFA1.col183 u v
    · exact InFA1.col184 u v
    · exact InFA1.col185 u v
    · exact InFA1.col186 u v
    · exact InFA1.col187 u v
    · exact InFA1.col188 u v
    · exact InFA1.col189 u v
    · exact InFA1.col190 u v
    · exact InFA1.col191 u v
    · exact InFA1.col192 u v
    · exact InFA1.col193 u v
    · exact InFA1.col194 u v
    · exact InFA1.col195 u v
    · exact InFA1.col196 u v
    · exact InFA1.col197 u v
    · exact InFA1.col198 u v
    · exact InFA1.col199 u v
    · exact InFA1.col200 u v
    · exact InFA1.col201 u v
    · exact InFA1.col202 u v
    · exact InFA1.col203 u v
    · exact InFA1.col204 u v
    · exact InFA1.col205 u v
    · exact InFA1.col206 u v
    · exact InFA1.col207 u v
    · exact InFA1.col208 u v
    · exact InFA1.col209 u v
    · exact InFA1.col210 u v
    · exact InFA1.col211 u v
    · exact InFA1.col212 u v
    · exact InFA1.col213 u v
    · exact InFA1.col214 u v
    · exact InFA1.col215 u v
    · exact InFA1.col216 u v
    · exact InFA1.col217 u v
    · exact InFA1.col218 u v
    · exact InFA1.col219 u v
    · exact InFA1.col220 u v
    · exact InFA1.col221 u v
    · exact InFA1.col222 u v
    · exact InFA1.col223 u v
    · exact InFA1.col224 u v
    · exact InFA1.col225 u v
    · exact InFA1.col226 u v
    · exact InFA1.col227 u v
    · exact InFA1.col228 u v
    · exact InFA1.col229 u v
    · exact InFA1.col230 u v
  exact key c.val hc

/-- hT0 of `X2.CoreA1g.transfer_unit` and `.transfer_global`, verbatim, for every symmetric source in the source forms of sector 1. -/
theorem hT0 (N : X2Blocks 1) (hN : ∀ k, (N k)ᵀ = N k) (hsrc : InDA1.SrcForm N) :
    ∀ (i : Fin 282) (j : Fin 231) (c : Fin 231), x2EmbedA x2DataConcrete 1 N i j c =
      (ent 384 (384 - 1) (x2Tab CoreA1g.f0 (j.val / 77) c) ((j.val % 77) * 282 + i.val) : ℚ) / 1108531032609225922165724911675932935547910848716289179910144000 :=
  hT0A_of_segs 1 N InDA1.TTaasD InDA1.TCaasD InDA1.TTsaaD InDA1.TCasaD InDA1.Zd (InDA1.dirSpecA N hN hsrc) labelDecompS_1 labelDecompA_1 typeOKA_1 CoreA1g.f0 segs

end ThreeCopyQutritWerner.X2.InHA1
