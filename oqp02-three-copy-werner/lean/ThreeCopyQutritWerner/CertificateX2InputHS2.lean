module

public import ThreeCopyQutritWerner.CertificateX2InputFS2x0
public import ThreeCopyQutritWerner.CertificateX2InputFS2x1
public import ThreeCopyQutritWerner.CertificateX2InputFS2x2
public import ThreeCopyQutritWerner.CertificateX2InputFS2x3
public import ThreeCopyQutritWerner.CertificateX2InputFS2x4
public import ThreeCopyQutritWerner.CertificateX2InputFS2x5
public import ThreeCopyQutritWerner.CertificateX2InputFS2x6
public import ThreeCopyQutritWerner.CertificateX2InputFS2x7
public import ThreeCopyQutritWerner.CertificateX2InputFS2x8
public import ThreeCopyQutritWerner.CertificateX2InputFS2x9
public import ThreeCopyQutritWerner.CertificateX2InputFS2x10
public import ThreeCopyQutritWerner.CertificateX2InputFS2x11
public import ThreeCopyQutritWerner.CertificateX2InputFS2x12
public import ThreeCopyQutritWerner.CertificateX2InputFS2x13
public import ThreeCopyQutritWerner.CertificateX2InputFS2x14
public import ThreeCopyQutritWerner.CertificateX2InputFS2x15
public import ThreeCopyQutritWerner.CertificateX2InputFS2x16
public import ThreeCopyQutritWerner.CertificateX2InputFS2x17
public import ThreeCopyQutritWerner.CertificateX2InputFS2x18
public import ThreeCopyQutritWerner.CertificateX2InputFS2x19
public import ThreeCopyQutritWerner.CertificateX2InputFS2x20
public import ThreeCopyQutritWerner.CertificateX2InputFS2x21
public import ThreeCopyQutritWerner.CertificateX2InputFS2x22
public import ThreeCopyQutritWerner.CertificateX2InputFS2x23

@[expose] public section


/-! HT0 of the S2g transfer theorems, for every symmetric source in the source forms of sector 2. -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option exponentiation.threshold 1000000

open scoped Matrix

namespace ThreeCopyQutritWerner.X2.InHS2
open ThreeCopyQutritWerner ThreeCopyQutritWerner.X2

theorem f0len : ∀ r < 3, (CoreS2g.f0.getD r []).length = 282 := by decide +kernel
theorem segs : ∀ c : Fin 282, ∀ u v : Fin 8, segOK 2 InDS2.TTd InDS2.TCd InDS2.Zd (colFibers CoreS2g.f0 c) c u v = true := by
  intro c u v
  have hc := c.isLt
  have key : ∀ c0 : ℕ, c0 < 282 → segOK 2 InDS2.TTd InDS2.TCd InDS2.Zd (colFibers CoreS2g.f0 c0) c0 u v = true := by
    intro c0 hc0
    interval_cases c0
    · exact colsChunkOK_sound 2 _ _ _ _ f0len 0 1 (by norm_num) InFS2.col0 0 le_rfl (by norm_num) u v
    · exact colsChunkOK_sound 2 _ _ _ _ f0len 1 1 (by norm_num) InFS2.col1 1 le_rfl (by norm_num) u v
    · exact colsChunkOK_sound 2 _ _ _ _ f0len 2 1 (by norm_num) InFS2.col2 2 le_rfl (by norm_num) u v
    · exact colsChunkOK_sound 2 _ _ _ _ f0len 3 1 (by norm_num) InFS2.col3 3 le_rfl (by norm_num) u v
    · exact colsChunkOK_sound 2 _ _ _ _ f0len 4 1 (by norm_num) InFS2.col4 4 le_rfl (by norm_num) u v
    · exact colsChunkOK_sound 2 _ _ _ _ f0len 5 1 (by norm_num) InFS2.col5 5 le_rfl (by norm_num) u v
    · exact colsChunkOK_sound 2 _ _ _ _ f0len 6 1 (by norm_num) InFS2.col6 6 le_rfl (by norm_num) u v
    · exact colsChunkOK_sound 2 _ _ _ _ f0len 7 1 (by norm_num) InFS2.col7 7 le_rfl (by norm_num) u v
    · exact colsChunkOK_sound 2 _ _ _ _ f0len 8 1 (by norm_num) InFS2.col8 8 le_rfl (by norm_num) u v
    · exact colsChunkOK_sound 2 _ _ _ _ f0len 9 1 (by norm_num) InFS2.col9 9 le_rfl (by norm_num) u v
    · exact colsChunkOK_sound 2 _ _ _ _ f0len 10 1 (by norm_num) InFS2.col10 10 le_rfl (by norm_num) u v
    · exact colsChunkOK_sound 2 _ _ _ _ f0len 11 1 (by norm_num) InFS2.col11 11 le_rfl (by norm_num) u v
    · exact colsChunkOK_sound 2 _ _ _ _ f0len 12 1 (by norm_num) InFS2.col12 12 le_rfl (by norm_num) u v
    · exact colsChunkOK_sound 2 _ _ _ _ f0len 13 1 (by norm_num) InFS2.col13 13 le_rfl (by norm_num) u v
    · exact colsChunkOK_sound 2 _ _ _ _ f0len 14 1 (by norm_num) InFS2.col14 14 le_rfl (by norm_num) u v
    · exact colsChunkOK_sound 2 _ _ _ _ f0len 15 1 (by norm_num) InFS2.col15 15 le_rfl (by norm_num) u v
    · exact colsChunkOK_sound 2 _ _ _ _ f0len 16 1 (by norm_num) InFS2.col16 16 le_rfl (by norm_num) u v
    · exact colsChunkOK_sound 2 _ _ _ _ f0len 17 1 (by norm_num) InFS2.col17 17 le_rfl (by norm_num) u v
    · exact colsChunkOK_sound 2 _ _ _ _ f0len 18 1 (by norm_num) InFS2.col18 18 le_rfl (by norm_num) u v
    · exact colsChunkOK_sound 2 _ _ _ _ f0len 19 1 (by norm_num) InFS2.col19 19 le_rfl (by norm_num) u v
    · exact colsChunkOK_sound 2 _ _ _ _ f0len 20 1 (by norm_num) InFS2.col20 20 le_rfl (by norm_num) u v
    · exact colsChunkOK_sound 2 _ _ _ _ f0len 21 1 (by norm_num) InFS2.col21 21 le_rfl (by norm_num) u v
    · exact colsChunkOK_sound 2 _ _ _ _ f0len 22 1 (by norm_num) InFS2.col22 22 le_rfl (by norm_num) u v
    · exact colsChunkOK_sound 2 _ _ _ _ f0len 23 1 (by norm_num) InFS2.col23 23 le_rfl (by norm_num) u v
    · exact colsChunkOK_sound 2 _ _ _ _ f0len 24 1 (by norm_num) InFS2.col24 24 le_rfl (by norm_num) u v
    · exact colsChunkOK_sound 2 _ _ _ _ f0len 25 1 (by norm_num) InFS2.col25 25 le_rfl (by norm_num) u v
    · exact colsChunkOK_sound 2 _ _ _ _ f0len 26 1 (by norm_num) InFS2.col26 26 le_rfl (by norm_num) u v
    · exact colsChunkOK_sound 2 _ _ _ _ f0len 27 1 (by norm_num) InFS2.col27 27 le_rfl (by norm_num) u v
    · exact colsChunkOK_sound 2 _ _ _ _ f0len 28 1 (by norm_num) InFS2.col28 28 le_rfl (by norm_num) u v
    · exact colsChunkOK_sound 2 _ _ _ _ f0len 29 1 (by norm_num) InFS2.col29 29 le_rfl (by norm_num) u v
    · exact colsChunkOK_sound 2 _ _ _ _ f0len 30 1 (by norm_num) InFS2.col30 30 le_rfl (by norm_num) u v
    · exact colsChunkOK_sound 2 _ _ _ _ f0len 31 1 (by norm_num) InFS2.col31 31 le_rfl (by norm_num) u v
    · exact colsChunkOK_sound 2 _ _ _ _ f0len 32 1 (by norm_num) InFS2.col32 32 le_rfl (by norm_num) u v
    · exact colsChunkOK_sound 2 _ _ _ _ f0len 33 1 (by norm_num) InFS2.col33 33 le_rfl (by norm_num) u v
    · exact colsChunkOK_sound 2 _ _ _ _ f0len 34 1 (by norm_num) InFS2.col34 34 le_rfl (by norm_num) u v
    · exact colsChunkOK_sound 2 _ _ _ _ f0len 35 1 (by norm_num) InFS2.col35 35 le_rfl (by norm_num) u v
    · exact colsChunkOK_sound 2 _ _ _ _ f0len 36 1 (by norm_num) InFS2.col36 36 le_rfl (by norm_num) u v
    · exact colsChunkOK_sound 2 _ _ _ _ f0len 37 1 (by norm_num) InFS2.col37 37 le_rfl (by norm_num) u v
    · exact colsChunkOK_sound 2 _ _ _ _ f0len 38 1 (by norm_num) InFS2.col38 38 le_rfl (by norm_num) u v
    · exact colsChunkOK_sound 2 _ _ _ _ f0len 39 1 (by norm_num) InFS2.col39 39 le_rfl (by norm_num) u v
    · exact colsChunkOK_sound 2 _ _ _ _ f0len 40 1 (by norm_num) InFS2.col40 40 le_rfl (by norm_num) u v
    · exact colsChunkOK_sound 2 _ _ _ _ f0len 41 1 (by norm_num) InFS2.col41 41 le_rfl (by norm_num) u v
    · exact colsChunkOK_sound 2 _ _ _ _ f0len 42 1 (by norm_num) InFS2.col42 42 le_rfl (by norm_num) u v
    · exact colsChunkOK_sound 2 _ _ _ _ f0len 43 1 (by norm_num) InFS2.col43 43 le_rfl (by norm_num) u v
    · exact colsChunkOK_sound 2 _ _ _ _ f0len 44 1 (by norm_num) InFS2.col44 44 le_rfl (by norm_num) u v
    · exact colsChunkOK_sound 2 _ _ _ _ f0len 45 1 (by norm_num) InFS2.col45 45 le_rfl (by norm_num) u v
    · exact colsChunkOK_sound 2 _ _ _ _ f0len 46 1 (by norm_num) InFS2.col46 46 le_rfl (by norm_num) u v
    · exact colsChunkOK_sound 2 _ _ _ _ f0len 47 1 (by norm_num) InFS2.col47 47 le_rfl (by norm_num) u v
    · exact colsChunkOK_sound 2 _ _ _ _ f0len 48 1 (by norm_num) InFS2.col48 48 le_rfl (by norm_num) u v
    · exact colsChunkOK_sound 2 _ _ _ _ f0len 49 1 (by norm_num) InFS2.col49 49 le_rfl (by norm_num) u v
    · exact colsChunkOK_sound 2 _ _ _ _ f0len 50 1 (by norm_num) InFS2.col50 50 le_rfl (by norm_num) u v
    · exact colsChunkOK_sound 2 _ _ _ _ f0len 51 1 (by norm_num) InFS2.col51 51 le_rfl (by norm_num) u v
    · exact colsChunkOK_sound 2 _ _ _ _ f0len 52 1 (by norm_num) InFS2.col52 52 le_rfl (by norm_num) u v
    · exact colsChunkOK_sound 2 _ _ _ _ f0len 53 1 (by norm_num) InFS2.col53 53 le_rfl (by norm_num) u v
    · exact colsChunkOK_sound 2 _ _ _ _ f0len 54 1 (by norm_num) InFS2.col54 54 le_rfl (by norm_num) u v
    · exact colsChunkOK_sound 2 _ _ _ _ f0len 55 1 (by norm_num) InFS2.col55 55 le_rfl (by norm_num) u v
    · exact colsChunkOK_sound 2 _ _ _ _ f0len 56 1 (by norm_num) InFS2.col56 56 le_rfl (by norm_num) u v
    · exact colsChunkOK_sound 2 _ _ _ _ f0len 57 1 (by norm_num) InFS2.col57 57 le_rfl (by norm_num) u v
    · exact colsChunkOK_sound 2 _ _ _ _ f0len 58 1 (by norm_num) InFS2.col58 58 le_rfl (by norm_num) u v
    · exact colsChunkOK_sound 2 _ _ _ _ f0len 59 1 (by norm_num) InFS2.col59 59 le_rfl (by norm_num) u v
    · exact colsChunkOK_sound 2 _ _ _ _ f0len 60 1 (by norm_num) InFS2.col60 60 le_rfl (by norm_num) u v
    · exact colsChunkOK_sound 2 _ _ _ _ f0len 61 1 (by norm_num) InFS2.col61 61 le_rfl (by norm_num) u v
    · exact colsChunkOK_sound 2 _ _ _ _ f0len 62 1 (by norm_num) InFS2.col62 62 le_rfl (by norm_num) u v
    · exact colsChunkOK_sound 2 _ _ _ _ f0len 63 1 (by norm_num) InFS2.col63 63 le_rfl (by norm_num) u v
    · exact colsChunkOK_sound 2 _ _ _ _ f0len 64 1 (by norm_num) InFS2.col64 64 le_rfl (by norm_num) u v
    · exact colsChunkOK_sound 2 _ _ _ _ f0len 65 1 (by norm_num) InFS2.col65 65 le_rfl (by norm_num) u v
    · exact colsChunkOK_sound 2 _ _ _ _ f0len 66 1 (by norm_num) InFS2.col66 66 le_rfl (by norm_num) u v
    · exact colsChunkOK_sound 2 _ _ _ _ f0len 67 1 (by norm_num) InFS2.col67 67 le_rfl (by norm_num) u v
    · exact colsChunkOK_sound 2 _ _ _ _ f0len 68 1 (by norm_num) InFS2.col68 68 le_rfl (by norm_num) u v
    · exact colsChunkOK_sound 2 _ _ _ _ f0len 69 1 (by norm_num) InFS2.col69 69 le_rfl (by norm_num) u v
    · exact colsChunkOK_sound 2 _ _ _ _ f0len 70 1 (by norm_num) InFS2.col70 70 le_rfl (by norm_num) u v
    · exact colsChunkOK_sound 2 _ _ _ _ f0len 71 1 (by norm_num) InFS2.col71 71 le_rfl (by norm_num) u v
    · exact colsChunkOK_sound 2 _ _ _ _ f0len 72 1 (by norm_num) InFS2.col72 72 le_rfl (by norm_num) u v
    · exact colsChunkOK_sound 2 _ _ _ _ f0len 73 1 (by norm_num) InFS2.col73 73 le_rfl (by norm_num) u v
    · exact colsChunkOK_sound 2 _ _ _ _ f0len 74 1 (by norm_num) InFS2.col74 74 le_rfl (by norm_num) u v
    · exact colsChunkOK_sound 2 _ _ _ _ f0len 75 1 (by norm_num) InFS2.col75 75 le_rfl (by norm_num) u v
    · exact colsChunkOK_sound 2 _ _ _ _ f0len 76 1 (by norm_num) InFS2.col76 76 le_rfl (by norm_num) u v
    · exact colsChunkOK_sound 2 _ _ _ _ f0len 77 1 (by norm_num) InFS2.col77 77 le_rfl (by norm_num) u v
    · exact colsChunkOK_sound 2 _ _ _ _ f0len 78 1 (by norm_num) InFS2.col78 78 le_rfl (by norm_num) u v
    · exact colsChunkOK_sound 2 _ _ _ _ f0len 79 1 (by norm_num) InFS2.col79 79 le_rfl (by norm_num) u v
    · exact colsChunkOK_sound 2 _ _ _ _ f0len 80 1 (by norm_num) InFS2.col80 80 le_rfl (by norm_num) u v
    · exact colsChunkOK_sound 2 _ _ _ _ f0len 81 1 (by norm_num) InFS2.col81 81 le_rfl (by norm_num) u v
    · exact colsChunkOK_sound 2 _ _ _ _ f0len 82 1 (by norm_num) InFS2.col82 82 le_rfl (by norm_num) u v
    · exact colsChunkOK_sound 2 _ _ _ _ f0len 83 1 (by norm_num) InFS2.col83 83 le_rfl (by norm_num) u v
    · exact colsChunkOK_sound 2 _ _ _ _ f0len 84 1 (by norm_num) InFS2.col84 84 le_rfl (by norm_num) u v
    · exact colsChunkOK_sound 2 _ _ _ _ f0len 85 1 (by norm_num) InFS2.col85 85 le_rfl (by norm_num) u v
    · exact colsChunkOK_sound 2 _ _ _ _ f0len 86 1 (by norm_num) InFS2.col86 86 le_rfl (by norm_num) u v
    · exact colsChunkOK_sound 2 _ _ _ _ f0len 87 1 (by norm_num) InFS2.col87 87 le_rfl (by norm_num) u v
    · exact colsChunkOK_sound 2 _ _ _ _ f0len 88 1 (by norm_num) InFS2.col88 88 le_rfl (by norm_num) u v
    · exact colsChunkOK_sound 2 _ _ _ _ f0len 89 1 (by norm_num) InFS2.col89 89 le_rfl (by norm_num) u v
    · exact colsChunkOK_sound 2 _ _ _ _ f0len 90 1 (by norm_num) InFS2.col90 90 le_rfl (by norm_num) u v
    · exact colsChunkOK_sound 2 _ _ _ _ f0len 91 1 (by norm_num) InFS2.col91 91 le_rfl (by norm_num) u v
    · exact colsChunkOK_sound 2 _ _ _ _ f0len 92 1 (by norm_num) InFS2.col92 92 le_rfl (by norm_num) u v
    · exact colsChunkOK_sound 2 _ _ _ _ f0len 93 1 (by norm_num) InFS2.col93 93 le_rfl (by norm_num) u v
    · exact colsChunkOK_sound 2 _ _ _ _ f0len 94 1 (by norm_num) InFS2.col94 94 le_rfl (by norm_num) u v
    · exact colsChunkOK_sound 2 _ _ _ _ f0len 95 1 (by norm_num) InFS2.col95 95 le_rfl (by norm_num) u v
    · exact colsChunkOK_sound 2 _ _ _ _ f0len 96 1 (by norm_num) InFS2.col96 96 le_rfl (by norm_num) u v
    · exact colsChunkOK_sound 2 _ _ _ _ f0len 97 1 (by norm_num) InFS2.col97 97 le_rfl (by norm_num) u v
    · exact colsChunkOK_sound 2 _ _ _ _ f0len 98 1 (by norm_num) InFS2.col98 98 le_rfl (by norm_num) u v
    · exact colsChunkOK_sound 2 _ _ _ _ f0len 99 1 (by norm_num) InFS2.col99 99 le_rfl (by norm_num) u v
    · exact colsChunkOK_sound 2 _ _ _ _ f0len 100 1 (by norm_num) InFS2.col100 100 le_rfl (by norm_num) u v
    · exact colsChunkOK_sound 2 _ _ _ _ f0len 101 1 (by norm_num) InFS2.col101 101 le_rfl (by norm_num) u v
    · exact colsChunkOK_sound 2 _ _ _ _ f0len 102 1 (by norm_num) InFS2.col102 102 le_rfl (by norm_num) u v
    · exact colsChunkOK_sound 2 _ _ _ _ f0len 103 1 (by norm_num) InFS2.col103 103 le_rfl (by norm_num) u v
    · exact colsChunkOK_sound 2 _ _ _ _ f0len 104 1 (by norm_num) InFS2.col104 104 le_rfl (by norm_num) u v
    · exact colsChunkOK_sound 2 _ _ _ _ f0len 105 1 (by norm_num) InFS2.col105 105 le_rfl (by norm_num) u v
    · exact colsChunkOK_sound 2 _ _ _ _ f0len 106 1 (by norm_num) InFS2.col106 106 le_rfl (by norm_num) u v
    · exact colsChunkOK_sound 2 _ _ _ _ f0len 107 1 (by norm_num) InFS2.col107 107 le_rfl (by norm_num) u v
    · exact colsChunkOK_sound 2 _ _ _ _ f0len 108 1 (by norm_num) InFS2.col108 108 le_rfl (by norm_num) u v
    · exact colsChunkOK_sound 2 _ _ _ _ f0len 109 1 (by norm_num) InFS2.col109 109 le_rfl (by norm_num) u v
    · exact colsChunkOK_sound 2 _ _ _ _ f0len 110 1 (by norm_num) InFS2.col110 110 le_rfl (by norm_num) u v
    · exact colsChunkOK_sound 2 _ _ _ _ f0len 111 1 (by norm_num) InFS2.col111 111 le_rfl (by norm_num) u v
    · exact colsChunkOK_sound 2 _ _ _ _ f0len 112 1 (by norm_num) InFS2.col112 112 le_rfl (by norm_num) u v
    · exact colsChunkOK_sound 2 _ _ _ _ f0len 113 1 (by norm_num) InFS2.col113 113 le_rfl (by norm_num) u v
    · exact colsChunkOK_sound 2 _ _ _ _ f0len 114 1 (by norm_num) InFS2.col114 114 le_rfl (by norm_num) u v
    · exact colsChunkOK_sound 2 _ _ _ _ f0len 115 1 (by norm_num) InFS2.col115 115 le_rfl (by norm_num) u v
    · exact colsChunkOK_sound 2 _ _ _ _ f0len 116 1 (by norm_num) InFS2.col116 116 le_rfl (by norm_num) u v
    · exact colsChunkOK_sound 2 _ _ _ _ f0len 117 1 (by norm_num) InFS2.col117 117 le_rfl (by norm_num) u v
    · exact colsChunkOK_sound 2 _ _ _ _ f0len 118 1 (by norm_num) InFS2.col118 118 le_rfl (by norm_num) u v
    · exact colsChunkOK_sound 2 _ _ _ _ f0len 119 1 (by norm_num) InFS2.col119 119 le_rfl (by norm_num) u v
    · exact colsChunkOK_sound 2 _ _ _ _ f0len 120 1 (by norm_num) InFS2.col120 120 le_rfl (by norm_num) u v
    · exact colsChunkOK_sound 2 _ _ _ _ f0len 121 1 (by norm_num) InFS2.col121 121 le_rfl (by norm_num) u v
    · exact colsChunkOK_sound 2 _ _ _ _ f0len 122 1 (by norm_num) InFS2.col122 122 le_rfl (by norm_num) u v
    · exact colsChunkOK_sound 2 _ _ _ _ f0len 123 1 (by norm_num) InFS2.col123 123 le_rfl (by norm_num) u v
    · exact colsChunkOK_sound 2 _ _ _ _ f0len 124 1 (by norm_num) InFS2.col124 124 le_rfl (by norm_num) u v
    · exact colsChunkOK_sound 2 _ _ _ _ f0len 125 1 (by norm_num) InFS2.col125 125 le_rfl (by norm_num) u v
    · exact colsChunkOK_sound 2 _ _ _ _ f0len 126 1 (by norm_num) InFS2.col126 126 le_rfl (by norm_num) u v
    · exact colsChunkOK_sound 2 _ _ _ _ f0len 127 1 (by norm_num) InFS2.col127 127 le_rfl (by norm_num) u v
    · exact colsChunkOK_sound 2 _ _ _ _ f0len 128 1 (by norm_num) InFS2.col128 128 le_rfl (by norm_num) u v
    · exact colsChunkOK_sound 2 _ _ _ _ f0len 129 1 (by norm_num) InFS2.col129 129 le_rfl (by norm_num) u v
    · exact colsChunkOK_sound 2 _ _ _ _ f0len 130 1 (by norm_num) InFS2.col130 130 le_rfl (by norm_num) u v
    · exact colsChunkOK_sound 2 _ _ _ _ f0len 131 1 (by norm_num) InFS2.col131 131 le_rfl (by norm_num) u v
    · exact colsChunkOK_sound 2 _ _ _ _ f0len 132 1 (by norm_num) InFS2.col132 132 le_rfl (by norm_num) u v
    · exact colsChunkOK_sound 2 _ _ _ _ f0len 133 1 (by norm_num) InFS2.col133 133 le_rfl (by norm_num) u v
    · exact colsChunkOK_sound 2 _ _ _ _ f0len 134 1 (by norm_num) InFS2.col134 134 le_rfl (by norm_num) u v
    · exact colsChunkOK_sound 2 _ _ _ _ f0len 135 1 (by norm_num) InFS2.col135 135 le_rfl (by norm_num) u v
    · exact colsChunkOK_sound 2 _ _ _ _ f0len 136 1 (by norm_num) InFS2.col136 136 le_rfl (by norm_num) u v
    · exact colsChunkOK_sound 2 _ _ _ _ f0len 137 1 (by norm_num) InFS2.col137 137 le_rfl (by norm_num) u v
    · exact colsChunkOK_sound 2 _ _ _ _ f0len 138 1 (by norm_num) InFS2.col138 138 le_rfl (by norm_num) u v
    · exact colsChunkOK_sound 2 _ _ _ _ f0len 139 1 (by norm_num) InFS2.col139 139 le_rfl (by norm_num) u v
    · exact colsChunkOK_sound 2 _ _ _ _ f0len 140 1 (by norm_num) InFS2.col140 140 le_rfl (by norm_num) u v
    · exact colsChunkOK_sound 2 _ _ _ _ f0len 141 1 (by norm_num) InFS2.col141 141 le_rfl (by norm_num) u v
    · exact colsChunkOK_sound 2 _ _ _ _ f0len 142 1 (by norm_num) InFS2.col142 142 le_rfl (by norm_num) u v
    · exact colsChunkOK_sound 2 _ _ _ _ f0len 143 1 (by norm_num) InFS2.col143 143 le_rfl (by norm_num) u v
    · exact colsChunkOK_sound 2 _ _ _ _ f0len 144 1 (by norm_num) InFS2.col144 144 le_rfl (by norm_num) u v
    · exact colsChunkOK_sound 2 _ _ _ _ f0len 145 1 (by norm_num) InFS2.col145 145 le_rfl (by norm_num) u v
    · exact colsChunkOK_sound 2 _ _ _ _ f0len 146 1 (by norm_num) InFS2.col146 146 le_rfl (by norm_num) u v
    · exact colsChunkOK_sound 2 _ _ _ _ f0len 147 1 (by norm_num) InFS2.col147 147 le_rfl (by norm_num) u v
    · exact colsChunkOK_sound 2 _ _ _ _ f0len 148 1 (by norm_num) InFS2.col148 148 le_rfl (by norm_num) u v
    · exact colsChunkOK_sound 2 _ _ _ _ f0len 149 1 (by norm_num) InFS2.col149 149 le_rfl (by norm_num) u v
    · exact colsChunkOK_sound 2 _ _ _ _ f0len 150 1 (by norm_num) InFS2.col150 150 le_rfl (by norm_num) u v
    · exact colsChunkOK_sound 2 _ _ _ _ f0len 151 1 (by norm_num) InFS2.col151 151 le_rfl (by norm_num) u v
    · exact colsChunkOK_sound 2 _ _ _ _ f0len 152 1 (by norm_num) InFS2.col152 152 le_rfl (by norm_num) u v
    · exact colsChunkOK_sound 2 _ _ _ _ f0len 153 1 (by norm_num) InFS2.col153 153 le_rfl (by norm_num) u v
    · exact colsChunkOK_sound 2 _ _ _ _ f0len 154 1 (by norm_num) InFS2.col154 154 le_rfl (by norm_num) u v
    · exact colsChunkOK_sound 2 _ _ _ _ f0len 155 1 (by norm_num) InFS2.col155 155 le_rfl (by norm_num) u v
    · exact colsChunkOK_sound 2 _ _ _ _ f0len 156 1 (by norm_num) InFS2.col156 156 le_rfl (by norm_num) u v
    · exact colsChunkOK_sound 2 _ _ _ _ f0len 157 1 (by norm_num) InFS2.col157 157 le_rfl (by norm_num) u v
    · exact colsChunkOK_sound 2 _ _ _ _ f0len 158 1 (by norm_num) InFS2.col158 158 le_rfl (by norm_num) u v
    · exact colsChunkOK_sound 2 _ _ _ _ f0len 159 1 (by norm_num) InFS2.col159 159 le_rfl (by norm_num) u v
    · exact colsChunkOK_sound 2 _ _ _ _ f0len 160 1 (by norm_num) InFS2.col160 160 le_rfl (by norm_num) u v
    · exact colsChunkOK_sound 2 _ _ _ _ f0len 161 1 (by norm_num) InFS2.col161 161 le_rfl (by norm_num) u v
    · exact colsChunkOK_sound 2 _ _ _ _ f0len 162 1 (by norm_num) InFS2.col162 162 le_rfl (by norm_num) u v
    · exact colsChunkOK_sound 2 _ _ _ _ f0len 163 1 (by norm_num) InFS2.col163 163 le_rfl (by norm_num) u v
    · exact colsChunkOK_sound 2 _ _ _ _ f0len 164 1 (by norm_num) InFS2.col164 164 le_rfl (by norm_num) u v
    · exact colsChunkOK_sound 2 _ _ _ _ f0len 165 1 (by norm_num) InFS2.col165 165 le_rfl (by norm_num) u v
    · exact colsChunkOK_sound 2 _ _ _ _ f0len 166 1 (by norm_num) InFS2.col166 166 le_rfl (by norm_num) u v
    · exact colsChunkOK_sound 2 _ _ _ _ f0len 167 1 (by norm_num) InFS2.col167 167 le_rfl (by norm_num) u v
    · exact colsChunkOK_sound 2 _ _ _ _ f0len 168 1 (by norm_num) InFS2.col168 168 le_rfl (by norm_num) u v
    · exact colsChunkOK_sound 2 _ _ _ _ f0len 169 1 (by norm_num) InFS2.col169 169 le_rfl (by norm_num) u v
    · exact colsChunkOK_sound 2 _ _ _ _ f0len 170 1 (by norm_num) InFS2.col170 170 le_rfl (by norm_num) u v
    · exact colsChunkOK_sound 2 _ _ _ _ f0len 171 1 (by norm_num) InFS2.col171 171 le_rfl (by norm_num) u v
    · exact colsChunkOK_sound 2 _ _ _ _ f0len 172 1 (by norm_num) InFS2.col172 172 le_rfl (by norm_num) u v
    · exact colsChunkOK_sound 2 _ _ _ _ f0len 173 1 (by norm_num) InFS2.col173 173 le_rfl (by norm_num) u v
    · exact colsChunkOK_sound 2 _ _ _ _ f0len 174 1 (by norm_num) InFS2.col174 174 le_rfl (by norm_num) u v
    · exact colsChunkOK_sound 2 _ _ _ _ f0len 175 1 (by norm_num) InFS2.col175 175 le_rfl (by norm_num) u v
    · exact colsChunkOK_sound 2 _ _ _ _ f0len 176 1 (by norm_num) InFS2.col176 176 le_rfl (by norm_num) u v
    · exact colsChunkOK_sound 2 _ _ _ _ f0len 177 1 (by norm_num) InFS2.col177 177 le_rfl (by norm_num) u v
    · exact colsChunkOK_sound 2 _ _ _ _ f0len 178 1 (by norm_num) InFS2.col178 178 le_rfl (by norm_num) u v
    · exact colsChunkOK_sound 2 _ _ _ _ f0len 179 1 (by norm_num) InFS2.col179 179 le_rfl (by norm_num) u v
    · exact colsChunkOK_sound 2 _ _ _ _ f0len 180 1 (by norm_num) InFS2.col180 180 le_rfl (by norm_num) u v
    · exact colsChunkOK_sound 2 _ _ _ _ f0len 181 1 (by norm_num) InFS2.col181 181 le_rfl (by norm_num) u v
    · exact colsChunkOK_sound 2 _ _ _ _ f0len 182 1 (by norm_num) InFS2.col182 182 le_rfl (by norm_num) u v
    · exact colsChunkOK_sound 2 _ _ _ _ f0len 183 1 (by norm_num) InFS2.col183 183 le_rfl (by norm_num) u v
    · exact colsChunkOK_sound 2 _ _ _ _ f0len 184 1 (by norm_num) InFS2.col184 184 le_rfl (by norm_num) u v
    · exact colsChunkOK_sound 2 _ _ _ _ f0len 185 1 (by norm_num) InFS2.col185 185 le_rfl (by norm_num) u v
    · exact colsChunkOK_sound 2 _ _ _ _ f0len 186 1 (by norm_num) InFS2.col186 186 le_rfl (by norm_num) u v
    · exact colsChunkOK_sound 2 _ _ _ _ f0len 187 1 (by norm_num) InFS2.col187 187 le_rfl (by norm_num) u v
    · exact colsChunkOK_sound 2 _ _ _ _ f0len 188 1 (by norm_num) InFS2.col188 188 le_rfl (by norm_num) u v
    · exact colsChunkOK_sound 2 _ _ _ _ f0len 189 1 (by norm_num) InFS2.col189 189 le_rfl (by norm_num) u v
    · exact colsChunkOK_sound 2 _ _ _ _ f0len 190 1 (by norm_num) InFS2.col190 190 le_rfl (by norm_num) u v
    · exact colsChunkOK_sound 2 _ _ _ _ f0len 191 1 (by norm_num) InFS2.col191 191 le_rfl (by norm_num) u v
    · exact colsChunkOK_sound 2 _ _ _ _ f0len 192 1 (by norm_num) InFS2.col192 192 le_rfl (by norm_num) u v
    · exact colsChunkOK_sound 2 _ _ _ _ f0len 193 1 (by norm_num) InFS2.col193 193 le_rfl (by norm_num) u v
    · exact colsChunkOK_sound 2 _ _ _ _ f0len 194 1 (by norm_num) InFS2.col194 194 le_rfl (by norm_num) u v
    · exact colsChunkOK_sound 2 _ _ _ _ f0len 195 1 (by norm_num) InFS2.col195 195 le_rfl (by norm_num) u v
    · exact colsChunkOK_sound 2 _ _ _ _ f0len 196 1 (by norm_num) InFS2.col196 196 le_rfl (by norm_num) u v
    · exact colsChunkOK_sound 2 _ _ _ _ f0len 197 1 (by norm_num) InFS2.col197 197 le_rfl (by norm_num) u v
    · exact colsChunkOK_sound 2 _ _ _ _ f0len 198 1 (by norm_num) InFS2.col198 198 le_rfl (by norm_num) u v
    · exact colsChunkOK_sound 2 _ _ _ _ f0len 199 1 (by norm_num) InFS2.col199 199 le_rfl (by norm_num) u v
    · exact colsChunkOK_sound 2 _ _ _ _ f0len 200 1 (by norm_num) InFS2.col200 200 le_rfl (by norm_num) u v
    · exact colsChunkOK_sound 2 _ _ _ _ f0len 201 1 (by norm_num) InFS2.col201 201 le_rfl (by norm_num) u v
    · exact colsChunkOK_sound 2 _ _ _ _ f0len 202 1 (by norm_num) InFS2.col202 202 le_rfl (by norm_num) u v
    · exact colsChunkOK_sound 2 _ _ _ _ f0len 203 1 (by norm_num) InFS2.col203 203 le_rfl (by norm_num) u v
    · exact colsChunkOK_sound 2 _ _ _ _ f0len 204 1 (by norm_num) InFS2.col204 204 le_rfl (by norm_num) u v
    · exact colsChunkOK_sound 2 _ _ _ _ f0len 205 1 (by norm_num) InFS2.col205 205 le_rfl (by norm_num) u v
    · exact colsChunkOK_sound 2 _ _ _ _ f0len 206 1 (by norm_num) InFS2.col206 206 le_rfl (by norm_num) u v
    · exact colsChunkOK_sound 2 _ _ _ _ f0len 207 1 (by norm_num) InFS2.col207 207 le_rfl (by norm_num) u v
    · exact colsChunkOK_sound 2 _ _ _ _ f0len 208 1 (by norm_num) InFS2.col208 208 le_rfl (by norm_num) u v
    · exact colsChunkOK_sound 2 _ _ _ _ f0len 209 1 (by norm_num) InFS2.col209 209 le_rfl (by norm_num) u v
    · exact colsChunkOK_sound 2 _ _ _ _ f0len 210 1 (by norm_num) InFS2.col210 210 le_rfl (by norm_num) u v
    · exact colsChunkOK_sound 2 _ _ _ _ f0len 211 1 (by norm_num) InFS2.col211 211 le_rfl (by norm_num) u v
    · exact colsChunkOK_sound 2 _ _ _ _ f0len 212 1 (by norm_num) InFS2.col212 212 le_rfl (by norm_num) u v
    · exact colsChunkOK_sound 2 _ _ _ _ f0len 213 1 (by norm_num) InFS2.col213 213 le_rfl (by norm_num) u v
    · exact colsChunkOK_sound 2 _ _ _ _ f0len 214 1 (by norm_num) InFS2.col214 214 le_rfl (by norm_num) u v
    · exact colsChunkOK_sound 2 _ _ _ _ f0len 215 1 (by norm_num) InFS2.col215 215 le_rfl (by norm_num) u v
    · exact colsChunkOK_sound 2 _ _ _ _ f0len 216 1 (by norm_num) InFS2.col216 216 le_rfl (by norm_num) u v
    · exact colsChunkOK_sound 2 _ _ _ _ f0len 217 1 (by norm_num) InFS2.col217 217 le_rfl (by norm_num) u v
    · exact colsChunkOK_sound 2 _ _ _ _ f0len 218 1 (by norm_num) InFS2.col218 218 le_rfl (by norm_num) u v
    · exact colsChunkOK_sound 2 _ _ _ _ f0len 219 1 (by norm_num) InFS2.col219 219 le_rfl (by norm_num) u v
    · exact colsChunkOK_sound 2 _ _ _ _ f0len 220 1 (by norm_num) InFS2.col220 220 le_rfl (by norm_num) u v
    · exact colsChunkOK_sound 2 _ _ _ _ f0len 221 1 (by norm_num) InFS2.col221 221 le_rfl (by norm_num) u v
    · exact colsChunkOK_sound 2 _ _ _ _ f0len 222 1 (by norm_num) InFS2.col222 222 le_rfl (by norm_num) u v
    · exact colsChunkOK_sound 2 _ _ _ _ f0len 223 1 (by norm_num) InFS2.col223 223 le_rfl (by norm_num) u v
    · exact colsChunkOK_sound 2 _ _ _ _ f0len 224 1 (by norm_num) InFS2.col224 224 le_rfl (by norm_num) u v
    · exact colsChunkOK_sound 2 _ _ _ _ f0len 225 1 (by norm_num) InFS2.col225 225 le_rfl (by norm_num) u v
    · exact colsChunkOK_sound 2 _ _ _ _ f0len 226 1 (by norm_num) InFS2.col226 226 le_rfl (by norm_num) u v
    · exact colsChunkOK_sound 2 _ _ _ _ f0len 227 1 (by norm_num) InFS2.col227 227 le_rfl (by norm_num) u v
    · exact colsChunkOK_sound 2 _ _ _ _ f0len 228 1 (by norm_num) InFS2.col228 228 le_rfl (by norm_num) u v
    · exact colsChunkOK_sound 2 _ _ _ _ f0len 229 1 (by norm_num) InFS2.col229 229 le_rfl (by norm_num) u v
    · exact colsChunkOK_sound 2 _ _ _ _ f0len 230 1 (by norm_num) InFS2.col230 230 le_rfl (by norm_num) u v
    · exact colsChunkOK_sound 2 _ _ _ _ f0len 231 1 (by norm_num) InFS2.col231 231 le_rfl (by norm_num) u v
    · exact colsChunkOK_sound 2 _ _ _ _ f0len 232 1 (by norm_num) InFS2.col232 232 le_rfl (by norm_num) u v
    · exact colsChunkOK_sound 2 _ _ _ _ f0len 233 1 (by norm_num) InFS2.col233 233 le_rfl (by norm_num) u v
    · exact colsChunkOK_sound 2 _ _ _ _ f0len 234 1 (by norm_num) InFS2.col234 234 le_rfl (by norm_num) u v
    · exact colsChunkOK_sound 2 _ _ _ _ f0len 235 1 (by norm_num) InFS2.col235 235 le_rfl (by norm_num) u v
    · exact colsChunkOK_sound 2 _ _ _ _ f0len 236 1 (by norm_num) InFS2.col236 236 le_rfl (by norm_num) u v
    · exact colsChunkOK_sound 2 _ _ _ _ f0len 237 1 (by norm_num) InFS2.col237 237 le_rfl (by norm_num) u v
    · exact colsChunkOK_sound 2 _ _ _ _ f0len 238 1 (by norm_num) InFS2.col238 238 le_rfl (by norm_num) u v
    · exact colsChunkOK_sound 2 _ _ _ _ f0len 239 1 (by norm_num) InFS2.col239 239 le_rfl (by norm_num) u v
    · exact colsChunkOK_sound 2 _ _ _ _ f0len 240 1 (by norm_num) InFS2.col240 240 le_rfl (by norm_num) u v
    · exact colsChunkOK_sound 2 _ _ _ _ f0len 241 1 (by norm_num) InFS2.col241 241 le_rfl (by norm_num) u v
    · exact colsChunkOK_sound 2 _ _ _ _ f0len 242 1 (by norm_num) InFS2.col242 242 le_rfl (by norm_num) u v
    · exact colsChunkOK_sound 2 _ _ _ _ f0len 243 1 (by norm_num) InFS2.col243 243 le_rfl (by norm_num) u v
    · exact colsChunkOK_sound 2 _ _ _ _ f0len 244 1 (by norm_num) InFS2.col244 244 le_rfl (by norm_num) u v
    · exact colsChunkOK_sound 2 _ _ _ _ f0len 245 1 (by norm_num) InFS2.col245 245 le_rfl (by norm_num) u v
    · exact colsChunkOK_sound 2 _ _ _ _ f0len 246 1 (by norm_num) InFS2.col246 246 le_rfl (by norm_num) u v
    · exact colsChunkOK_sound 2 _ _ _ _ f0len 247 1 (by norm_num) InFS2.col247 247 le_rfl (by norm_num) u v
    · exact colsChunkOK_sound 2 _ _ _ _ f0len 248 1 (by norm_num) InFS2.col248 248 le_rfl (by norm_num) u v
    · exact colsChunkOK_sound 2 _ _ _ _ f0len 249 1 (by norm_num) InFS2.col249 249 le_rfl (by norm_num) u v
    · exact colsChunkOK_sound 2 _ _ _ _ f0len 250 1 (by norm_num) InFS2.col250 250 le_rfl (by norm_num) u v
    · exact colsChunkOK_sound 2 _ _ _ _ f0len 251 1 (by norm_num) InFS2.col251 251 le_rfl (by norm_num) u v
    · exact colsChunkOK_sound 2 _ _ _ _ f0len 252 1 (by norm_num) InFS2.col252 252 le_rfl (by norm_num) u v
    · exact colsChunkOK_sound 2 _ _ _ _ f0len 253 1 (by norm_num) InFS2.col253 253 le_rfl (by norm_num) u v
    · exact colsChunkOK_sound 2 _ _ _ _ f0len 254 1 (by norm_num) InFS2.col254 254 le_rfl (by norm_num) u v
    · exact colsChunkOK_sound 2 _ _ _ _ f0len 255 1 (by norm_num) InFS2.col255 255 le_rfl (by norm_num) u v
    · exact colsChunkOK_sound 2 _ _ _ _ f0len 256 1 (by norm_num) InFS2.col256 256 le_rfl (by norm_num) u v
    · exact colsChunkOK_sound 2 _ _ _ _ f0len 257 1 (by norm_num) InFS2.col257 257 le_rfl (by norm_num) u v
    · exact colsChunkOK_sound 2 _ _ _ _ f0len 258 1 (by norm_num) InFS2.col258 258 le_rfl (by norm_num) u v
    · exact colsChunkOK_sound 2 _ _ _ _ f0len 259 1 (by norm_num) InFS2.col259 259 le_rfl (by norm_num) u v
    · exact colsChunkOK_sound 2 _ _ _ _ f0len 260 1 (by norm_num) InFS2.col260 260 le_rfl (by norm_num) u v
    · exact colsChunkOK_sound 2 _ _ _ _ f0len 261 1 (by norm_num) InFS2.col261 261 le_rfl (by norm_num) u v
    · exact colsChunkOK_sound 2 _ _ _ _ f0len 262 1 (by norm_num) InFS2.col262 262 le_rfl (by norm_num) u v
    · exact colsChunkOK_sound 2 _ _ _ _ f0len 263 1 (by norm_num) InFS2.col263 263 le_rfl (by norm_num) u v
    · exact colsChunkOK_sound 2 _ _ _ _ f0len 264 1 (by norm_num) InFS2.col264 264 le_rfl (by norm_num) u v
    · exact colsChunkOK_sound 2 _ _ _ _ f0len 265 1 (by norm_num) InFS2.col265 265 le_rfl (by norm_num) u v
    · exact colsChunkOK_sound 2 _ _ _ _ f0len 266 1 (by norm_num) InFS2.col266 266 le_rfl (by norm_num) u v
    · exact colsChunkOK_sound 2 _ _ _ _ f0len 267 1 (by norm_num) InFS2.col267 267 le_rfl (by norm_num) u v
    · exact colsChunkOK_sound 2 _ _ _ _ f0len 268 1 (by norm_num) InFS2.col268 268 le_rfl (by norm_num) u v
    · exact colsChunkOK_sound 2 _ _ _ _ f0len 269 1 (by norm_num) InFS2.col269 269 le_rfl (by norm_num) u v
    · exact colsChunkOK_sound 2 _ _ _ _ f0len 270 1 (by norm_num) InFS2.col270 270 le_rfl (by norm_num) u v
    · exact colsChunkOK_sound 2 _ _ _ _ f0len 271 1 (by norm_num) InFS2.col271 271 le_rfl (by norm_num) u v
    · exact colsChunkOK_sound 2 _ _ _ _ f0len 272 1 (by norm_num) InFS2.col272 272 le_rfl (by norm_num) u v
    · exact colsChunkOK_sound 2 _ _ _ _ f0len 273 1 (by norm_num) InFS2.col273 273 le_rfl (by norm_num) u v
    · exact colsChunkOK_sound 2 _ _ _ _ f0len 274 1 (by norm_num) InFS2.col274 274 le_rfl (by norm_num) u v
    · exact colsChunkOK_sound 2 _ _ _ _ f0len 275 1 (by norm_num) InFS2.col275 275 le_rfl (by norm_num) u v
    · exact colsChunkOK_sound 2 _ _ _ _ f0len 276 1 (by norm_num) InFS2.col276 276 le_rfl (by norm_num) u v
    · exact colsChunkOK_sound 2 _ _ _ _ f0len 277 1 (by norm_num) InFS2.col277 277 le_rfl (by norm_num) u v
    · exact colsChunkOK_sound 2 _ _ _ _ f0len 278 1 (by norm_num) InFS2.col278 278 le_rfl (by norm_num) u v
    · exact colsChunkOK_sound 2 _ _ _ _ f0len 279 1 (by norm_num) InFS2.col279 279 le_rfl (by norm_num) u v
    · exact colsChunkOK_sound 2 _ _ _ _ f0len 280 1 (by norm_num) InFS2.col280 280 le_rfl (by norm_num) u v
    · exact colsChunkOK_sound 2 _ _ _ _ f0len 281 1 (by norm_num) InFS2.col281 281 le_rfl (by norm_num) u v
  exact key c.val hc

/-- hT0 of `X2.CoreS2g.transfer_unit` and `.transfer_global`, verbatim, for every symmetric source in the source forms of sector 2. -/
theorem hT0 (N : X2Blocks 2) (hN : ∀ k, (N k)ᵀ = N k) (hsrc : InDS2.SrcForm N) :
    ∀ (i : Fin 282) (j : Fin 282) (c : Fin 282), x2EmbedS x2DataConcrete 2 N i j c =
      (ent 384 (384 - 1) (x2Tab CoreS2g.f0 (j.val / 94) c) ((j.val % 94) * 282 + i.val) : ℚ) / 1108531032609225922165724911675932935547910848716289179910144000 :=
  hT0S_of_segs 2 N InDS2.TTd InDS2.TCd InDS2.Zd (InDS2.dirSpec N hN hsrc) labelDecompS_2 typeOKS_2 CoreS2g.f0 segs

end ThreeCopyQutritWerner.X2.InHS2
