module

public import ThreeCopyQutritWerner.CertificateX2SitesCompCheck0_0
public import ThreeCopyQutritWerner.CertificateX2SitesCompCheck0_1
public import ThreeCopyQutritWerner.CertificateX2SitesCompCheck0_2
public import ThreeCopyQutritWerner.CertificateX2SitesCompCheck0_3
public import ThreeCopyQutritWerner.CertificateX2SitesCompCheck0_4
public import ThreeCopyQutritWerner.CertificateX2SitesCompCheck0_5
public import ThreeCopyQutritWerner.CertificateX2SitesCompCheck0_6
public import ThreeCopyQutritWerner.CertificateX2SitesCompCheck0_7
public import ThreeCopyQutritWerner.CertificateX2SitesCompCheck0_8
public import ThreeCopyQutritWerner.CertificateX2SitesCompCheck0_9
public import ThreeCopyQutritWerner.CertificateX2SitesCompCheck0_10
public import ThreeCopyQutritWerner.CertificateX2SitesCompCheck0_11
public import ThreeCopyQutritWerner.CertificateX2SitesCompCheck0_12
public import ThreeCopyQutritWerner.CertificateX2SitesCompCheck0_13
public import ThreeCopyQutritWerner.CertificateX2SitesCompCheck0_14
public import ThreeCopyQutritWerner.CertificateX2SitesCompCheck0_15
public import ThreeCopyQutritWerner.CertificateX2SitesCompCheck0_16
public import ThreeCopyQutritWerner.CertificateX2SitesCompCheck1_0
public import ThreeCopyQutritWerner.CertificateX2SitesCompCheck1_1
public import ThreeCopyQutritWerner.CertificateX2SitesCompCheck1_2
public import ThreeCopyQutritWerner.CertificateX2SitesCompCheck1_3
public import ThreeCopyQutritWerner.CertificateX2SitesCompCheck1_4
public import ThreeCopyQutritWerner.CertificateX2SitesCompCheck1_5
public import ThreeCopyQutritWerner.CertificateX2SitesCompCheck1_6
public import ThreeCopyQutritWerner.CertificateX2SitesCompCheck1_7
public import ThreeCopyQutritWerner.CertificateX2SitesCompCheck1_8
public import ThreeCopyQutritWerner.CertificateX2SitesCompCheck1_9
public import ThreeCopyQutritWerner.CertificateX2SitesCompCheck1_10
public import ThreeCopyQutritWerner.CertificateX2SitesCompCheck1_11
public import ThreeCopyQutritWerner.CertificateX2SitesCompCheck1_12
public import ThreeCopyQutritWerner.CertificateX2SitesCompCheck1_13
public import ThreeCopyQutritWerner.CertificateX2SitesCompCheck1_14
public import ThreeCopyQutritWerner.CertificateX2SitesCompCheck1_15
public import ThreeCopyQutritWerner.CertificateX2SitesCompCheck1_16
public import ThreeCopyQutritWerner.CertificateX2SitesCompCheck2_0
public import ThreeCopyQutritWerner.CertificateX2SitesCompCheck2_1
public import ThreeCopyQutritWerner.CertificateX2SitesCompCheck2_2
public import ThreeCopyQutritWerner.CertificateX2SitesCompCheck2_3
public import ThreeCopyQutritWerner.CertificateX2SitesCompCheck2_4
public import ThreeCopyQutritWerner.CertificateX2SitesCompCheck2_5
public import ThreeCopyQutritWerner.CertificateX2SitesCompCheck2_6
public import ThreeCopyQutritWerner.CertificateX2SitesCompCheck2_7
public import ThreeCopyQutritWerner.CertificateX2SitesCompCheck2_8
public import ThreeCopyQutritWerner.CertificateX2SitesCompCheck2_9
public import ThreeCopyQutritWerner.CertificateX2SitesCompCheck2_10
public import ThreeCopyQutritWerner.CertificateX2SitesCompCheck2_11
public import ThreeCopyQutritWerner.CertificateX2SitesCompCheck2_12
public import ThreeCopyQutritWerner.CertificateX2SitesCompCheck2_13
public import ThreeCopyQutritWerner.CertificateX2SitesCompCheck2_14
public import ThreeCopyQutritWerner.CertificateX2SitesCompCheck2_15
public import ThreeCopyQutritWerner.CertificateX2SitesCompCheck2_16

@[expose] public section


/-! The compressions of the 513 pivot diagrams in the three sectors,
from the chunked kernel checks and `comp_sound`. -/

set_option maxRecDepth 100000

open scoped Matrix

namespace ThreeCopyQutritWerner.X2Sites

open X2

theorem x2sComp0_check (p : Fin 513) :
    finish (offset 48 (48 - 1) 513) (x2sComp0.getD p 0)
      (scanM x2sMask0 x2sTys0 (3 ^ (rowPos x2sS0 (x2SitesPerm (x2SitesPiv p)) 0 : ℕ)) (3 ^ (rowPos x2sS0 (x2SitesPerm (x2SitesPiv p)) 1 : ℕ)) (3 ^ (rowPos x2sS0 (x2SitesPerm (x2SitesPiv p)) 2 : ℕ)) (3 ^ (rowPos x2sS0 (x2SitesPerm (x2SitesPiv p)) 3 : ℕ)) (3 ^ (rowPos x2sS0 (x2SitesPerm (x2SitesPiv p)) 4 : ℕ)) (3 ^ (rowPos x2sS0 (x2SitesPerm (x2SitesPiv p)) 5 : ℕ))
        (3 ^ (colPos x2sS0 (x2SitesPerm (x2SitesPiv p)) 0 : ℕ)) (3 ^ (colPos x2sS0 (x2SitesPerm (x2SitesPiv p)) 1 : ℕ)) (3 ^ (colPos x2sS0 (x2SitesPerm (x2SitesPiv p)) 2 : ℕ)) (3 ^ (colPos x2sS0 (x2SitesPerm (x2SitesPiv p)) 3 : ℕ)) (3 ^ (colPos x2sS0 (x2SitesPerm (x2SitesPiv p)) 4 : ℕ)) (3 ^ (colPos x2sS0 (x2SitesPerm (x2SitesPiv p)) 5 : ℕ)) 729 (0, 0)) = true := by
  by_cases h0 : (p : ℕ) < 8
  · exact x2sComp0_check0 p h0
  by_cases h1 : (p : ℕ) < 16
  · exact x2sComp0_check1 p (by omega) h1
  by_cases h2 : (p : ℕ) < 24
  · exact x2sComp0_check2 p (by omega) h2
  by_cases h3 : (p : ℕ) < 32
  · exact x2sComp0_check3 p (by omega) h3
  by_cases h4 : (p : ℕ) < 40
  · exact x2sComp0_check4 p (by omega) h4
  by_cases h5 : (p : ℕ) < 48
  · exact x2sComp0_check5 p (by omega) h5
  by_cases h6 : (p : ℕ) < 56
  · exact x2sComp0_check6 p (by omega) h6
  by_cases h7 : (p : ℕ) < 64
  · exact x2sComp0_check7 p (by omega) h7
  by_cases h8 : (p : ℕ) < 72
  · exact x2sComp0_check8 p (by omega) h8
  by_cases h9 : (p : ℕ) < 80
  · exact x2sComp0_check9 p (by omega) h9
  by_cases h10 : (p : ℕ) < 88
  · exact x2sComp0_check10 p (by omega) h10
  by_cases h11 : (p : ℕ) < 96
  · exact x2sComp0_check11 p (by omega) h11
  by_cases h12 : (p : ℕ) < 104
  · exact x2sComp0_check12 p (by omega) h12
  by_cases h13 : (p : ℕ) < 112
  · exact x2sComp0_check13 p (by omega) h13
  by_cases h14 : (p : ℕ) < 120
  · exact x2sComp0_check14 p (by omega) h14
  by_cases h15 : (p : ℕ) < 128
  · exact x2sComp0_check15 p (by omega) h15
  by_cases h16 : (p : ℕ) < 136
  · exact x2sComp0_check16 p (by omega) h16
  by_cases h17 : (p : ℕ) < 144
  · exact x2sComp0_check17 p (by omega) h17
  by_cases h18 : (p : ℕ) < 152
  · exact x2sComp0_check18 p (by omega) h18
  by_cases h19 : (p : ℕ) < 160
  · exact x2sComp0_check19 p (by omega) h19
  by_cases h20 : (p : ℕ) < 168
  · exact x2sComp0_check20 p (by omega) h20
  by_cases h21 : (p : ℕ) < 176
  · exact x2sComp0_check21 p (by omega) h21
  by_cases h22 : (p : ℕ) < 184
  · exact x2sComp0_check22 p (by omega) h22
  by_cases h23 : (p : ℕ) < 192
  · exact x2sComp0_check23 p (by omega) h23
  by_cases h24 : (p : ℕ) < 200
  · exact x2sComp0_check24 p (by omega) h24
  by_cases h25 : (p : ℕ) < 208
  · exact x2sComp0_check25 p (by omega) h25
  by_cases h26 : (p : ℕ) < 216
  · exact x2sComp0_check26 p (by omega) h26
  by_cases h27 : (p : ℕ) < 224
  · exact x2sComp0_check27 p (by omega) h27
  by_cases h28 : (p : ℕ) < 232
  · exact x2sComp0_check28 p (by omega) h28
  by_cases h29 : (p : ℕ) < 240
  · exact x2sComp0_check29 p (by omega) h29
  by_cases h30 : (p : ℕ) < 248
  · exact x2sComp0_check30 p (by omega) h30
  by_cases h31 : (p : ℕ) < 256
  · exact x2sComp0_check31 p (by omega) h31
  by_cases h32 : (p : ℕ) < 264
  · exact x2sComp0_check32 p (by omega) h32
  by_cases h33 : (p : ℕ) < 272
  · exact x2sComp0_check33 p (by omega) h33
  by_cases h34 : (p : ℕ) < 280
  · exact x2sComp0_check34 p (by omega) h34
  by_cases h35 : (p : ℕ) < 288
  · exact x2sComp0_check35 p (by omega) h35
  by_cases h36 : (p : ℕ) < 296
  · exact x2sComp0_check36 p (by omega) h36
  by_cases h37 : (p : ℕ) < 304
  · exact x2sComp0_check37 p (by omega) h37
  by_cases h38 : (p : ℕ) < 312
  · exact x2sComp0_check38 p (by omega) h38
  by_cases h39 : (p : ℕ) < 320
  · exact x2sComp0_check39 p (by omega) h39
  by_cases h40 : (p : ℕ) < 328
  · exact x2sComp0_check40 p (by omega) h40
  by_cases h41 : (p : ℕ) < 336
  · exact x2sComp0_check41 p (by omega) h41
  by_cases h42 : (p : ℕ) < 344
  · exact x2sComp0_check42 p (by omega) h42
  by_cases h43 : (p : ℕ) < 352
  · exact x2sComp0_check43 p (by omega) h43
  by_cases h44 : (p : ℕ) < 360
  · exact x2sComp0_check44 p (by omega) h44
  by_cases h45 : (p : ℕ) < 368
  · exact x2sComp0_check45 p (by omega) h45
  by_cases h46 : (p : ℕ) < 376
  · exact x2sComp0_check46 p (by omega) h46
  by_cases h47 : (p : ℕ) < 384
  · exact x2sComp0_check47 p (by omega) h47
  by_cases h48 : (p : ℕ) < 392
  · exact x2sComp0_check48 p (by omega) h48
  by_cases h49 : (p : ℕ) < 400
  · exact x2sComp0_check49 p (by omega) h49
  by_cases h50 : (p : ℕ) < 408
  · exact x2sComp0_check50 p (by omega) h50
  by_cases h51 : (p : ℕ) < 416
  · exact x2sComp0_check51 p (by omega) h51
  by_cases h52 : (p : ℕ) < 424
  · exact x2sComp0_check52 p (by omega) h52
  by_cases h53 : (p : ℕ) < 432
  · exact x2sComp0_check53 p (by omega) h53
  by_cases h54 : (p : ℕ) < 440
  · exact x2sComp0_check54 p (by omega) h54
  by_cases h55 : (p : ℕ) < 448
  · exact x2sComp0_check55 p (by omega) h55
  by_cases h56 : (p : ℕ) < 456
  · exact x2sComp0_check56 p (by omega) h56
  by_cases h57 : (p : ℕ) < 464
  · exact x2sComp0_check57 p (by omega) h57
  by_cases h58 : (p : ℕ) < 472
  · exact x2sComp0_check58 p (by omega) h58
  by_cases h59 : (p : ℕ) < 480
  · exact x2sComp0_check59 p (by omega) h59
  by_cases h60 : (p : ℕ) < 488
  · exact x2sComp0_check60 p (by omega) h60
  by_cases h61 : (p : ℕ) < 496
  · exact x2sComp0_check61 p (by omega) h61
  by_cases h62 : (p : ℕ) < 504
  · exact x2sComp0_check62 p (by omega) h62
  by_cases h63 : (p : ℕ) < 512
  · exact x2sComp0_check63 p (by omega) h63
  · exact x2sComp0_check64 p (by omega) p.isLt

/-- Sector 0: the compression of pivot diagram `p` on the frame of type `t` is slot
`off t + i m_t + j` of fiber `p` (48-bit slots, offset `2^47`). -/
theorem x2sComp0_spec (p : Fin 513) (t : Fin 7) (i j : Fin (certificateDescendantFrames2SourceSize t)) :
    ((certificateMatrixFromSparseEntries (x2sE0 t))ᵀ *
      certificateLocalDiagram (n := Fin 3) (R := ℤ) x2sS0 (x2SitesPerm (x2SitesPiv p)) *
        certificateMatrixFromSparseEntries (x2sE0 t)) i j =
      ent 48 (48 - 1) (x2sComp0.getD p 0) (x2sOff0 t + i * certificateDescendantFrames2SourceSize t + j) :=
  comp_sound 48 513 (by norm_num) certificateDescendantFrames2SourceSize x2sE0 x2sOff0 300 x2sE0_absSum (by norm_num) x2s0_big
    (layout_lt _ _ 513 x2s0_end) (layout_inj _ _ x2s0_step) x2sS0 (x2SitesPerm (x2SitesPiv p)) _
    (x2sComp0_check p) t i j

theorem x2sComp1_check (p : Fin 513) :
    finish (offset 48 (48 - 1) 513) (x2sComp1.getD p 0)
      (scanM x2sMask1 x2sTys1 (3 ^ (rowPos x2sS1 (x2SitesPerm (x2SitesPiv p)) 0 : ℕ)) (3 ^ (rowPos x2sS1 (x2SitesPerm (x2SitesPiv p)) 1 : ℕ)) (3 ^ (rowPos x2sS1 (x2SitesPerm (x2SitesPiv p)) 2 : ℕ)) (3 ^ (rowPos x2sS1 (x2SitesPerm (x2SitesPiv p)) 3 : ℕ)) (3 ^ (rowPos x2sS1 (x2SitesPerm (x2SitesPiv p)) 4 : ℕ)) (3 ^ (rowPos x2sS1 (x2SitesPerm (x2SitesPiv p)) 5 : ℕ))
        (3 ^ (colPos x2sS1 (x2SitesPerm (x2SitesPiv p)) 0 : ℕ)) (3 ^ (colPos x2sS1 (x2SitesPerm (x2SitesPiv p)) 1 : ℕ)) (3 ^ (colPos x2sS1 (x2SitesPerm (x2SitesPiv p)) 2 : ℕ)) (3 ^ (colPos x2sS1 (x2SitesPerm (x2SitesPiv p)) 3 : ℕ)) (3 ^ (colPos x2sS1 (x2SitesPerm (x2SitesPiv p)) 4 : ℕ)) (3 ^ (colPos x2sS1 (x2SitesPerm (x2SitesPiv p)) 5 : ℕ)) 729 (0, 0)) = true := by
  by_cases h0 : (p : ℕ) < 8
  · exact x2sComp1_check0 p h0
  by_cases h1 : (p : ℕ) < 16
  · exact x2sComp1_check1 p (by omega) h1
  by_cases h2 : (p : ℕ) < 24
  · exact x2sComp1_check2 p (by omega) h2
  by_cases h3 : (p : ℕ) < 32
  · exact x2sComp1_check3 p (by omega) h3
  by_cases h4 : (p : ℕ) < 40
  · exact x2sComp1_check4 p (by omega) h4
  by_cases h5 : (p : ℕ) < 48
  · exact x2sComp1_check5 p (by omega) h5
  by_cases h6 : (p : ℕ) < 56
  · exact x2sComp1_check6 p (by omega) h6
  by_cases h7 : (p : ℕ) < 64
  · exact x2sComp1_check7 p (by omega) h7
  by_cases h8 : (p : ℕ) < 72
  · exact x2sComp1_check8 p (by omega) h8
  by_cases h9 : (p : ℕ) < 80
  · exact x2sComp1_check9 p (by omega) h9
  by_cases h10 : (p : ℕ) < 88
  · exact x2sComp1_check10 p (by omega) h10
  by_cases h11 : (p : ℕ) < 96
  · exact x2sComp1_check11 p (by omega) h11
  by_cases h12 : (p : ℕ) < 104
  · exact x2sComp1_check12 p (by omega) h12
  by_cases h13 : (p : ℕ) < 112
  · exact x2sComp1_check13 p (by omega) h13
  by_cases h14 : (p : ℕ) < 120
  · exact x2sComp1_check14 p (by omega) h14
  by_cases h15 : (p : ℕ) < 128
  · exact x2sComp1_check15 p (by omega) h15
  by_cases h16 : (p : ℕ) < 136
  · exact x2sComp1_check16 p (by omega) h16
  by_cases h17 : (p : ℕ) < 144
  · exact x2sComp1_check17 p (by omega) h17
  by_cases h18 : (p : ℕ) < 152
  · exact x2sComp1_check18 p (by omega) h18
  by_cases h19 : (p : ℕ) < 160
  · exact x2sComp1_check19 p (by omega) h19
  by_cases h20 : (p : ℕ) < 168
  · exact x2sComp1_check20 p (by omega) h20
  by_cases h21 : (p : ℕ) < 176
  · exact x2sComp1_check21 p (by omega) h21
  by_cases h22 : (p : ℕ) < 184
  · exact x2sComp1_check22 p (by omega) h22
  by_cases h23 : (p : ℕ) < 192
  · exact x2sComp1_check23 p (by omega) h23
  by_cases h24 : (p : ℕ) < 200
  · exact x2sComp1_check24 p (by omega) h24
  by_cases h25 : (p : ℕ) < 208
  · exact x2sComp1_check25 p (by omega) h25
  by_cases h26 : (p : ℕ) < 216
  · exact x2sComp1_check26 p (by omega) h26
  by_cases h27 : (p : ℕ) < 224
  · exact x2sComp1_check27 p (by omega) h27
  by_cases h28 : (p : ℕ) < 232
  · exact x2sComp1_check28 p (by omega) h28
  by_cases h29 : (p : ℕ) < 240
  · exact x2sComp1_check29 p (by omega) h29
  by_cases h30 : (p : ℕ) < 248
  · exact x2sComp1_check30 p (by omega) h30
  by_cases h31 : (p : ℕ) < 256
  · exact x2sComp1_check31 p (by omega) h31
  by_cases h32 : (p : ℕ) < 264
  · exact x2sComp1_check32 p (by omega) h32
  by_cases h33 : (p : ℕ) < 272
  · exact x2sComp1_check33 p (by omega) h33
  by_cases h34 : (p : ℕ) < 280
  · exact x2sComp1_check34 p (by omega) h34
  by_cases h35 : (p : ℕ) < 288
  · exact x2sComp1_check35 p (by omega) h35
  by_cases h36 : (p : ℕ) < 296
  · exact x2sComp1_check36 p (by omega) h36
  by_cases h37 : (p : ℕ) < 304
  · exact x2sComp1_check37 p (by omega) h37
  by_cases h38 : (p : ℕ) < 312
  · exact x2sComp1_check38 p (by omega) h38
  by_cases h39 : (p : ℕ) < 320
  · exact x2sComp1_check39 p (by omega) h39
  by_cases h40 : (p : ℕ) < 328
  · exact x2sComp1_check40 p (by omega) h40
  by_cases h41 : (p : ℕ) < 336
  · exact x2sComp1_check41 p (by omega) h41
  by_cases h42 : (p : ℕ) < 344
  · exact x2sComp1_check42 p (by omega) h42
  by_cases h43 : (p : ℕ) < 352
  · exact x2sComp1_check43 p (by omega) h43
  by_cases h44 : (p : ℕ) < 360
  · exact x2sComp1_check44 p (by omega) h44
  by_cases h45 : (p : ℕ) < 368
  · exact x2sComp1_check45 p (by omega) h45
  by_cases h46 : (p : ℕ) < 376
  · exact x2sComp1_check46 p (by omega) h46
  by_cases h47 : (p : ℕ) < 384
  · exact x2sComp1_check47 p (by omega) h47
  by_cases h48 : (p : ℕ) < 392
  · exact x2sComp1_check48 p (by omega) h48
  by_cases h49 : (p : ℕ) < 400
  · exact x2sComp1_check49 p (by omega) h49
  by_cases h50 : (p : ℕ) < 408
  · exact x2sComp1_check50 p (by omega) h50
  by_cases h51 : (p : ℕ) < 416
  · exact x2sComp1_check51 p (by omega) h51
  by_cases h52 : (p : ℕ) < 424
  · exact x2sComp1_check52 p (by omega) h52
  by_cases h53 : (p : ℕ) < 432
  · exact x2sComp1_check53 p (by omega) h53
  by_cases h54 : (p : ℕ) < 440
  · exact x2sComp1_check54 p (by omega) h54
  by_cases h55 : (p : ℕ) < 448
  · exact x2sComp1_check55 p (by omega) h55
  by_cases h56 : (p : ℕ) < 456
  · exact x2sComp1_check56 p (by omega) h56
  by_cases h57 : (p : ℕ) < 464
  · exact x2sComp1_check57 p (by omega) h57
  by_cases h58 : (p : ℕ) < 472
  · exact x2sComp1_check58 p (by omega) h58
  by_cases h59 : (p : ℕ) < 480
  · exact x2sComp1_check59 p (by omega) h59
  by_cases h60 : (p : ℕ) < 488
  · exact x2sComp1_check60 p (by omega) h60
  by_cases h61 : (p : ℕ) < 496
  · exact x2sComp1_check61 p (by omega) h61
  by_cases h62 : (p : ℕ) < 504
  · exact x2sComp1_check62 p (by omega) h62
  by_cases h63 : (p : ℕ) < 512
  · exact x2sComp1_check63 p (by omega) h63
  · exact x2sComp1_check64 p (by omega) p.isLt

/-- Sector 1: the compression of pivot diagram `p` on the frame of type `t` is slot
`off t + i m_t + j` of fiber `p` (48-bit slots, offset `2^47`). -/
theorem x2sComp1_spec (p : Fin 513) (t : Fin 8) (i j : Fin (certificateDescendantFrames1SourceSize t)) :
    ((certificateMatrixFromSparseEntries (x2sE1 t))ᵀ *
      certificateLocalDiagram (n := Fin 3) (R := ℤ) x2sS1 (x2SitesPerm (x2SitesPiv p)) *
        certificateMatrixFromSparseEntries (x2sE1 t)) i j =
      ent 48 (48 - 1) (x2sComp1.getD p 0) (x2sOff1 t + i * certificateDescendantFrames1SourceSize t + j) :=
  comp_sound 48 513 (by norm_num) certificateDescendantFrames1SourceSize x2sE1 x2sOff1 300 x2sE1_absSum (by norm_num) x2s1_big
    (layout_lt _ _ 513 x2s1_end) (layout_inj _ _ x2s1_step) x2sS1 (x2SitesPerm (x2SitesPiv p)) _
    (x2sComp1_check p) t i j

theorem x2sComp2_check (p : Fin 513) :
    finish (offset 48 (48 - 1) 513) (x2sComp2.getD p 0)
      (scanM x2sMask2 x2sTys2 (3 ^ (rowPos x2sS2 (x2SitesPerm (x2SitesPiv p)) 0 : ℕ)) (3 ^ (rowPos x2sS2 (x2SitesPerm (x2SitesPiv p)) 1 : ℕ)) (3 ^ (rowPos x2sS2 (x2SitesPerm (x2SitesPiv p)) 2 : ℕ)) (3 ^ (rowPos x2sS2 (x2SitesPerm (x2SitesPiv p)) 3 : ℕ)) (3 ^ (rowPos x2sS2 (x2SitesPerm (x2SitesPiv p)) 4 : ℕ)) (3 ^ (rowPos x2sS2 (x2SitesPerm (x2SitesPiv p)) 5 : ℕ))
        (3 ^ (colPos x2sS2 (x2SitesPerm (x2SitesPiv p)) 0 : ℕ)) (3 ^ (colPos x2sS2 (x2SitesPerm (x2SitesPiv p)) 1 : ℕ)) (3 ^ (colPos x2sS2 (x2SitesPerm (x2SitesPiv p)) 2 : ℕ)) (3 ^ (colPos x2sS2 (x2SitesPerm (x2SitesPiv p)) 3 : ℕ)) (3 ^ (colPos x2sS2 (x2SitesPerm (x2SitesPiv p)) 4 : ℕ)) (3 ^ (colPos x2sS2 (x2SitesPerm (x2SitesPiv p)) 5 : ℕ)) 729 (0, 0)) = true := by
  by_cases h0 : (p : ℕ) < 8
  · exact x2sComp2_check0 p h0
  by_cases h1 : (p : ℕ) < 16
  · exact x2sComp2_check1 p (by omega) h1
  by_cases h2 : (p : ℕ) < 24
  · exact x2sComp2_check2 p (by omega) h2
  by_cases h3 : (p : ℕ) < 32
  · exact x2sComp2_check3 p (by omega) h3
  by_cases h4 : (p : ℕ) < 40
  · exact x2sComp2_check4 p (by omega) h4
  by_cases h5 : (p : ℕ) < 48
  · exact x2sComp2_check5 p (by omega) h5
  by_cases h6 : (p : ℕ) < 56
  · exact x2sComp2_check6 p (by omega) h6
  by_cases h7 : (p : ℕ) < 64
  · exact x2sComp2_check7 p (by omega) h7
  by_cases h8 : (p : ℕ) < 72
  · exact x2sComp2_check8 p (by omega) h8
  by_cases h9 : (p : ℕ) < 80
  · exact x2sComp2_check9 p (by omega) h9
  by_cases h10 : (p : ℕ) < 88
  · exact x2sComp2_check10 p (by omega) h10
  by_cases h11 : (p : ℕ) < 96
  · exact x2sComp2_check11 p (by omega) h11
  by_cases h12 : (p : ℕ) < 104
  · exact x2sComp2_check12 p (by omega) h12
  by_cases h13 : (p : ℕ) < 112
  · exact x2sComp2_check13 p (by omega) h13
  by_cases h14 : (p : ℕ) < 120
  · exact x2sComp2_check14 p (by omega) h14
  by_cases h15 : (p : ℕ) < 128
  · exact x2sComp2_check15 p (by omega) h15
  by_cases h16 : (p : ℕ) < 136
  · exact x2sComp2_check16 p (by omega) h16
  by_cases h17 : (p : ℕ) < 144
  · exact x2sComp2_check17 p (by omega) h17
  by_cases h18 : (p : ℕ) < 152
  · exact x2sComp2_check18 p (by omega) h18
  by_cases h19 : (p : ℕ) < 160
  · exact x2sComp2_check19 p (by omega) h19
  by_cases h20 : (p : ℕ) < 168
  · exact x2sComp2_check20 p (by omega) h20
  by_cases h21 : (p : ℕ) < 176
  · exact x2sComp2_check21 p (by omega) h21
  by_cases h22 : (p : ℕ) < 184
  · exact x2sComp2_check22 p (by omega) h22
  by_cases h23 : (p : ℕ) < 192
  · exact x2sComp2_check23 p (by omega) h23
  by_cases h24 : (p : ℕ) < 200
  · exact x2sComp2_check24 p (by omega) h24
  by_cases h25 : (p : ℕ) < 208
  · exact x2sComp2_check25 p (by omega) h25
  by_cases h26 : (p : ℕ) < 216
  · exact x2sComp2_check26 p (by omega) h26
  by_cases h27 : (p : ℕ) < 224
  · exact x2sComp2_check27 p (by omega) h27
  by_cases h28 : (p : ℕ) < 232
  · exact x2sComp2_check28 p (by omega) h28
  by_cases h29 : (p : ℕ) < 240
  · exact x2sComp2_check29 p (by omega) h29
  by_cases h30 : (p : ℕ) < 248
  · exact x2sComp2_check30 p (by omega) h30
  by_cases h31 : (p : ℕ) < 256
  · exact x2sComp2_check31 p (by omega) h31
  by_cases h32 : (p : ℕ) < 264
  · exact x2sComp2_check32 p (by omega) h32
  by_cases h33 : (p : ℕ) < 272
  · exact x2sComp2_check33 p (by omega) h33
  by_cases h34 : (p : ℕ) < 280
  · exact x2sComp2_check34 p (by omega) h34
  by_cases h35 : (p : ℕ) < 288
  · exact x2sComp2_check35 p (by omega) h35
  by_cases h36 : (p : ℕ) < 296
  · exact x2sComp2_check36 p (by omega) h36
  by_cases h37 : (p : ℕ) < 304
  · exact x2sComp2_check37 p (by omega) h37
  by_cases h38 : (p : ℕ) < 312
  · exact x2sComp2_check38 p (by omega) h38
  by_cases h39 : (p : ℕ) < 320
  · exact x2sComp2_check39 p (by omega) h39
  by_cases h40 : (p : ℕ) < 328
  · exact x2sComp2_check40 p (by omega) h40
  by_cases h41 : (p : ℕ) < 336
  · exact x2sComp2_check41 p (by omega) h41
  by_cases h42 : (p : ℕ) < 344
  · exact x2sComp2_check42 p (by omega) h42
  by_cases h43 : (p : ℕ) < 352
  · exact x2sComp2_check43 p (by omega) h43
  by_cases h44 : (p : ℕ) < 360
  · exact x2sComp2_check44 p (by omega) h44
  by_cases h45 : (p : ℕ) < 368
  · exact x2sComp2_check45 p (by omega) h45
  by_cases h46 : (p : ℕ) < 376
  · exact x2sComp2_check46 p (by omega) h46
  by_cases h47 : (p : ℕ) < 384
  · exact x2sComp2_check47 p (by omega) h47
  by_cases h48 : (p : ℕ) < 392
  · exact x2sComp2_check48 p (by omega) h48
  by_cases h49 : (p : ℕ) < 400
  · exact x2sComp2_check49 p (by omega) h49
  by_cases h50 : (p : ℕ) < 408
  · exact x2sComp2_check50 p (by omega) h50
  by_cases h51 : (p : ℕ) < 416
  · exact x2sComp2_check51 p (by omega) h51
  by_cases h52 : (p : ℕ) < 424
  · exact x2sComp2_check52 p (by omega) h52
  by_cases h53 : (p : ℕ) < 432
  · exact x2sComp2_check53 p (by omega) h53
  by_cases h54 : (p : ℕ) < 440
  · exact x2sComp2_check54 p (by omega) h54
  by_cases h55 : (p : ℕ) < 448
  · exact x2sComp2_check55 p (by omega) h55
  by_cases h56 : (p : ℕ) < 456
  · exact x2sComp2_check56 p (by omega) h56
  by_cases h57 : (p : ℕ) < 464
  · exact x2sComp2_check57 p (by omega) h57
  by_cases h58 : (p : ℕ) < 472
  · exact x2sComp2_check58 p (by omega) h58
  by_cases h59 : (p : ℕ) < 480
  · exact x2sComp2_check59 p (by omega) h59
  by_cases h60 : (p : ℕ) < 488
  · exact x2sComp2_check60 p (by omega) h60
  by_cases h61 : (p : ℕ) < 496
  · exact x2sComp2_check61 p (by omega) h61
  by_cases h62 : (p : ℕ) < 504
  · exact x2sComp2_check62 p (by omega) h62
  by_cases h63 : (p : ℕ) < 512
  · exact x2sComp2_check63 p (by omega) h63
  · exact x2sComp2_check64 p (by omega) p.isLt

/-- Sector 2: the compression of pivot diagram `p` on the frame of type `t` is slot
`off t + i m_t + j` of fiber `p` (48-bit slots, offset `2^47`). -/
theorem x2sComp2_spec (p : Fin 513) (t : Fin 7) (i j : Fin (certificateDescendantFrames2SourceSize t)) :
    ((certificateMatrixFromSparseEntries (x2sE2 t))ᵀ *
      certificateLocalDiagram (n := Fin 3) (R := ℤ) x2sS2 (x2SitesPerm (x2SitesPiv p)) *
        certificateMatrixFromSparseEntries (x2sE2 t)) i j =
      ent 48 (48 - 1) (x2sComp2.getD p 0) (x2sOff0 t + i * certificateDescendantFrames2SourceSize t + j) :=
  comp_sound 48 513 (by norm_num) certificateDescendantFrames2SourceSize x2sE2 x2sOff0 300 x2sE2_absSum (by norm_num) x2s0_big
    (layout_lt _ _ 513 x2s0_end) (layout_inj _ _ x2s0_step) x2sS2 (x2SitesPerm (x2SitesPiv p)) _
    (x2sComp2_check p) t i j

end ThreeCopyQutritWerner.X2Sites
