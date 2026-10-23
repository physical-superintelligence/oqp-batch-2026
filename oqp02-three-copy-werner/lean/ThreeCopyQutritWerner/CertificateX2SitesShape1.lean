module

public import ThreeCopyQutritWerner.CertificateX2SitesCompData1
public import ThreeCopyQutritWerner.CertificateX2SitesFiberOK

@[expose] public section


/-! Range and slot bounds of the sector-1 compression fibers (kernel), 16 fibers
per declaration. -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option profiler true
set_option profiler.threshold 1000

namespace ThreeCopyQutritWerner.X2Sites

open X2

theorem x2sComp1_len : x2sComp1.length = 513 := by decide +kernel

theorem x2sComp1_fib0 : ∀ p < 513, 0 ≤ p → p < 16 → fiberOK (x2sComp1.getD p 0) = true := by
  decide +kernel

theorem x2sComp1_fib1 : ∀ p < 513, 16 ≤ p → p < 32 → fiberOK (x2sComp1.getD p 0) = true := by
  decide +kernel

theorem x2sComp1_fib2 : ∀ p < 513, 32 ≤ p → p < 48 → fiberOK (x2sComp1.getD p 0) = true := by
  decide +kernel

theorem x2sComp1_fib3 : ∀ p < 513, 48 ≤ p → p < 64 → fiberOK (x2sComp1.getD p 0) = true := by
  decide +kernel

theorem x2sComp1_fib4 : ∀ p < 513, 64 ≤ p → p < 80 → fiberOK (x2sComp1.getD p 0) = true := by
  decide +kernel

theorem x2sComp1_fib5 : ∀ p < 513, 80 ≤ p → p < 96 → fiberOK (x2sComp1.getD p 0) = true := by
  decide +kernel

theorem x2sComp1_fib6 : ∀ p < 513, 96 ≤ p → p < 112 → fiberOK (x2sComp1.getD p 0) = true := by
  decide +kernel

theorem x2sComp1_fib7 : ∀ p < 513, 112 ≤ p → p < 128 → fiberOK (x2sComp1.getD p 0) = true := by
  decide +kernel

theorem x2sComp1_fib8 : ∀ p < 513, 128 ≤ p → p < 144 → fiberOK (x2sComp1.getD p 0) = true := by
  decide +kernel

theorem x2sComp1_fib9 : ∀ p < 513, 144 ≤ p → p < 160 → fiberOK (x2sComp1.getD p 0) = true := by
  decide +kernel

theorem x2sComp1_fib10 : ∀ p < 513, 160 ≤ p → p < 176 → fiberOK (x2sComp1.getD p 0) = true := by
  decide +kernel

theorem x2sComp1_fib11 : ∀ p < 513, 176 ≤ p → p < 192 → fiberOK (x2sComp1.getD p 0) = true := by
  decide +kernel

theorem x2sComp1_fib12 : ∀ p < 513, 192 ≤ p → p < 208 → fiberOK (x2sComp1.getD p 0) = true := by
  decide +kernel

theorem x2sComp1_fib13 : ∀ p < 513, 208 ≤ p → p < 224 → fiberOK (x2sComp1.getD p 0) = true := by
  decide +kernel

theorem x2sComp1_fib14 : ∀ p < 513, 224 ≤ p → p < 240 → fiberOK (x2sComp1.getD p 0) = true := by
  decide +kernel

theorem x2sComp1_fib15 : ∀ p < 513, 240 ≤ p → p < 256 → fiberOK (x2sComp1.getD p 0) = true := by
  decide +kernel

theorem x2sComp1_fib16 : ∀ p < 513, 256 ≤ p → p < 272 → fiberOK (x2sComp1.getD p 0) = true := by
  decide +kernel

theorem x2sComp1_fib17 : ∀ p < 513, 272 ≤ p → p < 288 → fiberOK (x2sComp1.getD p 0) = true := by
  decide +kernel

theorem x2sComp1_fib18 : ∀ p < 513, 288 ≤ p → p < 304 → fiberOK (x2sComp1.getD p 0) = true := by
  decide +kernel

theorem x2sComp1_fib19 : ∀ p < 513, 304 ≤ p → p < 320 → fiberOK (x2sComp1.getD p 0) = true := by
  decide +kernel

theorem x2sComp1_fib20 : ∀ p < 513, 320 ≤ p → p < 336 → fiberOK (x2sComp1.getD p 0) = true := by
  decide +kernel

theorem x2sComp1_fib21 : ∀ p < 513, 336 ≤ p → p < 352 → fiberOK (x2sComp1.getD p 0) = true := by
  decide +kernel

theorem x2sComp1_fib22 : ∀ p < 513, 352 ≤ p → p < 368 → fiberOK (x2sComp1.getD p 0) = true := by
  decide +kernel

theorem x2sComp1_fib23 : ∀ p < 513, 368 ≤ p → p < 384 → fiberOK (x2sComp1.getD p 0) = true := by
  decide +kernel

theorem x2sComp1_fib24 : ∀ p < 513, 384 ≤ p → p < 400 → fiberOK (x2sComp1.getD p 0) = true := by
  decide +kernel

theorem x2sComp1_fib25 : ∀ p < 513, 400 ≤ p → p < 416 → fiberOK (x2sComp1.getD p 0) = true := by
  decide +kernel

theorem x2sComp1_fib26 : ∀ p < 513, 416 ≤ p → p < 432 → fiberOK (x2sComp1.getD p 0) = true := by
  decide +kernel

theorem x2sComp1_fib27 : ∀ p < 513, 432 ≤ p → p < 448 → fiberOK (x2sComp1.getD p 0) = true := by
  decide +kernel

theorem x2sComp1_fib28 : ∀ p < 513, 448 ≤ p → p < 464 → fiberOK (x2sComp1.getD p 0) = true := by
  decide +kernel

theorem x2sComp1_fib29 : ∀ p < 513, 464 ≤ p → p < 480 → fiberOK (x2sComp1.getD p 0) = true := by
  decide +kernel

theorem x2sComp1_fib30 : ∀ p < 513, 480 ≤ p → p < 496 → fiberOK (x2sComp1.getD p 0) = true := by
  decide +kernel

theorem x2sComp1_fib31 : ∀ p < 513, 496 ≤ p → p < 512 → fiberOK (x2sComp1.getD p 0) = true := by
  decide +kernel

theorem x2sComp1_fib32 : ∀ p < 513, 512 ≤ p → p < 513 → fiberOK (x2sComp1.getD p 0) = true := by
  decide +kernel

theorem x2sComp1_shape : x2sComp1.length = 513 ∧ ∀ p < 513, fiberOK (x2sComp1.getD p 0) = true := by
  refine ⟨x2sComp1_len, fun p hp => ?_⟩
  by_cases h0 : p < 16
  · exact x2sComp1_fib0 p hp (by omega) h0
  by_cases h1 : p < 32
  · exact x2sComp1_fib1 p hp (by omega) h1
  by_cases h2 : p < 48
  · exact x2sComp1_fib2 p hp (by omega) h2
  by_cases h3 : p < 64
  · exact x2sComp1_fib3 p hp (by omega) h3
  by_cases h4 : p < 80
  · exact x2sComp1_fib4 p hp (by omega) h4
  by_cases h5 : p < 96
  · exact x2sComp1_fib5 p hp (by omega) h5
  by_cases h6 : p < 112
  · exact x2sComp1_fib6 p hp (by omega) h6
  by_cases h7 : p < 128
  · exact x2sComp1_fib7 p hp (by omega) h7
  by_cases h8 : p < 144
  · exact x2sComp1_fib8 p hp (by omega) h8
  by_cases h9 : p < 160
  · exact x2sComp1_fib9 p hp (by omega) h9
  by_cases h10 : p < 176
  · exact x2sComp1_fib10 p hp (by omega) h10
  by_cases h11 : p < 192
  · exact x2sComp1_fib11 p hp (by omega) h11
  by_cases h12 : p < 208
  · exact x2sComp1_fib12 p hp (by omega) h12
  by_cases h13 : p < 224
  · exact x2sComp1_fib13 p hp (by omega) h13
  by_cases h14 : p < 240
  · exact x2sComp1_fib14 p hp (by omega) h14
  by_cases h15 : p < 256
  · exact x2sComp1_fib15 p hp (by omega) h15
  by_cases h16 : p < 272
  · exact x2sComp1_fib16 p hp (by omega) h16
  by_cases h17 : p < 288
  · exact x2sComp1_fib17 p hp (by omega) h17
  by_cases h18 : p < 304
  · exact x2sComp1_fib18 p hp (by omega) h18
  by_cases h19 : p < 320
  · exact x2sComp1_fib19 p hp (by omega) h19
  by_cases h20 : p < 336
  · exact x2sComp1_fib20 p hp (by omega) h20
  by_cases h21 : p < 352
  · exact x2sComp1_fib21 p hp (by omega) h21
  by_cases h22 : p < 368
  · exact x2sComp1_fib22 p hp (by omega) h22
  by_cases h23 : p < 384
  · exact x2sComp1_fib23 p hp (by omega) h23
  by_cases h24 : p < 400
  · exact x2sComp1_fib24 p hp (by omega) h24
  by_cases h25 : p < 416
  · exact x2sComp1_fib25 p hp (by omega) h25
  by_cases h26 : p < 432
  · exact x2sComp1_fib26 p hp (by omega) h26
  by_cases h27 : p < 448
  · exact x2sComp1_fib27 p hp (by omega) h27
  by_cases h28 : p < 464
  · exact x2sComp1_fib28 p hp (by omega) h28
  by_cases h29 : p < 480
  · exact x2sComp1_fib29 p hp (by omega) h29
  by_cases h30 : p < 496
  · exact x2sComp1_fib30 p hp (by omega) h30
  by_cases h31 : p < 512
  · exact x2sComp1_fib31 p hp (by omega) h31
  · exact x2sComp1_fib32 p hp (by omega) hp

end ThreeCopyQutritWerner.X2Sites
