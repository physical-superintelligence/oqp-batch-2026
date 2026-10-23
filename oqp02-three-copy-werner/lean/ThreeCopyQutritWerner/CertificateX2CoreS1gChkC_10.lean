module

public import ThreeCopyQutritWerner.CertificateX2CoreS1gT3
public import ThreeCopyQutritWerner.CertificateX2Trans
public import ThreeCopyQutritWerner.CertificateX2CoreBatchGen
public import ThreeCopyQutritWerner.CertificateX2CoreBatchFlat

@[expose] public section


/-! Batched core S1g: axis-0 stage, selected pairs, flat indices 16000..17599. -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option exponentiation.threshold 1000000

namespace ThreeCopyQutritWerner.X2.CoreS1g
open ThreeCopyQutritWerner ThreeCopyQutritWerner.X2

theorem chkC_10_d16000 : (List.range' 16000 8).all (fun t => (!(pOK tl tl (t % 282) (t / 282)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 282 % 94) * 282) (x2Tab o (t / 282 / 94) (t % 282))) (x2Tab t3 (t / 282) (t % 282)))) = true := by
  decide +kernel

theorem chkC_10_d16008 : (List.range' 16008 8).all (fun t => (!(pOK tl tl (t % 282) (t / 282)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 282 % 94) * 282) (x2Tab o (t / 282 / 94) (t % 282))) (x2Tab t3 (t / 282) (t % 282)))) = true := by
  decide +kernel

theorem chkC_10_d16016 : (List.range' 16016 8).all (fun t => (!(pOK tl tl (t % 282) (t / 282)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 282 % 94) * 282) (x2Tab o (t / 282 / 94) (t % 282))) (x2Tab t3 (t / 282) (t % 282)))) = true := by
  decide +kernel

theorem chkC_10_d16024 : (List.range' 16024 8).all (fun t => (!(pOK tl tl (t % 282) (t / 282)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 282 % 94) * 282) (x2Tab o (t / 282 / 94) (t % 282))) (x2Tab t3 (t / 282) (t % 282)))) = true := by
  decide +kernel

theorem chkC_10_d16032 : (List.range' 16032 8).all (fun t => (!(pOK tl tl (t % 282) (t / 282)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 282 % 94) * 282) (x2Tab o (t / 282 / 94) (t % 282))) (x2Tab t3 (t / 282) (t % 282)))) = true := by
  decide +kernel

theorem chkC_10_d16040 : (List.range' 16040 8).all (fun t => (!(pOK tl tl (t % 282) (t / 282)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 282 % 94) * 282) (x2Tab o (t / 282 / 94) (t % 282))) (x2Tab t3 (t / 282) (t % 282)))) = true := by
  decide +kernel

theorem chkC_10_d16048 : (List.range' 16048 8).all (fun t => (!(pOK tl tl (t % 282) (t / 282)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 282 % 94) * 282) (x2Tab o (t / 282 / 94) (t % 282))) (x2Tab t3 (t / 282) (t % 282)))) = true := by
  decide +kernel

theorem chkC_10_d16056 : (List.range' 16056 8).all (fun t => (!(pOK tl tl (t % 282) (t / 282)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 282 % 94) * 282) (x2Tab o (t / 282 / 94) (t % 282))) (x2Tab t3 (t / 282) (t % 282)))) = true := by
  decide +kernel

theorem chkC_10_d16064 : (List.range' 16064 8).all (fun t => (!(pOK tl tl (t % 282) (t / 282)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 282 % 94) * 282) (x2Tab o (t / 282 / 94) (t % 282))) (x2Tab t3 (t / 282) (t % 282)))) = true := by
  decide +kernel

theorem chkC_10_d16072 : (List.range' 16072 8).all (fun t => (!(pOK tl tl (t % 282) (t / 282)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 282 % 94) * 282) (x2Tab o (t / 282 / 94) (t % 282))) (x2Tab t3 (t / 282) (t % 282)))) = true := by
  decide +kernel

theorem chkC_10_d16080 : (List.range' 16080 8).all (fun t => (!(pOK tl tl (t % 282) (t / 282)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 282 % 94) * 282) (x2Tab o (t / 282 / 94) (t % 282))) (x2Tab t3 (t / 282) (t % 282)))) = true := by
  decide +kernel

theorem chkC_10_d16088 : (List.range' 16088 8).all (fun t => (!(pOK tl tl (t % 282) (t / 282)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 282 % 94) * 282) (x2Tab o (t / 282 / 94) (t % 282))) (x2Tab t3 (t / 282) (t % 282)))) = true := by
  decide +kernel

theorem chkC_10_d16096 : (List.range' 16096 8).all (fun t => (!(pOK tl tl (t % 282) (t / 282)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 282 % 94) * 282) (x2Tab o (t / 282 / 94) (t % 282))) (x2Tab t3 (t / 282) (t % 282)))) = true := by
  decide +kernel

theorem chkC_10_d16104 : (List.range' 16104 8).all (fun t => (!(pOK tl tl (t % 282) (t / 282)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 282 % 94) * 282) (x2Tab o (t / 282 / 94) (t % 282))) (x2Tab t3 (t / 282) (t % 282)))) = true := by
  decide +kernel

theorem chkC_10_d16112 : (List.range' 16112 8).all (fun t => (!(pOK tl tl (t % 282) (t / 282)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 282 % 94) * 282) (x2Tab o (t / 282 / 94) (t % 282))) (x2Tab t3 (t / 282) (t % 282)))) = true := by
  decide +kernel

theorem chkC_10_d16120 : (List.range' 16120 8).all (fun t => (!(pOK tl tl (t % 282) (t / 282)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 282 % 94) * 282) (x2Tab o (t / 282 / 94) (t % 282))) (x2Tab t3 (t / 282) (t % 282)))) = true := by
  decide +kernel

theorem chkC_10_d16128 : (List.range' 16128 8).all (fun t => (!(pOK tl tl (t % 282) (t / 282)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 282 % 94) * 282) (x2Tab o (t / 282 / 94) (t % 282))) (x2Tab t3 (t / 282) (t % 282)))) = true := by
  decide +kernel

theorem chkC_10_d16136 : (List.range' 16136 8).all (fun t => (!(pOK tl tl (t % 282) (t / 282)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 282 % 94) * 282) (x2Tab o (t / 282 / 94) (t % 282))) (x2Tab t3 (t / 282) (t % 282)))) = true := by
  decide +kernel

theorem chkC_10_d16144 : (List.range' 16144 8).all (fun t => (!(pOK tl tl (t % 282) (t / 282)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 282 % 94) * 282) (x2Tab o (t / 282 / 94) (t % 282))) (x2Tab t3 (t / 282) (t % 282)))) = true := by
  decide +kernel

theorem chkC_10_d16152 : (List.range' 16152 8).all (fun t => (!(pOK tl tl (t % 282) (t / 282)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 282 % 94) * 282) (x2Tab o (t / 282 / 94) (t % 282))) (x2Tab t3 (t / 282) (t % 282)))) = true := by
  decide +kernel

theorem chkC_10_d16160 : (List.range' 16160 8).all (fun t => (!(pOK tl tl (t % 282) (t / 282)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 282 % 94) * 282) (x2Tab o (t / 282 / 94) (t % 282))) (x2Tab t3 (t / 282) (t % 282)))) = true := by
  decide +kernel

theorem chkC_10_d16168 : (List.range' 16168 8).all (fun t => (!(pOK tl tl (t % 282) (t / 282)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 282 % 94) * 282) (x2Tab o (t / 282 / 94) (t % 282))) (x2Tab t3 (t / 282) (t % 282)))) = true := by
  decide +kernel

theorem chkC_10_d16176 : (List.range' 16176 8).all (fun t => (!(pOK tl tl (t % 282) (t / 282)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 282 % 94) * 282) (x2Tab o (t / 282 / 94) (t % 282))) (x2Tab t3 (t / 282) (t % 282)))) = true := by
  decide +kernel

theorem chkC_10_d16184 : (List.range' 16184 8).all (fun t => (!(pOK tl tl (t % 282) (t / 282)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 282 % 94) * 282) (x2Tab o (t / 282 / 94) (t % 282))) (x2Tab t3 (t / 282) (t % 282)))) = true := by
  decide +kernel

theorem chkC_10_d16192 : (List.range' 16192 8).all (fun t => (!(pOK tl tl (t % 282) (t / 282)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 282 % 94) * 282) (x2Tab o (t / 282 / 94) (t % 282))) (x2Tab t3 (t / 282) (t % 282)))) = true := by
  decide +kernel

theorem chkC_10_d16200 : (List.range' 16200 8).all (fun t => (!(pOK tl tl (t % 282) (t / 282)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 282 % 94) * 282) (x2Tab o (t / 282 / 94) (t % 282))) (x2Tab t3 (t / 282) (t % 282)))) = true := by
  decide +kernel

theorem chkC_10_d16208 : (List.range' 16208 8).all (fun t => (!(pOK tl tl (t % 282) (t / 282)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 282 % 94) * 282) (x2Tab o (t / 282 / 94) (t % 282))) (x2Tab t3 (t / 282) (t % 282)))) = true := by
  decide +kernel

theorem chkC_10_d16216 : (List.range' 16216 8).all (fun t => (!(pOK tl tl (t % 282) (t / 282)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 282 % 94) * 282) (x2Tab o (t / 282 / 94) (t % 282))) (x2Tab t3 (t / 282) (t % 282)))) = true := by
  decide +kernel

theorem chkC_10_d16224 : (List.range' 16224 8).all (fun t => (!(pOK tl tl (t % 282) (t / 282)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 282 % 94) * 282) (x2Tab o (t / 282 / 94) (t % 282))) (x2Tab t3 (t / 282) (t % 282)))) = true := by
  decide +kernel

theorem chkC_10_d16232 : (List.range' 16232 8).all (fun t => (!(pOK tl tl (t % 282) (t / 282)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 282 % 94) * 282) (x2Tab o (t / 282 / 94) (t % 282))) (x2Tab t3 (t / 282) (t % 282)))) = true := by
  decide +kernel

theorem chkC_10_d16240 : (List.range' 16240 8).all (fun t => (!(pOK tl tl (t % 282) (t / 282)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 282 % 94) * 282) (x2Tab o (t / 282 / 94) (t % 282))) (x2Tab t3 (t / 282) (t % 282)))) = true := by
  decide +kernel

theorem chkC_10_d16248 : (List.range' 16248 8).all (fun t => (!(pOK tl tl (t % 282) (t / 282)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 282 % 94) * 282) (x2Tab o (t / 282 / 94) (t % 282))) (x2Tab t3 (t / 282) (t % 282)))) = true := by
  decide +kernel

theorem chkC_10_d16256 : (List.range' 16256 8).all (fun t => (!(pOK tl tl (t % 282) (t / 282)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 282 % 94) * 282) (x2Tab o (t / 282 / 94) (t % 282))) (x2Tab t3 (t / 282) (t % 282)))) = true := by
  decide +kernel

theorem chkC_10_d16264 : (List.range' 16264 8).all (fun t => (!(pOK tl tl (t % 282) (t / 282)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 282 % 94) * 282) (x2Tab o (t / 282 / 94) (t % 282))) (x2Tab t3 (t / 282) (t % 282)))) = true := by
  decide +kernel

theorem chkC_10_d16272 : (List.range' 16272 8).all (fun t => (!(pOK tl tl (t % 282) (t / 282)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 282 % 94) * 282) (x2Tab o (t / 282 / 94) (t % 282))) (x2Tab t3 (t / 282) (t % 282)))) = true := by
  decide +kernel

theorem chkC_10_d16280 : (List.range' 16280 8).all (fun t => (!(pOK tl tl (t % 282) (t / 282)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 282 % 94) * 282) (x2Tab o (t / 282 / 94) (t % 282))) (x2Tab t3 (t / 282) (t % 282)))) = true := by
  decide +kernel

theorem chkC_10_d16288 : (List.range' 16288 8).all (fun t => (!(pOK tl tl (t % 282) (t / 282)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 282 % 94) * 282) (x2Tab o (t / 282 / 94) (t % 282))) (x2Tab t3 (t / 282) (t % 282)))) = true := by
  decide +kernel

theorem chkC_10_d16296 : (List.range' 16296 8).all (fun t => (!(pOK tl tl (t % 282) (t / 282)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 282 % 94) * 282) (x2Tab o (t / 282 / 94) (t % 282))) (x2Tab t3 (t / 282) (t % 282)))) = true := by
  decide +kernel

theorem chkC_10_d16304 : (List.range' 16304 8).all (fun t => (!(pOK tl tl (t % 282) (t / 282)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 282 % 94) * 282) (x2Tab o (t / 282 / 94) (t % 282))) (x2Tab t3 (t / 282) (t % 282)))) = true := by
  decide +kernel

theorem chkC_10_d16312 : (List.range' 16312 8).all (fun t => (!(pOK tl tl (t % 282) (t / 282)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 282 % 94) * 282) (x2Tab o (t / 282 / 94) (t % 282))) (x2Tab t3 (t / 282) (t % 282)))) = true := by
  decide +kernel

theorem chkC_10_d16320 : (List.range' 16320 8).all (fun t => (!(pOK tl tl (t % 282) (t / 282)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 282 % 94) * 282) (x2Tab o (t / 282 / 94) (t % 282))) (x2Tab t3 (t / 282) (t % 282)))) = true := by
  decide +kernel

theorem chkC_10_d16328 : (List.range' 16328 8).all (fun t => (!(pOK tl tl (t % 282) (t / 282)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 282 % 94) * 282) (x2Tab o (t / 282 / 94) (t % 282))) (x2Tab t3 (t / 282) (t % 282)))) = true := by
  decide +kernel

theorem chkC_10_d16336 : (List.range' 16336 8).all (fun t => (!(pOK tl tl (t % 282) (t / 282)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 282 % 94) * 282) (x2Tab o (t / 282 / 94) (t % 282))) (x2Tab t3 (t / 282) (t % 282)))) = true := by
  decide +kernel

theorem chkC_10_d16344 : (List.range' 16344 8).all (fun t => (!(pOK tl tl (t % 282) (t / 282)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 282 % 94) * 282) (x2Tab o (t / 282 / 94) (t % 282))) (x2Tab t3 (t / 282) (t % 282)))) = true := by
  decide +kernel

theorem chkC_10_d16352 : (List.range' 16352 8).all (fun t => (!(pOK tl tl (t % 282) (t / 282)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 282 % 94) * 282) (x2Tab o (t / 282 / 94) (t % 282))) (x2Tab t3 (t / 282) (t % 282)))) = true := by
  decide +kernel

theorem chkC_10_d16360 : (List.range' 16360 8).all (fun t => (!(pOK tl tl (t % 282) (t / 282)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 282 % 94) * 282) (x2Tab o (t / 282 / 94) (t % 282))) (x2Tab t3 (t / 282) (t % 282)))) = true := by
  decide +kernel

theorem chkC_10_d16368 : (List.range' 16368 8).all (fun t => (!(pOK tl tl (t % 282) (t / 282)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 282 % 94) * 282) (x2Tab o (t / 282 / 94) (t % 282))) (x2Tab t3 (t / 282) (t % 282)))) = true := by
  decide +kernel

theorem chkC_10_d16376 : (List.range' 16376 8).all (fun t => (!(pOK tl tl (t % 282) (t / 282)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 282 % 94) * 282) (x2Tab o (t / 282 / 94) (t % 282))) (x2Tab t3 (t / 282) (t % 282)))) = true := by
  decide +kernel

theorem chkC_10_d16384 : (List.range' 16384 8).all (fun t => (!(pOK tl tl (t % 282) (t / 282)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 282 % 94) * 282) (x2Tab o (t / 282 / 94) (t % 282))) (x2Tab t3 (t / 282) (t % 282)))) = true := by
  decide +kernel

theorem chkC_10_d16392 : (List.range' 16392 8).all (fun t => (!(pOK tl tl (t % 282) (t / 282)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 282 % 94) * 282) (x2Tab o (t / 282 / 94) (t % 282))) (x2Tab t3 (t / 282) (t % 282)))) = true := by
  decide +kernel

theorem chkC_10_d16400 : (List.range' 16400 8).all (fun t => (!(pOK tl tl (t % 282) (t / 282)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 282 % 94) * 282) (x2Tab o (t / 282 / 94) (t % 282))) (x2Tab t3 (t / 282) (t % 282)))) = true := by
  decide +kernel

theorem chkC_10_d16408 : (List.range' 16408 8).all (fun t => (!(pOK tl tl (t % 282) (t / 282)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 282 % 94) * 282) (x2Tab o (t / 282 / 94) (t % 282))) (x2Tab t3 (t / 282) (t % 282)))) = true := by
  decide +kernel

theorem chkC_10_d16416 : (List.range' 16416 8).all (fun t => (!(pOK tl tl (t % 282) (t / 282)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 282 % 94) * 282) (x2Tab o (t / 282 / 94) (t % 282))) (x2Tab t3 (t / 282) (t % 282)))) = true := by
  decide +kernel

theorem chkC_10_d16424 : (List.range' 16424 8).all (fun t => (!(pOK tl tl (t % 282) (t / 282)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 282 % 94) * 282) (x2Tab o (t / 282 / 94) (t % 282))) (x2Tab t3 (t / 282) (t % 282)))) = true := by
  decide +kernel

theorem chkC_10_d16432 : (List.range' 16432 8).all (fun t => (!(pOK tl tl (t % 282) (t / 282)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 282 % 94) * 282) (x2Tab o (t / 282 / 94) (t % 282))) (x2Tab t3 (t / 282) (t % 282)))) = true := by
  decide +kernel

theorem chkC_10_d16440 : (List.range' 16440 8).all (fun t => (!(pOK tl tl (t % 282) (t / 282)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 282 % 94) * 282) (x2Tab o (t / 282 / 94) (t % 282))) (x2Tab t3 (t / 282) (t % 282)))) = true := by
  decide +kernel

theorem chkC_10_d16448 : (List.range' 16448 8).all (fun t => (!(pOK tl tl (t % 282) (t / 282)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 282 % 94) * 282) (x2Tab o (t / 282 / 94) (t % 282))) (x2Tab t3 (t / 282) (t % 282)))) = true := by
  decide +kernel

theorem chkC_10_d16456 : (List.range' 16456 8).all (fun t => (!(pOK tl tl (t % 282) (t / 282)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 282 % 94) * 282) (x2Tab o (t / 282 / 94) (t % 282))) (x2Tab t3 (t / 282) (t % 282)))) = true := by
  decide +kernel

theorem chkC_10_d16464 : (List.range' 16464 8).all (fun t => (!(pOK tl tl (t % 282) (t / 282)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 282 % 94) * 282) (x2Tab o (t / 282 / 94) (t % 282))) (x2Tab t3 (t / 282) (t % 282)))) = true := by
  decide +kernel

theorem chkC_10_d16472 : (List.range' 16472 8).all (fun t => (!(pOK tl tl (t % 282) (t / 282)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 282 % 94) * 282) (x2Tab o (t / 282 / 94) (t % 282))) (x2Tab t3 (t / 282) (t % 282)))) = true := by
  decide +kernel

theorem chkC_10_d16480 : (List.range' 16480 8).all (fun t => (!(pOK tl tl (t % 282) (t / 282)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 282 % 94) * 282) (x2Tab o (t / 282 / 94) (t % 282))) (x2Tab t3 (t / 282) (t % 282)))) = true := by
  decide +kernel

theorem chkC_10_d16488 : (List.range' 16488 8).all (fun t => (!(pOK tl tl (t % 282) (t / 282)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 282 % 94) * 282) (x2Tab o (t / 282 / 94) (t % 282))) (x2Tab t3 (t / 282) (t % 282)))) = true := by
  decide +kernel

theorem chkC_10_d16496 : (List.range' 16496 8).all (fun t => (!(pOK tl tl (t % 282) (t / 282)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 282 % 94) * 282) (x2Tab o (t / 282 / 94) (t % 282))) (x2Tab t3 (t / 282) (t % 282)))) = true := by
  decide +kernel

theorem chkC_10_d16504 : (List.range' 16504 8).all (fun t => (!(pOK tl tl (t % 282) (t / 282)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 282 % 94) * 282) (x2Tab o (t / 282 / 94) (t % 282))) (x2Tab t3 (t / 282) (t % 282)))) = true := by
  decide +kernel

theorem chkC_10_d16512 : (List.range' 16512 8).all (fun t => (!(pOK tl tl (t % 282) (t / 282)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 282 % 94) * 282) (x2Tab o (t / 282 / 94) (t % 282))) (x2Tab t3 (t / 282) (t % 282)))) = true := by
  decide +kernel

theorem chkC_10_d16520 : (List.range' 16520 8).all (fun t => (!(pOK tl tl (t % 282) (t / 282)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 282 % 94) * 282) (x2Tab o (t / 282 / 94) (t % 282))) (x2Tab t3 (t / 282) (t % 282)))) = true := by
  decide +kernel

theorem chkC_10_d16528 : (List.range' 16528 8).all (fun t => (!(pOK tl tl (t % 282) (t / 282)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 282 % 94) * 282) (x2Tab o (t / 282 / 94) (t % 282))) (x2Tab t3 (t / 282) (t % 282)))) = true := by
  decide +kernel

theorem chkC_10_d16536 : (List.range' 16536 8).all (fun t => (!(pOK tl tl (t % 282) (t / 282)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 282 % 94) * 282) (x2Tab o (t / 282 / 94) (t % 282))) (x2Tab t3 (t / 282) (t % 282)))) = true := by
  decide +kernel

theorem chkC_10_d16544 : (List.range' 16544 8).all (fun t => (!(pOK tl tl (t % 282) (t / 282)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 282 % 94) * 282) (x2Tab o (t / 282 / 94) (t % 282))) (x2Tab t3 (t / 282) (t % 282)))) = true := by
  decide +kernel

theorem chkC_10_d16552 : (List.range' 16552 8).all (fun t => (!(pOK tl tl (t % 282) (t / 282)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 282 % 94) * 282) (x2Tab o (t / 282 / 94) (t % 282))) (x2Tab t3 (t / 282) (t % 282)))) = true := by
  decide +kernel

theorem chkC_10_d16560 : (List.range' 16560 8).all (fun t => (!(pOK tl tl (t % 282) (t / 282)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 282 % 94) * 282) (x2Tab o (t / 282 / 94) (t % 282))) (x2Tab t3 (t / 282) (t % 282)))) = true := by
  decide +kernel

theorem chkC_10_d16568 : (List.range' 16568 8).all (fun t => (!(pOK tl tl (t % 282) (t / 282)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 282 % 94) * 282) (x2Tab o (t / 282 / 94) (t % 282))) (x2Tab t3 (t / 282) (t % 282)))) = true := by
  decide +kernel

theorem chkC_10_d16576 : (List.range' 16576 8).all (fun t => (!(pOK tl tl (t % 282) (t / 282)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 282 % 94) * 282) (x2Tab o (t / 282 / 94) (t % 282))) (x2Tab t3 (t / 282) (t % 282)))) = true := by
  decide +kernel

theorem chkC_10_d16584 : (List.range' 16584 8).all (fun t => (!(pOK tl tl (t % 282) (t / 282)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 282 % 94) * 282) (x2Tab o (t / 282 / 94) (t % 282))) (x2Tab t3 (t / 282) (t % 282)))) = true := by
  decide +kernel

theorem chkC_10_d16592 : (List.range' 16592 8).all (fun t => (!(pOK tl tl (t % 282) (t / 282)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 282 % 94) * 282) (x2Tab o (t / 282 / 94) (t % 282))) (x2Tab t3 (t / 282) (t % 282)))) = true := by
  decide +kernel

theorem chkC_10_d16600 : (List.range' 16600 8).all (fun t => (!(pOK tl tl (t % 282) (t / 282)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 282 % 94) * 282) (x2Tab o (t / 282 / 94) (t % 282))) (x2Tab t3 (t / 282) (t % 282)))) = true := by
  decide +kernel

theorem chkC_10_d16608 : (List.range' 16608 8).all (fun t => (!(pOK tl tl (t % 282) (t / 282)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 282 % 94) * 282) (x2Tab o (t / 282 / 94) (t % 282))) (x2Tab t3 (t / 282) (t % 282)))) = true := by
  decide +kernel

theorem chkC_10_d16616 : (List.range' 16616 8).all (fun t => (!(pOK tl tl (t % 282) (t / 282)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 282 % 94) * 282) (x2Tab o (t / 282 / 94) (t % 282))) (x2Tab t3 (t / 282) (t % 282)))) = true := by
  decide +kernel

theorem chkC_10_d16624 : (List.range' 16624 8).all (fun t => (!(pOK tl tl (t % 282) (t / 282)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 282 % 94) * 282) (x2Tab o (t / 282 / 94) (t % 282))) (x2Tab t3 (t / 282) (t % 282)))) = true := by
  decide +kernel

theorem chkC_10_d16632 : (List.range' 16632 8).all (fun t => (!(pOK tl tl (t % 282) (t / 282)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 282 % 94) * 282) (x2Tab o (t / 282 / 94) (t % 282))) (x2Tab t3 (t / 282) (t % 282)))) = true := by
  decide +kernel

theorem chkC_10_d16640 : (List.range' 16640 8).all (fun t => (!(pOK tl tl (t % 282) (t / 282)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 282 % 94) * 282) (x2Tab o (t / 282 / 94) (t % 282))) (x2Tab t3 (t / 282) (t % 282)))) = true := by
  decide +kernel

theorem chkC_10_d16648 : (List.range' 16648 8).all (fun t => (!(pOK tl tl (t % 282) (t / 282)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 282 % 94) * 282) (x2Tab o (t / 282 / 94) (t % 282))) (x2Tab t3 (t / 282) (t % 282)))) = true := by
  decide +kernel

theorem chkC_10_d16656 : (List.range' 16656 8).all (fun t => (!(pOK tl tl (t % 282) (t / 282)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 282 % 94) * 282) (x2Tab o (t / 282 / 94) (t % 282))) (x2Tab t3 (t / 282) (t % 282)))) = true := by
  decide +kernel

theorem chkC_10_d16664 : (List.range' 16664 8).all (fun t => (!(pOK tl tl (t % 282) (t / 282)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 282 % 94) * 282) (x2Tab o (t / 282 / 94) (t % 282))) (x2Tab t3 (t / 282) (t % 282)))) = true := by
  decide +kernel

theorem chkC_10_d16672 : (List.range' 16672 8).all (fun t => (!(pOK tl tl (t % 282) (t / 282)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 282 % 94) * 282) (x2Tab o (t / 282 / 94) (t % 282))) (x2Tab t3 (t / 282) (t % 282)))) = true := by
  decide +kernel

theorem chkC_10_d16680 : (List.range' 16680 8).all (fun t => (!(pOK tl tl (t % 282) (t / 282)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 282 % 94) * 282) (x2Tab o (t / 282 / 94) (t % 282))) (x2Tab t3 (t / 282) (t % 282)))) = true := by
  decide +kernel

theorem chkC_10_d16688 : (List.range' 16688 8).all (fun t => (!(pOK tl tl (t % 282) (t / 282)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 282 % 94) * 282) (x2Tab o (t / 282 / 94) (t % 282))) (x2Tab t3 (t / 282) (t % 282)))) = true := by
  decide +kernel

theorem chkC_10_d16696 : (List.range' 16696 8).all (fun t => (!(pOK tl tl (t % 282) (t / 282)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 282 % 94) * 282) (x2Tab o (t / 282 / 94) (t % 282))) (x2Tab t3 (t / 282) (t % 282)))) = true := by
  decide +kernel

theorem chkC_10_d16704 : (List.range' 16704 8).all (fun t => (!(pOK tl tl (t % 282) (t / 282)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 282 % 94) * 282) (x2Tab o (t / 282 / 94) (t % 282))) (x2Tab t3 (t / 282) (t % 282)))) = true := by
  decide +kernel

theorem chkC_10_d16712 : (List.range' 16712 8).all (fun t => (!(pOK tl tl (t % 282) (t / 282)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 282 % 94) * 282) (x2Tab o (t / 282 / 94) (t % 282))) (x2Tab t3 (t / 282) (t % 282)))) = true := by
  decide +kernel

theorem chkC_10_d16720 : (List.range' 16720 8).all (fun t => (!(pOK tl tl (t % 282) (t / 282)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 282 % 94) * 282) (x2Tab o (t / 282 / 94) (t % 282))) (x2Tab t3 (t / 282) (t % 282)))) = true := by
  decide +kernel

theorem chkC_10_d16728 : (List.range' 16728 8).all (fun t => (!(pOK tl tl (t % 282) (t / 282)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 282 % 94) * 282) (x2Tab o (t / 282 / 94) (t % 282))) (x2Tab t3 (t / 282) (t % 282)))) = true := by
  decide +kernel

theorem chkC_10_d16736 : (List.range' 16736 8).all (fun t => (!(pOK tl tl (t % 282) (t / 282)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 282 % 94) * 282) (x2Tab o (t / 282 / 94) (t % 282))) (x2Tab t3 (t / 282) (t % 282)))) = true := by
  decide +kernel

theorem chkC_10_d16744 : (List.range' 16744 8).all (fun t => (!(pOK tl tl (t % 282) (t / 282)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 282 % 94) * 282) (x2Tab o (t / 282 / 94) (t % 282))) (x2Tab t3 (t / 282) (t % 282)))) = true := by
  decide +kernel

theorem chkC_10_d16752 : (List.range' 16752 8).all (fun t => (!(pOK tl tl (t % 282) (t / 282)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 282 % 94) * 282) (x2Tab o (t / 282 / 94) (t % 282))) (x2Tab t3 (t / 282) (t % 282)))) = true := by
  decide +kernel

theorem chkC_10_d16760 : (List.range' 16760 8).all (fun t => (!(pOK tl tl (t % 282) (t / 282)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 282 % 94) * 282) (x2Tab o (t / 282 / 94) (t % 282))) (x2Tab t3 (t / 282) (t % 282)))) = true := by
  decide +kernel

theorem chkC_10_d16768 : (List.range' 16768 8).all (fun t => (!(pOK tl tl (t % 282) (t / 282)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 282 % 94) * 282) (x2Tab o (t / 282 / 94) (t % 282))) (x2Tab t3 (t / 282) (t % 282)))) = true := by
  decide +kernel

theorem chkC_10_d16776 : (List.range' 16776 8).all (fun t => (!(pOK tl tl (t % 282) (t / 282)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 282 % 94) * 282) (x2Tab o (t / 282 / 94) (t % 282))) (x2Tab t3 (t / 282) (t % 282)))) = true := by
  decide +kernel

theorem chkC_10_d16784 : (List.range' 16784 8).all (fun t => (!(pOK tl tl (t % 282) (t / 282)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 282 % 94) * 282) (x2Tab o (t / 282 / 94) (t % 282))) (x2Tab t3 (t / 282) (t % 282)))) = true := by
  decide +kernel

theorem chkC_10_d16792 : (List.range' 16792 8).all (fun t => (!(pOK tl tl (t % 282) (t / 282)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 282 % 94) * 282) (x2Tab o (t / 282 / 94) (t % 282))) (x2Tab t3 (t / 282) (t % 282)))) = true := by
  decide +kernel

theorem chkC_10_d16800 : (List.range' 16800 8).all (fun t => (!(pOK tl tl (t % 282) (t / 282)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 282 % 94) * 282) (x2Tab o (t / 282 / 94) (t % 282))) (x2Tab t3 (t / 282) (t % 282)))) = true := by
  decide +kernel

theorem chkC_10_d16808 : (List.range' 16808 8).all (fun t => (!(pOK tl tl (t % 282) (t / 282)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 282 % 94) * 282) (x2Tab o (t / 282 / 94) (t % 282))) (x2Tab t3 (t / 282) (t % 282)))) = true := by
  decide +kernel

theorem chkC_10_d16816 : (List.range' 16816 8).all (fun t => (!(pOK tl tl (t % 282) (t / 282)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 282 % 94) * 282) (x2Tab o (t / 282 / 94) (t % 282))) (x2Tab t3 (t / 282) (t % 282)))) = true := by
  decide +kernel

theorem chkC_10_d16824 : (List.range' 16824 8).all (fun t => (!(pOK tl tl (t % 282) (t / 282)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 282 % 94) * 282) (x2Tab o (t / 282 / 94) (t % 282))) (x2Tab t3 (t / 282) (t % 282)))) = true := by
  decide +kernel

theorem chkC_10_d16832 : (List.range' 16832 8).all (fun t => (!(pOK tl tl (t % 282) (t / 282)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 282 % 94) * 282) (x2Tab o (t / 282 / 94) (t % 282))) (x2Tab t3 (t / 282) (t % 282)))) = true := by
  decide +kernel

theorem chkC_10_d16840 : (List.range' 16840 8).all (fun t => (!(pOK tl tl (t % 282) (t / 282)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 282 % 94) * 282) (x2Tab o (t / 282 / 94) (t % 282))) (x2Tab t3 (t / 282) (t % 282)))) = true := by
  decide +kernel

theorem chkC_10_d16848 : (List.range' 16848 8).all (fun t => (!(pOK tl tl (t % 282) (t / 282)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 282 % 94) * 282) (x2Tab o (t / 282 / 94) (t % 282))) (x2Tab t3 (t / 282) (t % 282)))) = true := by
  decide +kernel

theorem chkC_10_d16856 : (List.range' 16856 8).all (fun t => (!(pOK tl tl (t % 282) (t / 282)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 282 % 94) * 282) (x2Tab o (t / 282 / 94) (t % 282))) (x2Tab t3 (t / 282) (t % 282)))) = true := by
  decide +kernel

theorem chkC_10_d16864 : (List.range' 16864 8).all (fun t => (!(pOK tl tl (t % 282) (t / 282)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 282 % 94) * 282) (x2Tab o (t / 282 / 94) (t % 282))) (x2Tab t3 (t / 282) (t % 282)))) = true := by
  decide +kernel

theorem chkC_10_d16872 : (List.range' 16872 8).all (fun t => (!(pOK tl tl (t % 282) (t / 282)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 282 % 94) * 282) (x2Tab o (t / 282 / 94) (t % 282))) (x2Tab t3 (t / 282) (t % 282)))) = true := by
  decide +kernel

theorem chkC_10_d16880 : (List.range' 16880 8).all (fun t => (!(pOK tl tl (t % 282) (t / 282)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 282 % 94) * 282) (x2Tab o (t / 282 / 94) (t % 282))) (x2Tab t3 (t / 282) (t % 282)))) = true := by
  decide +kernel

theorem chkC_10_d16888 : (List.range' 16888 8).all (fun t => (!(pOK tl tl (t % 282) (t / 282)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 282 % 94) * 282) (x2Tab o (t / 282 / 94) (t % 282))) (x2Tab t3 (t / 282) (t % 282)))) = true := by
  decide +kernel

theorem chkC_10_d16896 : (List.range' 16896 8).all (fun t => (!(pOK tl tl (t % 282) (t / 282)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 282 % 94) * 282) (x2Tab o (t / 282 / 94) (t % 282))) (x2Tab t3 (t / 282) (t % 282)))) = true := by
  decide +kernel

theorem chkC_10_d16904 : (List.range' 16904 8).all (fun t => (!(pOK tl tl (t % 282) (t / 282)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 282 % 94) * 282) (x2Tab o (t / 282 / 94) (t % 282))) (x2Tab t3 (t / 282) (t % 282)))) = true := by
  decide +kernel

theorem chkC_10_d16912 : (List.range' 16912 8).all (fun t => (!(pOK tl tl (t % 282) (t / 282)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 282 % 94) * 282) (x2Tab o (t / 282 / 94) (t % 282))) (x2Tab t3 (t / 282) (t % 282)))) = true := by
  decide +kernel

theorem chkC_10_d16920 : (List.range' 16920 8).all (fun t => (!(pOK tl tl (t % 282) (t / 282)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 282 % 94) * 282) (x2Tab o (t / 282 / 94) (t % 282))) (x2Tab t3 (t / 282) (t % 282)))) = true := by
  decide +kernel

theorem chkC_10_d16928 : (List.range' 16928 8).all (fun t => (!(pOK tl tl (t % 282) (t / 282)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 282 % 94) * 282) (x2Tab o (t / 282 / 94) (t % 282))) (x2Tab t3 (t / 282) (t % 282)))) = true := by
  decide +kernel

theorem chkC_10_d16936 : (List.range' 16936 8).all (fun t => (!(pOK tl tl (t % 282) (t / 282)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 282 % 94) * 282) (x2Tab o (t / 282 / 94) (t % 282))) (x2Tab t3 (t / 282) (t % 282)))) = true := by
  decide +kernel

theorem chkC_10_d16944 : (List.range' 16944 8).all (fun t => (!(pOK tl tl (t % 282) (t / 282)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 282 % 94) * 282) (x2Tab o (t / 282 / 94) (t % 282))) (x2Tab t3 (t / 282) (t % 282)))) = true := by
  decide +kernel

theorem chkC_10_d16952 : (List.range' 16952 8).all (fun t => (!(pOK tl tl (t % 282) (t / 282)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 282 % 94) * 282) (x2Tab o (t / 282 / 94) (t % 282))) (x2Tab t3 (t / 282) (t % 282)))) = true := by
  decide +kernel

theorem chkC_10_d16960 : (List.range' 16960 8).all (fun t => (!(pOK tl tl (t % 282) (t / 282)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 282 % 94) * 282) (x2Tab o (t / 282 / 94) (t % 282))) (x2Tab t3 (t / 282) (t % 282)))) = true := by
  decide +kernel

theorem chkC_10_d16968 : (List.range' 16968 8).all (fun t => (!(pOK tl tl (t % 282) (t / 282)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 282 % 94) * 282) (x2Tab o (t / 282 / 94) (t % 282))) (x2Tab t3 (t / 282) (t % 282)))) = true := by
  decide +kernel

theorem chkC_10_d16976 : (List.range' 16976 8).all (fun t => (!(pOK tl tl (t % 282) (t / 282)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 282 % 94) * 282) (x2Tab o (t / 282 / 94) (t % 282))) (x2Tab t3 (t / 282) (t % 282)))) = true := by
  decide +kernel

theorem chkC_10_d16984 : (List.range' 16984 8).all (fun t => (!(pOK tl tl (t % 282) (t / 282)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 282 % 94) * 282) (x2Tab o (t / 282 / 94) (t % 282))) (x2Tab t3 (t / 282) (t % 282)))) = true := by
  decide +kernel

theorem chkC_10_d16992 : (List.range' 16992 8).all (fun t => (!(pOK tl tl (t % 282) (t / 282)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 282 % 94) * 282) (x2Tab o (t / 282 / 94) (t % 282))) (x2Tab t3 (t / 282) (t % 282)))) = true := by
  decide +kernel

theorem chkC_10_d17000 : (List.range' 17000 8).all (fun t => (!(pOK tl tl (t % 282) (t / 282)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 282 % 94) * 282) (x2Tab o (t / 282 / 94) (t % 282))) (x2Tab t3 (t / 282) (t % 282)))) = true := by
  decide +kernel

theorem chkC_10_d17008 : (List.range' 17008 8).all (fun t => (!(pOK tl tl (t % 282) (t / 282)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 282 % 94) * 282) (x2Tab o (t / 282 / 94) (t % 282))) (x2Tab t3 (t / 282) (t % 282)))) = true := by
  decide +kernel

theorem chkC_10_d17016 : (List.range' 17016 8).all (fun t => (!(pOK tl tl (t % 282) (t / 282)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 282 % 94) * 282) (x2Tab o (t / 282 / 94) (t % 282))) (x2Tab t3 (t / 282) (t % 282)))) = true := by
  decide +kernel

theorem chkC_10_d17024 : (List.range' 17024 8).all (fun t => (!(pOK tl tl (t % 282) (t / 282)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 282 % 94) * 282) (x2Tab o (t / 282 / 94) (t % 282))) (x2Tab t3 (t / 282) (t % 282)))) = true := by
  decide +kernel

theorem chkC_10_d17032 : (List.range' 17032 8).all (fun t => (!(pOK tl tl (t % 282) (t / 282)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 282 % 94) * 282) (x2Tab o (t / 282 / 94) (t % 282))) (x2Tab t3 (t / 282) (t % 282)))) = true := by
  decide +kernel

theorem chkC_10_d17040 : (List.range' 17040 8).all (fun t => (!(pOK tl tl (t % 282) (t / 282)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 282 % 94) * 282) (x2Tab o (t / 282 / 94) (t % 282))) (x2Tab t3 (t / 282) (t % 282)))) = true := by
  decide +kernel

theorem chkC_10_d17048 : (List.range' 17048 8).all (fun t => (!(pOK tl tl (t % 282) (t / 282)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 282 % 94) * 282) (x2Tab o (t / 282 / 94) (t % 282))) (x2Tab t3 (t / 282) (t % 282)))) = true := by
  decide +kernel

theorem chkC_10_d17056 : (List.range' 17056 8).all (fun t => (!(pOK tl tl (t % 282) (t / 282)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 282 % 94) * 282) (x2Tab o (t / 282 / 94) (t % 282))) (x2Tab t3 (t / 282) (t % 282)))) = true := by
  decide +kernel

theorem chkC_10_d17064 : (List.range' 17064 8).all (fun t => (!(pOK tl tl (t % 282) (t / 282)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 282 % 94) * 282) (x2Tab o (t / 282 / 94) (t % 282))) (x2Tab t3 (t / 282) (t % 282)))) = true := by
  decide +kernel

theorem chkC_10_d17072 : (List.range' 17072 8).all (fun t => (!(pOK tl tl (t % 282) (t / 282)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 282 % 94) * 282) (x2Tab o (t / 282 / 94) (t % 282))) (x2Tab t3 (t / 282) (t % 282)))) = true := by
  decide +kernel

theorem chkC_10_d17080 : (List.range' 17080 8).all (fun t => (!(pOK tl tl (t % 282) (t / 282)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 282 % 94) * 282) (x2Tab o (t / 282 / 94) (t % 282))) (x2Tab t3 (t / 282) (t % 282)))) = true := by
  decide +kernel

theorem chkC_10_d17088 : (List.range' 17088 8).all (fun t => (!(pOK tl tl (t % 282) (t / 282)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 282 % 94) * 282) (x2Tab o (t / 282 / 94) (t % 282))) (x2Tab t3 (t / 282) (t % 282)))) = true := by
  decide +kernel

theorem chkC_10_d17096 : (List.range' 17096 8).all (fun t => (!(pOK tl tl (t % 282) (t / 282)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 282 % 94) * 282) (x2Tab o (t / 282 / 94) (t % 282))) (x2Tab t3 (t / 282) (t % 282)))) = true := by
  decide +kernel

theorem chkC_10_d17104 : (List.range' 17104 8).all (fun t => (!(pOK tl tl (t % 282) (t / 282)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 282 % 94) * 282) (x2Tab o (t / 282 / 94) (t % 282))) (x2Tab t3 (t / 282) (t % 282)))) = true := by
  decide +kernel

theorem chkC_10_d17112 : (List.range' 17112 8).all (fun t => (!(pOK tl tl (t % 282) (t / 282)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 282 % 94) * 282) (x2Tab o (t / 282 / 94) (t % 282))) (x2Tab t3 (t / 282) (t % 282)))) = true := by
  decide +kernel

theorem chkC_10_d17120 : (List.range' 17120 8).all (fun t => (!(pOK tl tl (t % 282) (t / 282)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 282 % 94) * 282) (x2Tab o (t / 282 / 94) (t % 282))) (x2Tab t3 (t / 282) (t % 282)))) = true := by
  decide +kernel

theorem chkC_10_d17128 : (List.range' 17128 8).all (fun t => (!(pOK tl tl (t % 282) (t / 282)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 282 % 94) * 282) (x2Tab o (t / 282 / 94) (t % 282))) (x2Tab t3 (t / 282) (t % 282)))) = true := by
  decide +kernel

theorem chkC_10_d17136 : (List.range' 17136 8).all (fun t => (!(pOK tl tl (t % 282) (t / 282)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 282 % 94) * 282) (x2Tab o (t / 282 / 94) (t % 282))) (x2Tab t3 (t / 282) (t % 282)))) = true := by
  decide +kernel

theorem chkC_10_d17144 : (List.range' 17144 8).all (fun t => (!(pOK tl tl (t % 282) (t / 282)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 282 % 94) * 282) (x2Tab o (t / 282 / 94) (t % 282))) (x2Tab t3 (t / 282) (t % 282)))) = true := by
  decide +kernel

theorem chkC_10_d17152 : (List.range' 17152 8).all (fun t => (!(pOK tl tl (t % 282) (t / 282)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 282 % 94) * 282) (x2Tab o (t / 282 / 94) (t % 282))) (x2Tab t3 (t / 282) (t % 282)))) = true := by
  decide +kernel

theorem chkC_10_d17160 : (List.range' 17160 8).all (fun t => (!(pOK tl tl (t % 282) (t / 282)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 282 % 94) * 282) (x2Tab o (t / 282 / 94) (t % 282))) (x2Tab t3 (t / 282) (t % 282)))) = true := by
  decide +kernel

theorem chkC_10_d17168 : (List.range' 17168 8).all (fun t => (!(pOK tl tl (t % 282) (t / 282)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 282 % 94) * 282) (x2Tab o (t / 282 / 94) (t % 282))) (x2Tab t3 (t / 282) (t % 282)))) = true := by
  decide +kernel

theorem chkC_10_d17176 : (List.range' 17176 8).all (fun t => (!(pOK tl tl (t % 282) (t / 282)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 282 % 94) * 282) (x2Tab o (t / 282 / 94) (t % 282))) (x2Tab t3 (t / 282) (t % 282)))) = true := by
  decide +kernel

theorem chkC_10_d17184 : (List.range' 17184 8).all (fun t => (!(pOK tl tl (t % 282) (t / 282)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 282 % 94) * 282) (x2Tab o (t / 282 / 94) (t % 282))) (x2Tab t3 (t / 282) (t % 282)))) = true := by
  decide +kernel

theorem chkC_10_d17192 : (List.range' 17192 8).all (fun t => (!(pOK tl tl (t % 282) (t / 282)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 282 % 94) * 282) (x2Tab o (t / 282 / 94) (t % 282))) (x2Tab t3 (t / 282) (t % 282)))) = true := by
  decide +kernel

theorem chkC_10_d17200 : (List.range' 17200 8).all (fun t => (!(pOK tl tl (t % 282) (t / 282)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 282 % 94) * 282) (x2Tab o (t / 282 / 94) (t % 282))) (x2Tab t3 (t / 282) (t % 282)))) = true := by
  decide +kernel

theorem chkC_10_d17208 : (List.range' 17208 8).all (fun t => (!(pOK tl tl (t % 282) (t / 282)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 282 % 94) * 282) (x2Tab o (t / 282 / 94) (t % 282))) (x2Tab t3 (t / 282) (t % 282)))) = true := by
  decide +kernel

theorem chkC_10_d17216 : (List.range' 17216 8).all (fun t => (!(pOK tl tl (t % 282) (t / 282)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 282 % 94) * 282) (x2Tab o (t / 282 / 94) (t % 282))) (x2Tab t3 (t / 282) (t % 282)))) = true := by
  decide +kernel

theorem chkC_10_d17224 : (List.range' 17224 8).all (fun t => (!(pOK tl tl (t % 282) (t / 282)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 282 % 94) * 282) (x2Tab o (t / 282 / 94) (t % 282))) (x2Tab t3 (t / 282) (t % 282)))) = true := by
  decide +kernel

theorem chkC_10_d17232 : (List.range' 17232 8).all (fun t => (!(pOK tl tl (t % 282) (t / 282)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 282 % 94) * 282) (x2Tab o (t / 282 / 94) (t % 282))) (x2Tab t3 (t / 282) (t % 282)))) = true := by
  decide +kernel

theorem chkC_10_d17240 : (List.range' 17240 8).all (fun t => (!(pOK tl tl (t % 282) (t / 282)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 282 % 94) * 282) (x2Tab o (t / 282 / 94) (t % 282))) (x2Tab t3 (t / 282) (t % 282)))) = true := by
  decide +kernel

theorem chkC_10_d17248 : (List.range' 17248 8).all (fun t => (!(pOK tl tl (t % 282) (t / 282)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 282 % 94) * 282) (x2Tab o (t / 282 / 94) (t % 282))) (x2Tab t3 (t / 282) (t % 282)))) = true := by
  decide +kernel

theorem chkC_10_d17256 : (List.range' 17256 8).all (fun t => (!(pOK tl tl (t % 282) (t / 282)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 282 % 94) * 282) (x2Tab o (t / 282 / 94) (t % 282))) (x2Tab t3 (t / 282) (t % 282)))) = true := by
  decide +kernel

theorem chkC_10_d17264 : (List.range' 17264 8).all (fun t => (!(pOK tl tl (t % 282) (t / 282)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 282 % 94) * 282) (x2Tab o (t / 282 / 94) (t % 282))) (x2Tab t3 (t / 282) (t % 282)))) = true := by
  decide +kernel

theorem chkC_10_d17272 : (List.range' 17272 8).all (fun t => (!(pOK tl tl (t % 282) (t / 282)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 282 % 94) * 282) (x2Tab o (t / 282 / 94) (t % 282))) (x2Tab t3 (t / 282) (t % 282)))) = true := by
  decide +kernel

theorem chkC_10_d17280 : (List.range' 17280 8).all (fun t => (!(pOK tl tl (t % 282) (t / 282)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 282 % 94) * 282) (x2Tab o (t / 282 / 94) (t % 282))) (x2Tab t3 (t / 282) (t % 282)))) = true := by
  decide +kernel

theorem chkC_10_d17288 : (List.range' 17288 8).all (fun t => (!(pOK tl tl (t % 282) (t / 282)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 282 % 94) * 282) (x2Tab o (t / 282 / 94) (t % 282))) (x2Tab t3 (t / 282) (t % 282)))) = true := by
  decide +kernel

theorem chkC_10_d17296 : (List.range' 17296 8).all (fun t => (!(pOK tl tl (t % 282) (t / 282)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 282 % 94) * 282) (x2Tab o (t / 282 / 94) (t % 282))) (x2Tab t3 (t / 282) (t % 282)))) = true := by
  decide +kernel

theorem chkC_10_d17304 : (List.range' 17304 8).all (fun t => (!(pOK tl tl (t % 282) (t / 282)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 282 % 94) * 282) (x2Tab o (t / 282 / 94) (t % 282))) (x2Tab t3 (t / 282) (t % 282)))) = true := by
  decide +kernel

theorem chkC_10_d17312 : (List.range' 17312 8).all (fun t => (!(pOK tl tl (t % 282) (t / 282)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 282 % 94) * 282) (x2Tab o (t / 282 / 94) (t % 282))) (x2Tab t3 (t / 282) (t % 282)))) = true := by
  decide +kernel

theorem chkC_10_d17320 : (List.range' 17320 8).all (fun t => (!(pOK tl tl (t % 282) (t / 282)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 282 % 94) * 282) (x2Tab o (t / 282 / 94) (t % 282))) (x2Tab t3 (t / 282) (t % 282)))) = true := by
  decide +kernel

theorem chkC_10_d17328 : (List.range' 17328 8).all (fun t => (!(pOK tl tl (t % 282) (t / 282)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 282 % 94) * 282) (x2Tab o (t / 282 / 94) (t % 282))) (x2Tab t3 (t / 282) (t % 282)))) = true := by
  decide +kernel

theorem chkC_10_d17336 : (List.range' 17336 8).all (fun t => (!(pOK tl tl (t % 282) (t / 282)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 282 % 94) * 282) (x2Tab o (t / 282 / 94) (t % 282))) (x2Tab t3 (t / 282) (t % 282)))) = true := by
  decide +kernel

theorem chkC_10_d17344 : (List.range' 17344 8).all (fun t => (!(pOK tl tl (t % 282) (t / 282)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 282 % 94) * 282) (x2Tab o (t / 282 / 94) (t % 282))) (x2Tab t3 (t / 282) (t % 282)))) = true := by
  decide +kernel

theorem chkC_10_d17352 : (List.range' 17352 8).all (fun t => (!(pOK tl tl (t % 282) (t / 282)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 282 % 94) * 282) (x2Tab o (t / 282 / 94) (t % 282))) (x2Tab t3 (t / 282) (t % 282)))) = true := by
  decide +kernel

theorem chkC_10_d17360 : (List.range' 17360 8).all (fun t => (!(pOK tl tl (t % 282) (t / 282)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 282 % 94) * 282) (x2Tab o (t / 282 / 94) (t % 282))) (x2Tab t3 (t / 282) (t % 282)))) = true := by
  decide +kernel

theorem chkC_10_d17368 : (List.range' 17368 8).all (fun t => (!(pOK tl tl (t % 282) (t / 282)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 282 % 94) * 282) (x2Tab o (t / 282 / 94) (t % 282))) (x2Tab t3 (t / 282) (t % 282)))) = true := by
  decide +kernel

theorem chkC_10_d17376 : (List.range' 17376 8).all (fun t => (!(pOK tl tl (t % 282) (t / 282)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 282 % 94) * 282) (x2Tab o (t / 282 / 94) (t % 282))) (x2Tab t3 (t / 282) (t % 282)))) = true := by
  decide +kernel

theorem chkC_10_d17384 : (List.range' 17384 8).all (fun t => (!(pOK tl tl (t % 282) (t / 282)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 282 % 94) * 282) (x2Tab o (t / 282 / 94) (t % 282))) (x2Tab t3 (t / 282) (t % 282)))) = true := by
  decide +kernel

theorem chkC_10_d17392 : (List.range' 17392 8).all (fun t => (!(pOK tl tl (t % 282) (t / 282)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 282 % 94) * 282) (x2Tab o (t / 282 / 94) (t % 282))) (x2Tab t3 (t / 282) (t % 282)))) = true := by
  decide +kernel

theorem chkC_10_d17400 : (List.range' 17400 8).all (fun t => (!(pOK tl tl (t % 282) (t / 282)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 282 % 94) * 282) (x2Tab o (t / 282 / 94) (t % 282))) (x2Tab t3 (t / 282) (t % 282)))) = true := by
  decide +kernel

theorem chkC_10_d17408 : (List.range' 17408 8).all (fun t => (!(pOK tl tl (t % 282) (t / 282)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 282 % 94) * 282) (x2Tab o (t / 282 / 94) (t % 282))) (x2Tab t3 (t / 282) (t % 282)))) = true := by
  decide +kernel

theorem chkC_10_d17416 : (List.range' 17416 8).all (fun t => (!(pOK tl tl (t % 282) (t / 282)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 282 % 94) * 282) (x2Tab o (t / 282 / 94) (t % 282))) (x2Tab t3 (t / 282) (t % 282)))) = true := by
  decide +kernel

theorem chkC_10_d17424 : (List.range' 17424 8).all (fun t => (!(pOK tl tl (t % 282) (t / 282)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 282 % 94) * 282) (x2Tab o (t / 282 / 94) (t % 282))) (x2Tab t3 (t / 282) (t % 282)))) = true := by
  decide +kernel

theorem chkC_10_d17432 : (List.range' 17432 8).all (fun t => (!(pOK tl tl (t % 282) (t / 282)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 282 % 94) * 282) (x2Tab o (t / 282 / 94) (t % 282))) (x2Tab t3 (t / 282) (t % 282)))) = true := by
  decide +kernel

theorem chkC_10_d17440 : (List.range' 17440 8).all (fun t => (!(pOK tl tl (t % 282) (t / 282)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 282 % 94) * 282) (x2Tab o (t / 282 / 94) (t % 282))) (x2Tab t3 (t / 282) (t % 282)))) = true := by
  decide +kernel

theorem chkC_10_d17448 : (List.range' 17448 8).all (fun t => (!(pOK tl tl (t % 282) (t / 282)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 282 % 94) * 282) (x2Tab o (t / 282 / 94) (t % 282))) (x2Tab t3 (t / 282) (t % 282)))) = true := by
  decide +kernel

theorem chkC_10_d17456 : (List.range' 17456 8).all (fun t => (!(pOK tl tl (t % 282) (t / 282)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 282 % 94) * 282) (x2Tab o (t / 282 / 94) (t % 282))) (x2Tab t3 (t / 282) (t % 282)))) = true := by
  decide +kernel

theorem chkC_10_d17464 : (List.range' 17464 8).all (fun t => (!(pOK tl tl (t % 282) (t / 282)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 282 % 94) * 282) (x2Tab o (t / 282 / 94) (t % 282))) (x2Tab t3 (t / 282) (t % 282)))) = true := by
  decide +kernel

theorem chkC_10_d17472 : (List.range' 17472 8).all (fun t => (!(pOK tl tl (t % 282) (t / 282)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 282 % 94) * 282) (x2Tab o (t / 282 / 94) (t % 282))) (x2Tab t3 (t / 282) (t % 282)))) = true := by
  decide +kernel

theorem chkC_10_d17480 : (List.range' 17480 8).all (fun t => (!(pOK tl tl (t % 282) (t / 282)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 282 % 94) * 282) (x2Tab o (t / 282 / 94) (t % 282))) (x2Tab t3 (t / 282) (t % 282)))) = true := by
  decide +kernel

theorem chkC_10_d17488 : (List.range' 17488 8).all (fun t => (!(pOK tl tl (t % 282) (t / 282)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 282 % 94) * 282) (x2Tab o (t / 282 / 94) (t % 282))) (x2Tab t3 (t / 282) (t % 282)))) = true := by
  decide +kernel

theorem chkC_10_d17496 : (List.range' 17496 8).all (fun t => (!(pOK tl tl (t % 282) (t / 282)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 282 % 94) * 282) (x2Tab o (t / 282 / 94) (t % 282))) (x2Tab t3 (t / 282) (t % 282)))) = true := by
  decide +kernel

theorem chkC_10_d17504 : (List.range' 17504 8).all (fun t => (!(pOK tl tl (t % 282) (t / 282)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 282 % 94) * 282) (x2Tab o (t / 282 / 94) (t % 282))) (x2Tab t3 (t / 282) (t % 282)))) = true := by
  decide +kernel

theorem chkC_10_d17512 : (List.range' 17512 8).all (fun t => (!(pOK tl tl (t % 282) (t / 282)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 282 % 94) * 282) (x2Tab o (t / 282 / 94) (t % 282))) (x2Tab t3 (t / 282) (t % 282)))) = true := by
  decide +kernel

theorem chkC_10_d17520 : (List.range' 17520 8).all (fun t => (!(pOK tl tl (t % 282) (t / 282)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 282 % 94) * 282) (x2Tab o (t / 282 / 94) (t % 282))) (x2Tab t3 (t / 282) (t % 282)))) = true := by
  decide +kernel

theorem chkC_10_d17528 : (List.range' 17528 8).all (fun t => (!(pOK tl tl (t % 282) (t / 282)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 282 % 94) * 282) (x2Tab o (t / 282 / 94) (t % 282))) (x2Tab t3 (t / 282) (t % 282)))) = true := by
  decide +kernel

theorem chkC_10_d17536 : (List.range' 17536 8).all (fun t => (!(pOK tl tl (t % 282) (t / 282)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 282 % 94) * 282) (x2Tab o (t / 282 / 94) (t % 282))) (x2Tab t3 (t / 282) (t % 282)))) = true := by
  decide +kernel

theorem chkC_10_d17544 : (List.range' 17544 8).all (fun t => (!(pOK tl tl (t % 282) (t / 282)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 282 % 94) * 282) (x2Tab o (t / 282 / 94) (t % 282))) (x2Tab t3 (t / 282) (t % 282)))) = true := by
  decide +kernel

theorem chkC_10_d17552 : (List.range' 17552 8).all (fun t => (!(pOK tl tl (t % 282) (t / 282)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 282 % 94) * 282) (x2Tab o (t / 282 / 94) (t % 282))) (x2Tab t3 (t / 282) (t % 282)))) = true := by
  decide +kernel

theorem chkC_10_d17560 : (List.range' 17560 8).all (fun t => (!(pOK tl tl (t % 282) (t / 282)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 282 % 94) * 282) (x2Tab o (t / 282 / 94) (t % 282))) (x2Tab t3 (t / 282) (t % 282)))) = true := by
  decide +kernel

theorem chkC_10_d17568 : (List.range' 17568 8).all (fun t => (!(pOK tl tl (t % 282) (t / 282)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 282 % 94) * 282) (x2Tab o (t / 282 / 94) (t % 282))) (x2Tab t3 (t / 282) (t % 282)))) = true := by
  decide +kernel

theorem chkC_10_d17576 : (List.range' 17576 8).all (fun t => (!(pOK tl tl (t % 282) (t / 282)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 282 % 94) * 282) (x2Tab o (t / 282 / 94) (t % 282))) (x2Tab t3 (t / 282) (t % 282)))) = true := by
  decide +kernel

theorem chkC_10_d17584 : (List.range' 17584 8).all (fun t => (!(pOK tl tl (t % 282) (t / 282)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 282 % 94) * 282) (x2Tab o (t / 282 / 94) (t % 282))) (x2Tab t3 (t / 282) (t % 282)))) = true := by
  decide +kernel

theorem chkC_10_d17592 : (List.range' 17592 8).all (fun t => (!(pOK tl tl (t % 282) (t / 282)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 282 % 94) * 282) (x2Tab o (t / 282 / 94) (t % 282))) (x2Tab t3 (t / 282) (t % 282)))) = true := by
  decide +kernel

theorem chkC_10 : ∀ t, 16000 ≤ t → t < 17600 → ((!(pOK tl tl (t % 282) (t / 282)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 282 % 94) * 282) (x2Tab o (t / 282 / 94) (t % 282))) (x2Tab t3 (t / 282) (t % 282)))) = true := by
  exact (x2c_join _ 16000 16008 17600 (x2c_range_all (fun t => (!(pOK tl tl (t % 282) (t / 282)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 282 % 94) * 282) (x2Tab o (t / 282 / 94) (t % 282))) (x2Tab t3 (t / 282) (t % 282)))) 16000 8 chkC_10_d16000) (x2c_join _ 16008 16016 17600 (x2c_range_all (fun t => (!(pOK tl tl (t % 282) (t / 282)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 282 % 94) * 282) (x2Tab o (t / 282 / 94) (t % 282))) (x2Tab t3 (t / 282) (t % 282)))) 16008 8 chkC_10_d16008) (x2c_join _ 16016 16024 17600 (x2c_range_all (fun t => (!(pOK tl tl (t % 282) (t / 282)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 282 % 94) * 282) (x2Tab o (t / 282 / 94) (t % 282))) (x2Tab t3 (t / 282) (t % 282)))) 16016 8 chkC_10_d16016) (x2c_join _ 16024 16032 17600 (x2c_range_all (fun t => (!(pOK tl tl (t % 282) (t / 282)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 282 % 94) * 282) (x2Tab o (t / 282 / 94) (t % 282))) (x2Tab t3 (t / 282) (t % 282)))) 16024 8 chkC_10_d16024) (x2c_join _ 16032 16040 17600 (x2c_range_all (fun t => (!(pOK tl tl (t % 282) (t / 282)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 282 % 94) * 282) (x2Tab o (t / 282 / 94) (t % 282))) (x2Tab t3 (t / 282) (t % 282)))) 16032 8 chkC_10_d16032) (x2c_join _ 16040 16048 17600 (x2c_range_all (fun t => (!(pOK tl tl (t % 282) (t / 282)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 282 % 94) * 282) (x2Tab o (t / 282 / 94) (t % 282))) (x2Tab t3 (t / 282) (t % 282)))) 16040 8 chkC_10_d16040) (x2c_join _ 16048 16056 17600 (x2c_range_all (fun t => (!(pOK tl tl (t % 282) (t / 282)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 282 % 94) * 282) (x2Tab o (t / 282 / 94) (t % 282))) (x2Tab t3 (t / 282) (t % 282)))) 16048 8 chkC_10_d16048) (x2c_join _ 16056 16064 17600 (x2c_range_all (fun t => (!(pOK tl tl (t % 282) (t / 282)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 282 % 94) * 282) (x2Tab o (t / 282 / 94) (t % 282))) (x2Tab t3 (t / 282) (t % 282)))) 16056 8 chkC_10_d16056) (x2c_join _ 16064 16072 17600 (x2c_range_all (fun t => (!(pOK tl tl (t % 282) (t / 282)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 282 % 94) * 282) (x2Tab o (t / 282 / 94) (t % 282))) (x2Tab t3 (t / 282) (t % 282)))) 16064 8 chkC_10_d16064) (x2c_join _ 16072 16080 17600 (x2c_range_all (fun t => (!(pOK tl tl (t % 282) (t / 282)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 282 % 94) * 282) (x2Tab o (t / 282 / 94) (t % 282))) (x2Tab t3 (t / 282) (t % 282)))) 16072 8 chkC_10_d16072) (x2c_join _ 16080 16088 17600 (x2c_range_all (fun t => (!(pOK tl tl (t % 282) (t / 282)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 282 % 94) * 282) (x2Tab o (t / 282 / 94) (t % 282))) (x2Tab t3 (t / 282) (t % 282)))) 16080 8 chkC_10_d16080) (x2c_join _ 16088 16096 17600 (x2c_range_all (fun t => (!(pOK tl tl (t % 282) (t / 282)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 282 % 94) * 282) (x2Tab o (t / 282 / 94) (t % 282))) (x2Tab t3 (t / 282) (t % 282)))) 16088 8 chkC_10_d16088) (x2c_join _ 16096 16104 17600 (x2c_range_all (fun t => (!(pOK tl tl (t % 282) (t / 282)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 282 % 94) * 282) (x2Tab o (t / 282 / 94) (t % 282))) (x2Tab t3 (t / 282) (t % 282)))) 16096 8 chkC_10_d16096) (x2c_join _ 16104 16112 17600 (x2c_range_all (fun t => (!(pOK tl tl (t % 282) (t / 282)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 282 % 94) * 282) (x2Tab o (t / 282 / 94) (t % 282))) (x2Tab t3 (t / 282) (t % 282)))) 16104 8 chkC_10_d16104) (x2c_join _ 16112 16120 17600 (x2c_range_all (fun t => (!(pOK tl tl (t % 282) (t / 282)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 282 % 94) * 282) (x2Tab o (t / 282 / 94) (t % 282))) (x2Tab t3 (t / 282) (t % 282)))) 16112 8 chkC_10_d16112) (x2c_join _ 16120 16128 17600 (x2c_range_all (fun t => (!(pOK tl tl (t % 282) (t / 282)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 282 % 94) * 282) (x2Tab o (t / 282 / 94) (t % 282))) (x2Tab t3 (t / 282) (t % 282)))) 16120 8 chkC_10_d16120) (x2c_join _ 16128 16136 17600 (x2c_range_all (fun t => (!(pOK tl tl (t % 282) (t / 282)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 282 % 94) * 282) (x2Tab o (t / 282 / 94) (t % 282))) (x2Tab t3 (t / 282) (t % 282)))) 16128 8 chkC_10_d16128) (x2c_join _ 16136 16144 17600 (x2c_range_all (fun t => (!(pOK tl tl (t % 282) (t / 282)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 282 % 94) * 282) (x2Tab o (t / 282 / 94) (t % 282))) (x2Tab t3 (t / 282) (t % 282)))) 16136 8 chkC_10_d16136) (x2c_join _ 16144 16152 17600 (x2c_range_all (fun t => (!(pOK tl tl (t % 282) (t / 282)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 282 % 94) * 282) (x2Tab o (t / 282 / 94) (t % 282))) (x2Tab t3 (t / 282) (t % 282)))) 16144 8 chkC_10_d16144) (x2c_join _ 16152 16160 17600 (x2c_range_all (fun t => (!(pOK tl tl (t % 282) (t / 282)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 282 % 94) * 282) (x2Tab o (t / 282 / 94) (t % 282))) (x2Tab t3 (t / 282) (t % 282)))) 16152 8 chkC_10_d16152) (x2c_join _ 16160 16168 17600 (x2c_range_all (fun t => (!(pOK tl tl (t % 282) (t / 282)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 282 % 94) * 282) (x2Tab o (t / 282 / 94) (t % 282))) (x2Tab t3 (t / 282) (t % 282)))) 16160 8 chkC_10_d16160) (x2c_join _ 16168 16176 17600 (x2c_range_all (fun t => (!(pOK tl tl (t % 282) (t / 282)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 282 % 94) * 282) (x2Tab o (t / 282 / 94) (t % 282))) (x2Tab t3 (t / 282) (t % 282)))) 16168 8 chkC_10_d16168) (x2c_join _ 16176 16184 17600 (x2c_range_all (fun t => (!(pOK tl tl (t % 282) (t / 282)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 282 % 94) * 282) (x2Tab o (t / 282 / 94) (t % 282))) (x2Tab t3 (t / 282) (t % 282)))) 16176 8 chkC_10_d16176) (x2c_join _ 16184 16192 17600 (x2c_range_all (fun t => (!(pOK tl tl (t % 282) (t / 282)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 282 % 94) * 282) (x2Tab o (t / 282 / 94) (t % 282))) (x2Tab t3 (t / 282) (t % 282)))) 16184 8 chkC_10_d16184) (x2c_join _ 16192 16200 17600 (x2c_range_all (fun t => (!(pOK tl tl (t % 282) (t / 282)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 282 % 94) * 282) (x2Tab o (t / 282 / 94) (t % 282))) (x2Tab t3 (t / 282) (t % 282)))) 16192 8 chkC_10_d16192) (x2c_join _ 16200 16208 17600 (x2c_range_all (fun t => (!(pOK tl tl (t % 282) (t / 282)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 282 % 94) * 282) (x2Tab o (t / 282 / 94) (t % 282))) (x2Tab t3 (t / 282) (t % 282)))) 16200 8 chkC_10_d16200) (x2c_join _ 16208 16216 17600 (x2c_range_all (fun t => (!(pOK tl tl (t % 282) (t / 282)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 282 % 94) * 282) (x2Tab o (t / 282 / 94) (t % 282))) (x2Tab t3 (t / 282) (t % 282)))) 16208 8 chkC_10_d16208) (x2c_join _ 16216 16224 17600 (x2c_range_all (fun t => (!(pOK tl tl (t % 282) (t / 282)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 282 % 94) * 282) (x2Tab o (t / 282 / 94) (t % 282))) (x2Tab t3 (t / 282) (t % 282)))) 16216 8 chkC_10_d16216) (x2c_join _ 16224 16232 17600 (x2c_range_all (fun t => (!(pOK tl tl (t % 282) (t / 282)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 282 % 94) * 282) (x2Tab o (t / 282 / 94) (t % 282))) (x2Tab t3 (t / 282) (t % 282)))) 16224 8 chkC_10_d16224) (x2c_join _ 16232 16240 17600 (x2c_range_all (fun t => (!(pOK tl tl (t % 282) (t / 282)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 282 % 94) * 282) (x2Tab o (t / 282 / 94) (t % 282))) (x2Tab t3 (t / 282) (t % 282)))) 16232 8 chkC_10_d16232) (x2c_join _ 16240 16248 17600 (x2c_range_all (fun t => (!(pOK tl tl (t % 282) (t / 282)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 282 % 94) * 282) (x2Tab o (t / 282 / 94) (t % 282))) (x2Tab t3 (t / 282) (t % 282)))) 16240 8 chkC_10_d16240) (x2c_join _ 16248 16256 17600 (x2c_range_all (fun t => (!(pOK tl tl (t % 282) (t / 282)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 282 % 94) * 282) (x2Tab o (t / 282 / 94) (t % 282))) (x2Tab t3 (t / 282) (t % 282)))) 16248 8 chkC_10_d16248) (x2c_join _ 16256 16264 17600 (x2c_range_all (fun t => (!(pOK tl tl (t % 282) (t / 282)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 282 % 94) * 282) (x2Tab o (t / 282 / 94) (t % 282))) (x2Tab t3 (t / 282) (t % 282)))) 16256 8 chkC_10_d16256) (x2c_join _ 16264 16272 17600 (x2c_range_all (fun t => (!(pOK tl tl (t % 282) (t / 282)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 282 % 94) * 282) (x2Tab o (t / 282 / 94) (t % 282))) (x2Tab t3 (t / 282) (t % 282)))) 16264 8 chkC_10_d16264) (x2c_join _ 16272 16280 17600 (x2c_range_all (fun t => (!(pOK tl tl (t % 282) (t / 282)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 282 % 94) * 282) (x2Tab o (t / 282 / 94) (t % 282))) (x2Tab t3 (t / 282) (t % 282)))) 16272 8 chkC_10_d16272) (x2c_join _ 16280 16288 17600 (x2c_range_all (fun t => (!(pOK tl tl (t % 282) (t / 282)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 282 % 94) * 282) (x2Tab o (t / 282 / 94) (t % 282))) (x2Tab t3 (t / 282) (t % 282)))) 16280 8 chkC_10_d16280) (x2c_join _ 16288 16296 17600 (x2c_range_all (fun t => (!(pOK tl tl (t % 282) (t / 282)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 282 % 94) * 282) (x2Tab o (t / 282 / 94) (t % 282))) (x2Tab t3 (t / 282) (t % 282)))) 16288 8 chkC_10_d16288) (x2c_join _ 16296 16304 17600 (x2c_range_all (fun t => (!(pOK tl tl (t % 282) (t / 282)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 282 % 94) * 282) (x2Tab o (t / 282 / 94) (t % 282))) (x2Tab t3 (t / 282) (t % 282)))) 16296 8 chkC_10_d16296) (x2c_join _ 16304 16312 17600 (x2c_range_all (fun t => (!(pOK tl tl (t % 282) (t / 282)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 282 % 94) * 282) (x2Tab o (t / 282 / 94) (t % 282))) (x2Tab t3 (t / 282) (t % 282)))) 16304 8 chkC_10_d16304) (x2c_join _ 16312 16320 17600 (x2c_range_all (fun t => (!(pOK tl tl (t % 282) (t / 282)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 282 % 94) * 282) (x2Tab o (t / 282 / 94) (t % 282))) (x2Tab t3 (t / 282) (t % 282)))) 16312 8 chkC_10_d16312) (x2c_join _ 16320 16328 17600 (x2c_range_all (fun t => (!(pOK tl tl (t % 282) (t / 282)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 282 % 94) * 282) (x2Tab o (t / 282 / 94) (t % 282))) (x2Tab t3 (t / 282) (t % 282)))) 16320 8 chkC_10_d16320) (x2c_join _ 16328 16336 17600 (x2c_range_all (fun t => (!(pOK tl tl (t % 282) (t / 282)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 282 % 94) * 282) (x2Tab o (t / 282 / 94) (t % 282))) (x2Tab t3 (t / 282) (t % 282)))) 16328 8 chkC_10_d16328) (x2c_join _ 16336 16344 17600 (x2c_range_all (fun t => (!(pOK tl tl (t % 282) (t / 282)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 282 % 94) * 282) (x2Tab o (t / 282 / 94) (t % 282))) (x2Tab t3 (t / 282) (t % 282)))) 16336 8 chkC_10_d16336) (x2c_join _ 16344 16352 17600 (x2c_range_all (fun t => (!(pOK tl tl (t % 282) (t / 282)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 282 % 94) * 282) (x2Tab o (t / 282 / 94) (t % 282))) (x2Tab t3 (t / 282) (t % 282)))) 16344 8 chkC_10_d16344) (x2c_join _ 16352 16360 17600 (x2c_range_all (fun t => (!(pOK tl tl (t % 282) (t / 282)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 282 % 94) * 282) (x2Tab o (t / 282 / 94) (t % 282))) (x2Tab t3 (t / 282) (t % 282)))) 16352 8 chkC_10_d16352) (x2c_join _ 16360 16368 17600 (x2c_range_all (fun t => (!(pOK tl tl (t % 282) (t / 282)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 282 % 94) * 282) (x2Tab o (t / 282 / 94) (t % 282))) (x2Tab t3 (t / 282) (t % 282)))) 16360 8 chkC_10_d16360) (x2c_join _ 16368 16376 17600 (x2c_range_all (fun t => (!(pOK tl tl (t % 282) (t / 282)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 282 % 94) * 282) (x2Tab o (t / 282 / 94) (t % 282))) (x2Tab t3 (t / 282) (t % 282)))) 16368 8 chkC_10_d16368) (x2c_join _ 16376 16384 17600 (x2c_range_all (fun t => (!(pOK tl tl (t % 282) (t / 282)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 282 % 94) * 282) (x2Tab o (t / 282 / 94) (t % 282))) (x2Tab t3 (t / 282) (t % 282)))) 16376 8 chkC_10_d16376) (x2c_join _ 16384 16392 17600 (x2c_range_all (fun t => (!(pOK tl tl (t % 282) (t / 282)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 282 % 94) * 282) (x2Tab o (t / 282 / 94) (t % 282))) (x2Tab t3 (t / 282) (t % 282)))) 16384 8 chkC_10_d16384) (x2c_join _ 16392 16400 17600 (x2c_range_all (fun t => (!(pOK tl tl (t % 282) (t / 282)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 282 % 94) * 282) (x2Tab o (t / 282 / 94) (t % 282))) (x2Tab t3 (t / 282) (t % 282)))) 16392 8 chkC_10_d16392) (x2c_join _ 16400 16408 17600 (x2c_range_all (fun t => (!(pOK tl tl (t % 282) (t / 282)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 282 % 94) * 282) (x2Tab o (t / 282 / 94) (t % 282))) (x2Tab t3 (t / 282) (t % 282)))) 16400 8 chkC_10_d16400) (x2c_join _ 16408 16416 17600 (x2c_range_all (fun t => (!(pOK tl tl (t % 282) (t / 282)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 282 % 94) * 282) (x2Tab o (t / 282 / 94) (t % 282))) (x2Tab t3 (t / 282) (t % 282)))) 16408 8 chkC_10_d16408) (x2c_join _ 16416 16424 17600 (x2c_range_all (fun t => (!(pOK tl tl (t % 282) (t / 282)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 282 % 94) * 282) (x2Tab o (t / 282 / 94) (t % 282))) (x2Tab t3 (t / 282) (t % 282)))) 16416 8 chkC_10_d16416) (x2c_join _ 16424 16432 17600 (x2c_range_all (fun t => (!(pOK tl tl (t % 282) (t / 282)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 282 % 94) * 282) (x2Tab o (t / 282 / 94) (t % 282))) (x2Tab t3 (t / 282) (t % 282)))) 16424 8 chkC_10_d16424) (x2c_join _ 16432 16440 17600 (x2c_range_all (fun t => (!(pOK tl tl (t % 282) (t / 282)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 282 % 94) * 282) (x2Tab o (t / 282 / 94) (t % 282))) (x2Tab t3 (t / 282) (t % 282)))) 16432 8 chkC_10_d16432) (x2c_join _ 16440 16448 17600 (x2c_range_all (fun t => (!(pOK tl tl (t % 282) (t / 282)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 282 % 94) * 282) (x2Tab o (t / 282 / 94) (t % 282))) (x2Tab t3 (t / 282) (t % 282)))) 16440 8 chkC_10_d16440) (x2c_join _ 16448 16456 17600 (x2c_range_all (fun t => (!(pOK tl tl (t % 282) (t / 282)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 282 % 94) * 282) (x2Tab o (t / 282 / 94) (t % 282))) (x2Tab t3 (t / 282) (t % 282)))) 16448 8 chkC_10_d16448) (x2c_join _ 16456 16464 17600 (x2c_range_all (fun t => (!(pOK tl tl (t % 282) (t / 282)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 282 % 94) * 282) (x2Tab o (t / 282 / 94) (t % 282))) (x2Tab t3 (t / 282) (t % 282)))) 16456 8 chkC_10_d16456) (x2c_join _ 16464 16472 17600 (x2c_range_all (fun t => (!(pOK tl tl (t % 282) (t / 282)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 282 % 94) * 282) (x2Tab o (t / 282 / 94) (t % 282))) (x2Tab t3 (t / 282) (t % 282)))) 16464 8 chkC_10_d16464) (x2c_join _ 16472 16480 17600 (x2c_range_all (fun t => (!(pOK tl tl (t % 282) (t / 282)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 282 % 94) * 282) (x2Tab o (t / 282 / 94) (t % 282))) (x2Tab t3 (t / 282) (t % 282)))) 16472 8 chkC_10_d16472) (x2c_join _ 16480 16488 17600 (x2c_range_all (fun t => (!(pOK tl tl (t % 282) (t / 282)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 282 % 94) * 282) (x2Tab o (t / 282 / 94) (t % 282))) (x2Tab t3 (t / 282) (t % 282)))) 16480 8 chkC_10_d16480) (x2c_join _ 16488 16496 17600 (x2c_range_all (fun t => (!(pOK tl tl (t % 282) (t / 282)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 282 % 94) * 282) (x2Tab o (t / 282 / 94) (t % 282))) (x2Tab t3 (t / 282) (t % 282)))) 16488 8 chkC_10_d16488) (x2c_join _ 16496 16504 17600 (x2c_range_all (fun t => (!(pOK tl tl (t % 282) (t / 282)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 282 % 94) * 282) (x2Tab o (t / 282 / 94) (t % 282))) (x2Tab t3 (t / 282) (t % 282)))) 16496 8 chkC_10_d16496) (x2c_join _ 16504 16512 17600 (x2c_range_all (fun t => (!(pOK tl tl (t % 282) (t / 282)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 282 % 94) * 282) (x2Tab o (t / 282 / 94) (t % 282))) (x2Tab t3 (t / 282) (t % 282)))) 16504 8 chkC_10_d16504) (x2c_join _ 16512 16520 17600 (x2c_range_all (fun t => (!(pOK tl tl (t % 282) (t / 282)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 282 % 94) * 282) (x2Tab o (t / 282 / 94) (t % 282))) (x2Tab t3 (t / 282) (t % 282)))) 16512 8 chkC_10_d16512) (x2c_join _ 16520 16528 17600 (x2c_range_all (fun t => (!(pOK tl tl (t % 282) (t / 282)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 282 % 94) * 282) (x2Tab o (t / 282 / 94) (t % 282))) (x2Tab t3 (t / 282) (t % 282)))) 16520 8 chkC_10_d16520) (x2c_join _ 16528 16536 17600 (x2c_range_all (fun t => (!(pOK tl tl (t % 282) (t / 282)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 282 % 94) * 282) (x2Tab o (t / 282 / 94) (t % 282))) (x2Tab t3 (t / 282) (t % 282)))) 16528 8 chkC_10_d16528) (x2c_join _ 16536 16544 17600 (x2c_range_all (fun t => (!(pOK tl tl (t % 282) (t / 282)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 282 % 94) * 282) (x2Tab o (t / 282 / 94) (t % 282))) (x2Tab t3 (t / 282) (t % 282)))) 16536 8 chkC_10_d16536) (x2c_join _ 16544 16552 17600 (x2c_range_all (fun t => (!(pOK tl tl (t % 282) (t / 282)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 282 % 94) * 282) (x2Tab o (t / 282 / 94) (t % 282))) (x2Tab t3 (t / 282) (t % 282)))) 16544 8 chkC_10_d16544) (x2c_join _ 16552 16560 17600 (x2c_range_all (fun t => (!(pOK tl tl (t % 282) (t / 282)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 282 % 94) * 282) (x2Tab o (t / 282 / 94) (t % 282))) (x2Tab t3 (t / 282) (t % 282)))) 16552 8 chkC_10_d16552) (x2c_join _ 16560 16568 17600 (x2c_range_all (fun t => (!(pOK tl tl (t % 282) (t / 282)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 282 % 94) * 282) (x2Tab o (t / 282 / 94) (t % 282))) (x2Tab t3 (t / 282) (t % 282)))) 16560 8 chkC_10_d16560) (x2c_join _ 16568 16576 17600 (x2c_range_all (fun t => (!(pOK tl tl (t % 282) (t / 282)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 282 % 94) * 282) (x2Tab o (t / 282 / 94) (t % 282))) (x2Tab t3 (t / 282) (t % 282)))) 16568 8 chkC_10_d16568) (x2c_join _ 16576 16584 17600 (x2c_range_all (fun t => (!(pOK tl tl (t % 282) (t / 282)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 282 % 94) * 282) (x2Tab o (t / 282 / 94) (t % 282))) (x2Tab t3 (t / 282) (t % 282)))) 16576 8 chkC_10_d16576) (x2c_join _ 16584 16592 17600 (x2c_range_all (fun t => (!(pOK tl tl (t % 282) (t / 282)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 282 % 94) * 282) (x2Tab o (t / 282 / 94) (t % 282))) (x2Tab t3 (t / 282) (t % 282)))) 16584 8 chkC_10_d16584) (x2c_join _ 16592 16600 17600 (x2c_range_all (fun t => (!(pOK tl tl (t % 282) (t / 282)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 282 % 94) * 282) (x2Tab o (t / 282 / 94) (t % 282))) (x2Tab t3 (t / 282) (t % 282)))) 16592 8 chkC_10_d16592) (x2c_join _ 16600 16608 17600 (x2c_range_all (fun t => (!(pOK tl tl (t % 282) (t / 282)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 282 % 94) * 282) (x2Tab o (t / 282 / 94) (t % 282))) (x2Tab t3 (t / 282) (t % 282)))) 16600 8 chkC_10_d16600) (x2c_join _ 16608 16616 17600 (x2c_range_all (fun t => (!(pOK tl tl (t % 282) (t / 282)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 282 % 94) * 282) (x2Tab o (t / 282 / 94) (t % 282))) (x2Tab t3 (t / 282) (t % 282)))) 16608 8 chkC_10_d16608) (x2c_join _ 16616 16624 17600 (x2c_range_all (fun t => (!(pOK tl tl (t % 282) (t / 282)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 282 % 94) * 282) (x2Tab o (t / 282 / 94) (t % 282))) (x2Tab t3 (t / 282) (t % 282)))) 16616 8 chkC_10_d16616) (x2c_join _ 16624 16632 17600 (x2c_range_all (fun t => (!(pOK tl tl (t % 282) (t / 282)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 282 % 94) * 282) (x2Tab o (t / 282 / 94) (t % 282))) (x2Tab t3 (t / 282) (t % 282)))) 16624 8 chkC_10_d16624) (x2c_join _ 16632 16640 17600 (x2c_range_all (fun t => (!(pOK tl tl (t % 282) (t / 282)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 282 % 94) * 282) (x2Tab o (t / 282 / 94) (t % 282))) (x2Tab t3 (t / 282) (t % 282)))) 16632 8 chkC_10_d16632) (x2c_join _ 16640 16648 17600 (x2c_range_all (fun t => (!(pOK tl tl (t % 282) (t / 282)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 282 % 94) * 282) (x2Tab o (t / 282 / 94) (t % 282))) (x2Tab t3 (t / 282) (t % 282)))) 16640 8 chkC_10_d16640) (x2c_join _ 16648 16656 17600 (x2c_range_all (fun t => (!(pOK tl tl (t % 282) (t / 282)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 282 % 94) * 282) (x2Tab o (t / 282 / 94) (t % 282))) (x2Tab t3 (t / 282) (t % 282)))) 16648 8 chkC_10_d16648) (x2c_join _ 16656 16664 17600 (x2c_range_all (fun t => (!(pOK tl tl (t % 282) (t / 282)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 282 % 94) * 282) (x2Tab o (t / 282 / 94) (t % 282))) (x2Tab t3 (t / 282) (t % 282)))) 16656 8 chkC_10_d16656) (x2c_join _ 16664 16672 17600 (x2c_range_all (fun t => (!(pOK tl tl (t % 282) (t / 282)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 282 % 94) * 282) (x2Tab o (t / 282 / 94) (t % 282))) (x2Tab t3 (t / 282) (t % 282)))) 16664 8 chkC_10_d16664) (x2c_join _ 16672 16680 17600 (x2c_range_all (fun t => (!(pOK tl tl (t % 282) (t / 282)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 282 % 94) * 282) (x2Tab o (t / 282 / 94) (t % 282))) (x2Tab t3 (t / 282) (t % 282)))) 16672 8 chkC_10_d16672) (x2c_join _ 16680 16688 17600 (x2c_range_all (fun t => (!(pOK tl tl (t % 282) (t / 282)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 282 % 94) * 282) (x2Tab o (t / 282 / 94) (t % 282))) (x2Tab t3 (t / 282) (t % 282)))) 16680 8 chkC_10_d16680) (x2c_join _ 16688 16696 17600 (x2c_range_all (fun t => (!(pOK tl tl (t % 282) (t / 282)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 282 % 94) * 282) (x2Tab o (t / 282 / 94) (t % 282))) (x2Tab t3 (t / 282) (t % 282)))) 16688 8 chkC_10_d16688) (x2c_join _ 16696 16704 17600 (x2c_range_all (fun t => (!(pOK tl tl (t % 282) (t / 282)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 282 % 94) * 282) (x2Tab o (t / 282 / 94) (t % 282))) (x2Tab t3 (t / 282) (t % 282)))) 16696 8 chkC_10_d16696) (x2c_join _ 16704 16712 17600 (x2c_range_all (fun t => (!(pOK tl tl (t % 282) (t / 282)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 282 % 94) * 282) (x2Tab o (t / 282 / 94) (t % 282))) (x2Tab t3 (t / 282) (t % 282)))) 16704 8 chkC_10_d16704) (x2c_join _ 16712 16720 17600 (x2c_range_all (fun t => (!(pOK tl tl (t % 282) (t / 282)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 282 % 94) * 282) (x2Tab o (t / 282 / 94) (t % 282))) (x2Tab t3 (t / 282) (t % 282)))) 16712 8 chkC_10_d16712) (x2c_join _ 16720 16728 17600 (x2c_range_all (fun t => (!(pOK tl tl (t % 282) (t / 282)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 282 % 94) * 282) (x2Tab o (t / 282 / 94) (t % 282))) (x2Tab t3 (t / 282) (t % 282)))) 16720 8 chkC_10_d16720) (x2c_join _ 16728 16736 17600 (x2c_range_all (fun t => (!(pOK tl tl (t % 282) (t / 282)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 282 % 94) * 282) (x2Tab o (t / 282 / 94) (t % 282))) (x2Tab t3 (t / 282) (t % 282)))) 16728 8 chkC_10_d16728) (x2c_join _ 16736 16744 17600 (x2c_range_all (fun t => (!(pOK tl tl (t % 282) (t / 282)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 282 % 94) * 282) (x2Tab o (t / 282 / 94) (t % 282))) (x2Tab t3 (t / 282) (t % 282)))) 16736 8 chkC_10_d16736) (x2c_join _ 16744 16752 17600 (x2c_range_all (fun t => (!(pOK tl tl (t % 282) (t / 282)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 282 % 94) * 282) (x2Tab o (t / 282 / 94) (t % 282))) (x2Tab t3 (t / 282) (t % 282)))) 16744 8 chkC_10_d16744) (x2c_join _ 16752 16760 17600 (x2c_range_all (fun t => (!(pOK tl tl (t % 282) (t / 282)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 282 % 94) * 282) (x2Tab o (t / 282 / 94) (t % 282))) (x2Tab t3 (t / 282) (t % 282)))) 16752 8 chkC_10_d16752) (x2c_join _ 16760 16768 17600 (x2c_range_all (fun t => (!(pOK tl tl (t % 282) (t / 282)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 282 % 94) * 282) (x2Tab o (t / 282 / 94) (t % 282))) (x2Tab t3 (t / 282) (t % 282)))) 16760 8 chkC_10_d16760) (x2c_join _ 16768 16776 17600 (x2c_range_all (fun t => (!(pOK tl tl (t % 282) (t / 282)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 282 % 94) * 282) (x2Tab o (t / 282 / 94) (t % 282))) (x2Tab t3 (t / 282) (t % 282)))) 16768 8 chkC_10_d16768) (x2c_join _ 16776 16784 17600 (x2c_range_all (fun t => (!(pOK tl tl (t % 282) (t / 282)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 282 % 94) * 282) (x2Tab o (t / 282 / 94) (t % 282))) (x2Tab t3 (t / 282) (t % 282)))) 16776 8 chkC_10_d16776) (x2c_join _ 16784 16792 17600 (x2c_range_all (fun t => (!(pOK tl tl (t % 282) (t / 282)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 282 % 94) * 282) (x2Tab o (t / 282 / 94) (t % 282))) (x2Tab t3 (t / 282) (t % 282)))) 16784 8 chkC_10_d16784) (x2c_join _ 16792 16800 17600 (x2c_range_all (fun t => (!(pOK tl tl (t % 282) (t / 282)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 282 % 94) * 282) (x2Tab o (t / 282 / 94) (t % 282))) (x2Tab t3 (t / 282) (t % 282)))) 16792 8 chkC_10_d16792) (x2c_join _ 16800 16808 17600 (x2c_range_all (fun t => (!(pOK tl tl (t % 282) (t / 282)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 282 % 94) * 282) (x2Tab o (t / 282 / 94) (t % 282))) (x2Tab t3 (t / 282) (t % 282)))) 16800 8 chkC_10_d16800) (x2c_join _ 16808 16816 17600 (x2c_range_all (fun t => (!(pOK tl tl (t % 282) (t / 282)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 282 % 94) * 282) (x2Tab o (t / 282 / 94) (t % 282))) (x2Tab t3 (t / 282) (t % 282)))) 16808 8 chkC_10_d16808) (x2c_join _ 16816 16824 17600 (x2c_range_all (fun t => (!(pOK tl tl (t % 282) (t / 282)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 282 % 94) * 282) (x2Tab o (t / 282 / 94) (t % 282))) (x2Tab t3 (t / 282) (t % 282)))) 16816 8 chkC_10_d16816) (x2c_join _ 16824 16832 17600 (x2c_range_all (fun t => (!(pOK tl tl (t % 282) (t / 282)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 282 % 94) * 282) (x2Tab o (t / 282 / 94) (t % 282))) (x2Tab t3 (t / 282) (t % 282)))) 16824 8 chkC_10_d16824) (x2c_join _ 16832 16840 17600 (x2c_range_all (fun t => (!(pOK tl tl (t % 282) (t / 282)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 282 % 94) * 282) (x2Tab o (t / 282 / 94) (t % 282))) (x2Tab t3 (t / 282) (t % 282)))) 16832 8 chkC_10_d16832) (x2c_join _ 16840 16848 17600 (x2c_range_all (fun t => (!(pOK tl tl (t % 282) (t / 282)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 282 % 94) * 282) (x2Tab o (t / 282 / 94) (t % 282))) (x2Tab t3 (t / 282) (t % 282)))) 16840 8 chkC_10_d16840) (x2c_join _ 16848 16856 17600 (x2c_range_all (fun t => (!(pOK tl tl (t % 282) (t / 282)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 282 % 94) * 282) (x2Tab o (t / 282 / 94) (t % 282))) (x2Tab t3 (t / 282) (t % 282)))) 16848 8 chkC_10_d16848) (x2c_join _ 16856 16864 17600 (x2c_range_all (fun t => (!(pOK tl tl (t % 282) (t / 282)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 282 % 94) * 282) (x2Tab o (t / 282 / 94) (t % 282))) (x2Tab t3 (t / 282) (t % 282)))) 16856 8 chkC_10_d16856) (x2c_join _ 16864 16872 17600 (x2c_range_all (fun t => (!(pOK tl tl (t % 282) (t / 282)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 282 % 94) * 282) (x2Tab o (t / 282 / 94) (t % 282))) (x2Tab t3 (t / 282) (t % 282)))) 16864 8 chkC_10_d16864) (x2c_join _ 16872 16880 17600 (x2c_range_all (fun t => (!(pOK tl tl (t % 282) (t / 282)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 282 % 94) * 282) (x2Tab o (t / 282 / 94) (t % 282))) (x2Tab t3 (t / 282) (t % 282)))) 16872 8 chkC_10_d16872) (x2c_join _ 16880 16888 17600 (x2c_range_all (fun t => (!(pOK tl tl (t % 282) (t / 282)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 282 % 94) * 282) (x2Tab o (t / 282 / 94) (t % 282))) (x2Tab t3 (t / 282) (t % 282)))) 16880 8 chkC_10_d16880) (x2c_join _ 16888 16896 17600 (x2c_range_all (fun t => (!(pOK tl tl (t % 282) (t / 282)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 282 % 94) * 282) (x2Tab o (t / 282 / 94) (t % 282))) (x2Tab t3 (t / 282) (t % 282)))) 16888 8 chkC_10_d16888) (x2c_join _ 16896 16904 17600 (x2c_range_all (fun t => (!(pOK tl tl (t % 282) (t / 282)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 282 % 94) * 282) (x2Tab o (t / 282 / 94) (t % 282))) (x2Tab t3 (t / 282) (t % 282)))) 16896 8 chkC_10_d16896) (x2c_join _ 16904 16912 17600 (x2c_range_all (fun t => (!(pOK tl tl (t % 282) (t / 282)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 282 % 94) * 282) (x2Tab o (t / 282 / 94) (t % 282))) (x2Tab t3 (t / 282) (t % 282)))) 16904 8 chkC_10_d16904) (x2c_join _ 16912 16920 17600 (x2c_range_all (fun t => (!(pOK tl tl (t % 282) (t / 282)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 282 % 94) * 282) (x2Tab o (t / 282 / 94) (t % 282))) (x2Tab t3 (t / 282) (t % 282)))) 16912 8 chkC_10_d16912) (x2c_join _ 16920 16928 17600 (x2c_range_all (fun t => (!(pOK tl tl (t % 282) (t / 282)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 282 % 94) * 282) (x2Tab o (t / 282 / 94) (t % 282))) (x2Tab t3 (t / 282) (t % 282)))) 16920 8 chkC_10_d16920) (x2c_join _ 16928 16936 17600 (x2c_range_all (fun t => (!(pOK tl tl (t % 282) (t / 282)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 282 % 94) * 282) (x2Tab o (t / 282 / 94) (t % 282))) (x2Tab t3 (t / 282) (t % 282)))) 16928 8 chkC_10_d16928) (x2c_join _ 16936 16944 17600 (x2c_range_all (fun t => (!(pOK tl tl (t % 282) (t / 282)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 282 % 94) * 282) (x2Tab o (t / 282 / 94) (t % 282))) (x2Tab t3 (t / 282) (t % 282)))) 16936 8 chkC_10_d16936) (x2c_join _ 16944 16952 17600 (x2c_range_all (fun t => (!(pOK tl tl (t % 282) (t / 282)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 282 % 94) * 282) (x2Tab o (t / 282 / 94) (t % 282))) (x2Tab t3 (t / 282) (t % 282)))) 16944 8 chkC_10_d16944) (x2c_join _ 16952 16960 17600 (x2c_range_all (fun t => (!(pOK tl tl (t % 282) (t / 282)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 282 % 94) * 282) (x2Tab o (t / 282 / 94) (t % 282))) (x2Tab t3 (t / 282) (t % 282)))) 16952 8 chkC_10_d16952) (x2c_join _ 16960 16968 17600 (x2c_range_all (fun t => (!(pOK tl tl (t % 282) (t / 282)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 282 % 94) * 282) (x2Tab o (t / 282 / 94) (t % 282))) (x2Tab t3 (t / 282) (t % 282)))) 16960 8 chkC_10_d16960) (x2c_join _ 16968 16976 17600 (x2c_range_all (fun t => (!(pOK tl tl (t % 282) (t / 282)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 282 % 94) * 282) (x2Tab o (t / 282 / 94) (t % 282))) (x2Tab t3 (t / 282) (t % 282)))) 16968 8 chkC_10_d16968) (x2c_join _ 16976 16984 17600 (x2c_range_all (fun t => (!(pOK tl tl (t % 282) (t / 282)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 282 % 94) * 282) (x2Tab o (t / 282 / 94) (t % 282))) (x2Tab t3 (t / 282) (t % 282)))) 16976 8 chkC_10_d16976) (x2c_join _ 16984 16992 17600 (x2c_range_all (fun t => (!(pOK tl tl (t % 282) (t / 282)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 282 % 94) * 282) (x2Tab o (t / 282 / 94) (t % 282))) (x2Tab t3 (t / 282) (t % 282)))) 16984 8 chkC_10_d16984) (x2c_join _ 16992 17000 17600 (x2c_range_all (fun t => (!(pOK tl tl (t % 282) (t / 282)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 282 % 94) * 282) (x2Tab o (t / 282 / 94) (t % 282))) (x2Tab t3 (t / 282) (t % 282)))) 16992 8 chkC_10_d16992) (x2c_join _ 17000 17008 17600 (x2c_range_all (fun t => (!(pOK tl tl (t % 282) (t / 282)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 282 % 94) * 282) (x2Tab o (t / 282 / 94) (t % 282))) (x2Tab t3 (t / 282) (t % 282)))) 17000 8 chkC_10_d17000) (x2c_join _ 17008 17016 17600 (x2c_range_all (fun t => (!(pOK tl tl (t % 282) (t / 282)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 282 % 94) * 282) (x2Tab o (t / 282 / 94) (t % 282))) (x2Tab t3 (t / 282) (t % 282)))) 17008 8 chkC_10_d17008) (x2c_join _ 17016 17024 17600 (x2c_range_all (fun t => (!(pOK tl tl (t % 282) (t / 282)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 282 % 94) * 282) (x2Tab o (t / 282 / 94) (t % 282))) (x2Tab t3 (t / 282) (t % 282)))) 17016 8 chkC_10_d17016) (x2c_join _ 17024 17032 17600 (x2c_range_all (fun t => (!(pOK tl tl (t % 282) (t / 282)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 282 % 94) * 282) (x2Tab o (t / 282 / 94) (t % 282))) (x2Tab t3 (t / 282) (t % 282)))) 17024 8 chkC_10_d17024) (x2c_join _ 17032 17040 17600 (x2c_range_all (fun t => (!(pOK tl tl (t % 282) (t / 282)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 282 % 94) * 282) (x2Tab o (t / 282 / 94) (t % 282))) (x2Tab t3 (t / 282) (t % 282)))) 17032 8 chkC_10_d17032) (x2c_join _ 17040 17048 17600 (x2c_range_all (fun t => (!(pOK tl tl (t % 282) (t / 282)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 282 % 94) * 282) (x2Tab o (t / 282 / 94) (t % 282))) (x2Tab t3 (t / 282) (t % 282)))) 17040 8 chkC_10_d17040) (x2c_join _ 17048 17056 17600 (x2c_range_all (fun t => (!(pOK tl tl (t % 282) (t / 282)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 282 % 94) * 282) (x2Tab o (t / 282 / 94) (t % 282))) (x2Tab t3 (t / 282) (t % 282)))) 17048 8 chkC_10_d17048) (x2c_join _ 17056 17064 17600 (x2c_range_all (fun t => (!(pOK tl tl (t % 282) (t / 282)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 282 % 94) * 282) (x2Tab o (t / 282 / 94) (t % 282))) (x2Tab t3 (t / 282) (t % 282)))) 17056 8 chkC_10_d17056) (x2c_join _ 17064 17072 17600 (x2c_range_all (fun t => (!(pOK tl tl (t % 282) (t / 282)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 282 % 94) * 282) (x2Tab o (t / 282 / 94) (t % 282))) (x2Tab t3 (t / 282) (t % 282)))) 17064 8 chkC_10_d17064) (x2c_join _ 17072 17080 17600 (x2c_range_all (fun t => (!(pOK tl tl (t % 282) (t / 282)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 282 % 94) * 282) (x2Tab o (t / 282 / 94) (t % 282))) (x2Tab t3 (t / 282) (t % 282)))) 17072 8 chkC_10_d17072) (x2c_join _ 17080 17088 17600 (x2c_range_all (fun t => (!(pOK tl tl (t % 282) (t / 282)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 282 % 94) * 282) (x2Tab o (t / 282 / 94) (t % 282))) (x2Tab t3 (t / 282) (t % 282)))) 17080 8 chkC_10_d17080) (x2c_join _ 17088 17096 17600 (x2c_range_all (fun t => (!(pOK tl tl (t % 282) (t / 282)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 282 % 94) * 282) (x2Tab o (t / 282 / 94) (t % 282))) (x2Tab t3 (t / 282) (t % 282)))) 17088 8 chkC_10_d17088) (x2c_join _ 17096 17104 17600 (x2c_range_all (fun t => (!(pOK tl tl (t % 282) (t / 282)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 282 % 94) * 282) (x2Tab o (t / 282 / 94) (t % 282))) (x2Tab t3 (t / 282) (t % 282)))) 17096 8 chkC_10_d17096) (x2c_join _ 17104 17112 17600 (x2c_range_all (fun t => (!(pOK tl tl (t % 282) (t / 282)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 282 % 94) * 282) (x2Tab o (t / 282 / 94) (t % 282))) (x2Tab t3 (t / 282) (t % 282)))) 17104 8 chkC_10_d17104) (x2c_join _ 17112 17120 17600 (x2c_range_all (fun t => (!(pOK tl tl (t % 282) (t / 282)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 282 % 94) * 282) (x2Tab o (t / 282 / 94) (t % 282))) (x2Tab t3 (t / 282) (t % 282)))) 17112 8 chkC_10_d17112) (x2c_join _ 17120 17128 17600 (x2c_range_all (fun t => (!(pOK tl tl (t % 282) (t / 282)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 282 % 94) * 282) (x2Tab o (t / 282 / 94) (t % 282))) (x2Tab t3 (t / 282) (t % 282)))) 17120 8 chkC_10_d17120) (x2c_join _ 17128 17136 17600 (x2c_range_all (fun t => (!(pOK tl tl (t % 282) (t / 282)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 282 % 94) * 282) (x2Tab o (t / 282 / 94) (t % 282))) (x2Tab t3 (t / 282) (t % 282)))) 17128 8 chkC_10_d17128) (x2c_join _ 17136 17144 17600 (x2c_range_all (fun t => (!(pOK tl tl (t % 282) (t / 282)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 282 % 94) * 282) (x2Tab o (t / 282 / 94) (t % 282))) (x2Tab t3 (t / 282) (t % 282)))) 17136 8 chkC_10_d17136) (x2c_join _ 17144 17152 17600 (x2c_range_all (fun t => (!(pOK tl tl (t % 282) (t / 282)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 282 % 94) * 282) (x2Tab o (t / 282 / 94) (t % 282))) (x2Tab t3 (t / 282) (t % 282)))) 17144 8 chkC_10_d17144) (x2c_join _ 17152 17160 17600 (x2c_range_all (fun t => (!(pOK tl tl (t % 282) (t / 282)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 282 % 94) * 282) (x2Tab o (t / 282 / 94) (t % 282))) (x2Tab t3 (t / 282) (t % 282)))) 17152 8 chkC_10_d17152) (x2c_join _ 17160 17168 17600 (x2c_range_all (fun t => (!(pOK tl tl (t % 282) (t / 282)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 282 % 94) * 282) (x2Tab o (t / 282 / 94) (t % 282))) (x2Tab t3 (t / 282) (t % 282)))) 17160 8 chkC_10_d17160) (x2c_join _ 17168 17176 17600 (x2c_range_all (fun t => (!(pOK tl tl (t % 282) (t / 282)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 282 % 94) * 282) (x2Tab o (t / 282 / 94) (t % 282))) (x2Tab t3 (t / 282) (t % 282)))) 17168 8 chkC_10_d17168) (x2c_join _ 17176 17184 17600 (x2c_range_all (fun t => (!(pOK tl tl (t % 282) (t / 282)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 282 % 94) * 282) (x2Tab o (t / 282 / 94) (t % 282))) (x2Tab t3 (t / 282) (t % 282)))) 17176 8 chkC_10_d17176) (x2c_join _ 17184 17192 17600 (x2c_range_all (fun t => (!(pOK tl tl (t % 282) (t / 282)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 282 % 94) * 282) (x2Tab o (t / 282 / 94) (t % 282))) (x2Tab t3 (t / 282) (t % 282)))) 17184 8 chkC_10_d17184) (x2c_join _ 17192 17200 17600 (x2c_range_all (fun t => (!(pOK tl tl (t % 282) (t / 282)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 282 % 94) * 282) (x2Tab o (t / 282 / 94) (t % 282))) (x2Tab t3 (t / 282) (t % 282)))) 17192 8 chkC_10_d17192) (x2c_join _ 17200 17208 17600 (x2c_range_all (fun t => (!(pOK tl tl (t % 282) (t / 282)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 282 % 94) * 282) (x2Tab o (t / 282 / 94) (t % 282))) (x2Tab t3 (t / 282) (t % 282)))) 17200 8 chkC_10_d17200) (x2c_join _ 17208 17216 17600 (x2c_range_all (fun t => (!(pOK tl tl (t % 282) (t / 282)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 282 % 94) * 282) (x2Tab o (t / 282 / 94) (t % 282))) (x2Tab t3 (t / 282) (t % 282)))) 17208 8 chkC_10_d17208) (x2c_join _ 17216 17224 17600 (x2c_range_all (fun t => (!(pOK tl tl (t % 282) (t / 282)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 282 % 94) * 282) (x2Tab o (t / 282 / 94) (t % 282))) (x2Tab t3 (t / 282) (t % 282)))) 17216 8 chkC_10_d17216) (x2c_join _ 17224 17232 17600 (x2c_range_all (fun t => (!(pOK tl tl (t % 282) (t / 282)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 282 % 94) * 282) (x2Tab o (t / 282 / 94) (t % 282))) (x2Tab t3 (t / 282) (t % 282)))) 17224 8 chkC_10_d17224) (x2c_join _ 17232 17240 17600 (x2c_range_all (fun t => (!(pOK tl tl (t % 282) (t / 282)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 282 % 94) * 282) (x2Tab o (t / 282 / 94) (t % 282))) (x2Tab t3 (t / 282) (t % 282)))) 17232 8 chkC_10_d17232) (x2c_join _ 17240 17248 17600 (x2c_range_all (fun t => (!(pOK tl tl (t % 282) (t / 282)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 282 % 94) * 282) (x2Tab o (t / 282 / 94) (t % 282))) (x2Tab t3 (t / 282) (t % 282)))) 17240 8 chkC_10_d17240) (x2c_join _ 17248 17256 17600 (x2c_range_all (fun t => (!(pOK tl tl (t % 282) (t / 282)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 282 % 94) * 282) (x2Tab o (t / 282 / 94) (t % 282))) (x2Tab t3 (t / 282) (t % 282)))) 17248 8 chkC_10_d17248) (x2c_join _ 17256 17264 17600 (x2c_range_all (fun t => (!(pOK tl tl (t % 282) (t / 282)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 282 % 94) * 282) (x2Tab o (t / 282 / 94) (t % 282))) (x2Tab t3 (t / 282) (t % 282)))) 17256 8 chkC_10_d17256) (x2c_join _ 17264 17272 17600 (x2c_range_all (fun t => (!(pOK tl tl (t % 282) (t / 282)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 282 % 94) * 282) (x2Tab o (t / 282 / 94) (t % 282))) (x2Tab t3 (t / 282) (t % 282)))) 17264 8 chkC_10_d17264) (x2c_join _ 17272 17280 17600 (x2c_range_all (fun t => (!(pOK tl tl (t % 282) (t / 282)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 282 % 94) * 282) (x2Tab o (t / 282 / 94) (t % 282))) (x2Tab t3 (t / 282) (t % 282)))) 17272 8 chkC_10_d17272) (x2c_join _ 17280 17288 17600 (x2c_range_all (fun t => (!(pOK tl tl (t % 282) (t / 282)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 282 % 94) * 282) (x2Tab o (t / 282 / 94) (t % 282))) (x2Tab t3 (t / 282) (t % 282)))) 17280 8 chkC_10_d17280) (x2c_join _ 17288 17296 17600 (x2c_range_all (fun t => (!(pOK tl tl (t % 282) (t / 282)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 282 % 94) * 282) (x2Tab o (t / 282 / 94) (t % 282))) (x2Tab t3 (t / 282) (t % 282)))) 17288 8 chkC_10_d17288) (x2c_join _ 17296 17304 17600 (x2c_range_all (fun t => (!(pOK tl tl (t % 282) (t / 282)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 282 % 94) * 282) (x2Tab o (t / 282 / 94) (t % 282))) (x2Tab t3 (t / 282) (t % 282)))) 17296 8 chkC_10_d17296) (x2c_join _ 17304 17312 17600 (x2c_range_all (fun t => (!(pOK tl tl (t % 282) (t / 282)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 282 % 94) * 282) (x2Tab o (t / 282 / 94) (t % 282))) (x2Tab t3 (t / 282) (t % 282)))) 17304 8 chkC_10_d17304) (x2c_join _ 17312 17320 17600 (x2c_range_all (fun t => (!(pOK tl tl (t % 282) (t / 282)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 282 % 94) * 282) (x2Tab o (t / 282 / 94) (t % 282))) (x2Tab t3 (t / 282) (t % 282)))) 17312 8 chkC_10_d17312) (x2c_join _ 17320 17328 17600 (x2c_range_all (fun t => (!(pOK tl tl (t % 282) (t / 282)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 282 % 94) * 282) (x2Tab o (t / 282 / 94) (t % 282))) (x2Tab t3 (t / 282) (t % 282)))) 17320 8 chkC_10_d17320) (x2c_join _ 17328 17336 17600 (x2c_range_all (fun t => (!(pOK tl tl (t % 282) (t / 282)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 282 % 94) * 282) (x2Tab o (t / 282 / 94) (t % 282))) (x2Tab t3 (t / 282) (t % 282)))) 17328 8 chkC_10_d17328) (x2c_join _ 17336 17344 17600 (x2c_range_all (fun t => (!(pOK tl tl (t % 282) (t / 282)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 282 % 94) * 282) (x2Tab o (t / 282 / 94) (t % 282))) (x2Tab t3 (t / 282) (t % 282)))) 17336 8 chkC_10_d17336) (x2c_join _ 17344 17352 17600 (x2c_range_all (fun t => (!(pOK tl tl (t % 282) (t / 282)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 282 % 94) * 282) (x2Tab o (t / 282 / 94) (t % 282))) (x2Tab t3 (t / 282) (t % 282)))) 17344 8 chkC_10_d17344) (x2c_join _ 17352 17360 17600 (x2c_range_all (fun t => (!(pOK tl tl (t % 282) (t / 282)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 282 % 94) * 282) (x2Tab o (t / 282 / 94) (t % 282))) (x2Tab t3 (t / 282) (t % 282)))) 17352 8 chkC_10_d17352) (x2c_join _ 17360 17368 17600 (x2c_range_all (fun t => (!(pOK tl tl (t % 282) (t / 282)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 282 % 94) * 282) (x2Tab o (t / 282 / 94) (t % 282))) (x2Tab t3 (t / 282) (t % 282)))) 17360 8 chkC_10_d17360) (x2c_join _ 17368 17376 17600 (x2c_range_all (fun t => (!(pOK tl tl (t % 282) (t / 282)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 282 % 94) * 282) (x2Tab o (t / 282 / 94) (t % 282))) (x2Tab t3 (t / 282) (t % 282)))) 17368 8 chkC_10_d17368) (x2c_join _ 17376 17384 17600 (x2c_range_all (fun t => (!(pOK tl tl (t % 282) (t / 282)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 282 % 94) * 282) (x2Tab o (t / 282 / 94) (t % 282))) (x2Tab t3 (t / 282) (t % 282)))) 17376 8 chkC_10_d17376) (x2c_join _ 17384 17392 17600 (x2c_range_all (fun t => (!(pOK tl tl (t % 282) (t / 282)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 282 % 94) * 282) (x2Tab o (t / 282 / 94) (t % 282))) (x2Tab t3 (t / 282) (t % 282)))) 17384 8 chkC_10_d17384) (x2c_join _ 17392 17400 17600 (x2c_range_all (fun t => (!(pOK tl tl (t % 282) (t / 282)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 282 % 94) * 282) (x2Tab o (t / 282 / 94) (t % 282))) (x2Tab t3 (t / 282) (t % 282)))) 17392 8 chkC_10_d17392) (x2c_join _ 17400 17408 17600 (x2c_range_all (fun t => (!(pOK tl tl (t % 282) (t / 282)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 282 % 94) * 282) (x2Tab o (t / 282 / 94) (t % 282))) (x2Tab t3 (t / 282) (t % 282)))) 17400 8 chkC_10_d17400) (x2c_join _ 17408 17416 17600 (x2c_range_all (fun t => (!(pOK tl tl (t % 282) (t / 282)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 282 % 94) * 282) (x2Tab o (t / 282 / 94) (t % 282))) (x2Tab t3 (t / 282) (t % 282)))) 17408 8 chkC_10_d17408) (x2c_join _ 17416 17424 17600 (x2c_range_all (fun t => (!(pOK tl tl (t % 282) (t / 282)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 282 % 94) * 282) (x2Tab o (t / 282 / 94) (t % 282))) (x2Tab t3 (t / 282) (t % 282)))) 17416 8 chkC_10_d17416) (x2c_join _ 17424 17432 17600 (x2c_range_all (fun t => (!(pOK tl tl (t % 282) (t / 282)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 282 % 94) * 282) (x2Tab o (t / 282 / 94) (t % 282))) (x2Tab t3 (t / 282) (t % 282)))) 17424 8 chkC_10_d17424) (x2c_join _ 17432 17440 17600 (x2c_range_all (fun t => (!(pOK tl tl (t % 282) (t / 282)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 282 % 94) * 282) (x2Tab o (t / 282 / 94) (t % 282))) (x2Tab t3 (t / 282) (t % 282)))) 17432 8 chkC_10_d17432) (x2c_join _ 17440 17448 17600 (x2c_range_all (fun t => (!(pOK tl tl (t % 282) (t / 282)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 282 % 94) * 282) (x2Tab o (t / 282 / 94) (t % 282))) (x2Tab t3 (t / 282) (t % 282)))) 17440 8 chkC_10_d17440) (x2c_join _ 17448 17456 17600 (x2c_range_all (fun t => (!(pOK tl tl (t % 282) (t / 282)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 282 % 94) * 282) (x2Tab o (t / 282 / 94) (t % 282))) (x2Tab t3 (t / 282) (t % 282)))) 17448 8 chkC_10_d17448) (x2c_join _ 17456 17464 17600 (x2c_range_all (fun t => (!(pOK tl tl (t % 282) (t / 282)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 282 % 94) * 282) (x2Tab o (t / 282 / 94) (t % 282))) (x2Tab t3 (t / 282) (t % 282)))) 17456 8 chkC_10_d17456) (x2c_join _ 17464 17472 17600 (x2c_range_all (fun t => (!(pOK tl tl (t % 282) (t / 282)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 282 % 94) * 282) (x2Tab o (t / 282 / 94) (t % 282))) (x2Tab t3 (t / 282) (t % 282)))) 17464 8 chkC_10_d17464) (x2c_join _ 17472 17480 17600 (x2c_range_all (fun t => (!(pOK tl tl (t % 282) (t / 282)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 282 % 94) * 282) (x2Tab o (t / 282 / 94) (t % 282))) (x2Tab t3 (t / 282) (t % 282)))) 17472 8 chkC_10_d17472) (x2c_join _ 17480 17488 17600 (x2c_range_all (fun t => (!(pOK tl tl (t % 282) (t / 282)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 282 % 94) * 282) (x2Tab o (t / 282 / 94) (t % 282))) (x2Tab t3 (t / 282) (t % 282)))) 17480 8 chkC_10_d17480) (x2c_join _ 17488 17496 17600 (x2c_range_all (fun t => (!(pOK tl tl (t % 282) (t / 282)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 282 % 94) * 282) (x2Tab o (t / 282 / 94) (t % 282))) (x2Tab t3 (t / 282) (t % 282)))) 17488 8 chkC_10_d17488) (x2c_join _ 17496 17504 17600 (x2c_range_all (fun t => (!(pOK tl tl (t % 282) (t / 282)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 282 % 94) * 282) (x2Tab o (t / 282 / 94) (t % 282))) (x2Tab t3 (t / 282) (t % 282)))) 17496 8 chkC_10_d17496) (x2c_join _ 17504 17512 17600 (x2c_range_all (fun t => (!(pOK tl tl (t % 282) (t / 282)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 282 % 94) * 282) (x2Tab o (t / 282 / 94) (t % 282))) (x2Tab t3 (t / 282) (t % 282)))) 17504 8 chkC_10_d17504) (x2c_join _ 17512 17520 17600 (x2c_range_all (fun t => (!(pOK tl tl (t % 282) (t / 282)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 282 % 94) * 282) (x2Tab o (t / 282 / 94) (t % 282))) (x2Tab t3 (t / 282) (t % 282)))) 17512 8 chkC_10_d17512) (x2c_join _ 17520 17528 17600 (x2c_range_all (fun t => (!(pOK tl tl (t % 282) (t / 282)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 282 % 94) * 282) (x2Tab o (t / 282 / 94) (t % 282))) (x2Tab t3 (t / 282) (t % 282)))) 17520 8 chkC_10_d17520) (x2c_join _ 17528 17536 17600 (x2c_range_all (fun t => (!(pOK tl tl (t % 282) (t / 282)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 282 % 94) * 282) (x2Tab o (t / 282 / 94) (t % 282))) (x2Tab t3 (t / 282) (t % 282)))) 17528 8 chkC_10_d17528) (x2c_join _ 17536 17544 17600 (x2c_range_all (fun t => (!(pOK tl tl (t % 282) (t / 282)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 282 % 94) * 282) (x2Tab o (t / 282 / 94) (t % 282))) (x2Tab t3 (t / 282) (t % 282)))) 17536 8 chkC_10_d17536) (x2c_join _ 17544 17552 17600 (x2c_range_all (fun t => (!(pOK tl tl (t % 282) (t / 282)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 282 % 94) * 282) (x2Tab o (t / 282 / 94) (t % 282))) (x2Tab t3 (t / 282) (t % 282)))) 17544 8 chkC_10_d17544) (x2c_join _ 17552 17560 17600 (x2c_range_all (fun t => (!(pOK tl tl (t % 282) (t / 282)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 282 % 94) * 282) (x2Tab o (t / 282 / 94) (t % 282))) (x2Tab t3 (t / 282) (t % 282)))) 17552 8 chkC_10_d17552) (x2c_join _ 17560 17568 17600 (x2c_range_all (fun t => (!(pOK tl tl (t % 282) (t / 282)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 282 % 94) * 282) (x2Tab o (t / 282 / 94) (t % 282))) (x2Tab t3 (t / 282) (t % 282)))) 17560 8 chkC_10_d17560) (x2c_join _ 17568 17576 17600 (x2c_range_all (fun t => (!(pOK tl tl (t % 282) (t / 282)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 282 % 94) * 282) (x2Tab o (t / 282 / 94) (t % 282))) (x2Tab t3 (t / 282) (t % 282)))) 17568 8 chkC_10_d17568) (x2c_join _ 17576 17584 17600 (x2c_range_all (fun t => (!(pOK tl tl (t % 282) (t / 282)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 282 % 94) * 282) (x2Tab o (t / 282 / 94) (t % 282))) (x2Tab t3 (t / 282) (t % 282)))) 17576 8 chkC_10_d17576) (x2c_join _ 17584 17592 17600 (x2c_range_all (fun t => (!(pOK tl tl (t % 282) (t / 282)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 282 % 94) * 282) (x2Tab o (t / 282 / 94) (t % 282))) (x2Tab t3 (t / 282) (t % 282)))) 17584 8 chkC_10_d17584) (x2c_range_all (fun t => (!(pOK tl tl (t % 282) (t / 282)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 282 % 94) * 282) (x2Tab o (t / 282 / 94) (t % 282))) (x2Tab t3 (t / 282) (t % 282)))) 17592 8 chkC_10_d17592))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))


end ThreeCopyQutritWerner.X2.CoreS1g
