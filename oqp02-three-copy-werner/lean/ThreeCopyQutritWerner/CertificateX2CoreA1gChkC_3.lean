module

public import ThreeCopyQutritWerner.CertificateX2CoreA1gT3
public import ThreeCopyQutritWerner.CertificateX2Trans
public import ThreeCopyQutritWerner.CertificateX2CoreBatchGen
public import ThreeCopyQutritWerner.CertificateX2CoreBatchFlat

@[expose] public section


/-! Batched core A1g: axis-0 stage, selected pairs, flat indices 4800..6399. -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option exponentiation.threshold 1000000

namespace ThreeCopyQutritWerner.X2.CoreA1g
open ThreeCopyQutritWerner ThreeCopyQutritWerner.X2

theorem chkC_3_d4800 : (List.range' 4800 8).all (fun t => (!(pOK tl tl (t % 231) (t / 231)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 231 % 77) * 282) (x2Tab o (t / 231 / 77) (t % 231))) (x2Tab t3 (t / 231) (t % 231)))) = true := by
  decide +kernel

theorem chkC_3_d4808 : (List.range' 4808 8).all (fun t => (!(pOK tl tl (t % 231) (t / 231)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 231 % 77) * 282) (x2Tab o (t / 231 / 77) (t % 231))) (x2Tab t3 (t / 231) (t % 231)))) = true := by
  decide +kernel

theorem chkC_3_d4816 : (List.range' 4816 8).all (fun t => (!(pOK tl tl (t % 231) (t / 231)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 231 % 77) * 282) (x2Tab o (t / 231 / 77) (t % 231))) (x2Tab t3 (t / 231) (t % 231)))) = true := by
  decide +kernel

theorem chkC_3_d4824 : (List.range' 4824 8).all (fun t => (!(pOK tl tl (t % 231) (t / 231)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 231 % 77) * 282) (x2Tab o (t / 231 / 77) (t % 231))) (x2Tab t3 (t / 231) (t % 231)))) = true := by
  decide +kernel

theorem chkC_3_d4832 : (List.range' 4832 8).all (fun t => (!(pOK tl tl (t % 231) (t / 231)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 231 % 77) * 282) (x2Tab o (t / 231 / 77) (t % 231))) (x2Tab t3 (t / 231) (t % 231)))) = true := by
  decide +kernel

theorem chkC_3_d4840 : (List.range' 4840 8).all (fun t => (!(pOK tl tl (t % 231) (t / 231)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 231 % 77) * 282) (x2Tab o (t / 231 / 77) (t % 231))) (x2Tab t3 (t / 231) (t % 231)))) = true := by
  decide +kernel

theorem chkC_3_d4848 : (List.range' 4848 8).all (fun t => (!(pOK tl tl (t % 231) (t / 231)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 231 % 77) * 282) (x2Tab o (t / 231 / 77) (t % 231))) (x2Tab t3 (t / 231) (t % 231)))) = true := by
  decide +kernel

theorem chkC_3_d4856 : (List.range' 4856 8).all (fun t => (!(pOK tl tl (t % 231) (t / 231)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 231 % 77) * 282) (x2Tab o (t / 231 / 77) (t % 231))) (x2Tab t3 (t / 231) (t % 231)))) = true := by
  decide +kernel

theorem chkC_3_d4864 : (List.range' 4864 8).all (fun t => (!(pOK tl tl (t % 231) (t / 231)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 231 % 77) * 282) (x2Tab o (t / 231 / 77) (t % 231))) (x2Tab t3 (t / 231) (t % 231)))) = true := by
  decide +kernel

theorem chkC_3_d4872 : (List.range' 4872 8).all (fun t => (!(pOK tl tl (t % 231) (t / 231)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 231 % 77) * 282) (x2Tab o (t / 231 / 77) (t % 231))) (x2Tab t3 (t / 231) (t % 231)))) = true := by
  decide +kernel

theorem chkC_3_d4880 : (List.range' 4880 8).all (fun t => (!(pOK tl tl (t % 231) (t / 231)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 231 % 77) * 282) (x2Tab o (t / 231 / 77) (t % 231))) (x2Tab t3 (t / 231) (t % 231)))) = true := by
  decide +kernel

theorem chkC_3_d4888 : (List.range' 4888 8).all (fun t => (!(pOK tl tl (t % 231) (t / 231)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 231 % 77) * 282) (x2Tab o (t / 231 / 77) (t % 231))) (x2Tab t3 (t / 231) (t % 231)))) = true := by
  decide +kernel

theorem chkC_3_d4896 : (List.range' 4896 8).all (fun t => (!(pOK tl tl (t % 231) (t / 231)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 231 % 77) * 282) (x2Tab o (t / 231 / 77) (t % 231))) (x2Tab t3 (t / 231) (t % 231)))) = true := by
  decide +kernel

theorem chkC_3_d4904 : (List.range' 4904 8).all (fun t => (!(pOK tl tl (t % 231) (t / 231)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 231 % 77) * 282) (x2Tab o (t / 231 / 77) (t % 231))) (x2Tab t3 (t / 231) (t % 231)))) = true := by
  decide +kernel

theorem chkC_3_d4912 : (List.range' 4912 8).all (fun t => (!(pOK tl tl (t % 231) (t / 231)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 231 % 77) * 282) (x2Tab o (t / 231 / 77) (t % 231))) (x2Tab t3 (t / 231) (t % 231)))) = true := by
  decide +kernel

theorem chkC_3_d4920 : (List.range' 4920 8).all (fun t => (!(pOK tl tl (t % 231) (t / 231)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 231 % 77) * 282) (x2Tab o (t / 231 / 77) (t % 231))) (x2Tab t3 (t / 231) (t % 231)))) = true := by
  decide +kernel

theorem chkC_3_d4928 : (List.range' 4928 8).all (fun t => (!(pOK tl tl (t % 231) (t / 231)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 231 % 77) * 282) (x2Tab o (t / 231 / 77) (t % 231))) (x2Tab t3 (t / 231) (t % 231)))) = true := by
  decide +kernel

theorem chkC_3_d4936 : (List.range' 4936 8).all (fun t => (!(pOK tl tl (t % 231) (t / 231)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 231 % 77) * 282) (x2Tab o (t / 231 / 77) (t % 231))) (x2Tab t3 (t / 231) (t % 231)))) = true := by
  decide +kernel

theorem chkC_3_d4944 : (List.range' 4944 8).all (fun t => (!(pOK tl tl (t % 231) (t / 231)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 231 % 77) * 282) (x2Tab o (t / 231 / 77) (t % 231))) (x2Tab t3 (t / 231) (t % 231)))) = true := by
  decide +kernel

theorem chkC_3_d4952 : (List.range' 4952 8).all (fun t => (!(pOK tl tl (t % 231) (t / 231)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 231 % 77) * 282) (x2Tab o (t / 231 / 77) (t % 231))) (x2Tab t3 (t / 231) (t % 231)))) = true := by
  decide +kernel

theorem chkC_3_d4960 : (List.range' 4960 8).all (fun t => (!(pOK tl tl (t % 231) (t / 231)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 231 % 77) * 282) (x2Tab o (t / 231 / 77) (t % 231))) (x2Tab t3 (t / 231) (t % 231)))) = true := by
  decide +kernel

theorem chkC_3_d4968 : (List.range' 4968 8).all (fun t => (!(pOK tl tl (t % 231) (t / 231)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 231 % 77) * 282) (x2Tab o (t / 231 / 77) (t % 231))) (x2Tab t3 (t / 231) (t % 231)))) = true := by
  decide +kernel

theorem chkC_3_d4976 : (List.range' 4976 8).all (fun t => (!(pOK tl tl (t % 231) (t / 231)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 231 % 77) * 282) (x2Tab o (t / 231 / 77) (t % 231))) (x2Tab t3 (t / 231) (t % 231)))) = true := by
  decide +kernel

theorem chkC_3_d4984 : (List.range' 4984 8).all (fun t => (!(pOK tl tl (t % 231) (t / 231)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 231 % 77) * 282) (x2Tab o (t / 231 / 77) (t % 231))) (x2Tab t3 (t / 231) (t % 231)))) = true := by
  decide +kernel

theorem chkC_3_d4992 : (List.range' 4992 8).all (fun t => (!(pOK tl tl (t % 231) (t / 231)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 231 % 77) * 282) (x2Tab o (t / 231 / 77) (t % 231))) (x2Tab t3 (t / 231) (t % 231)))) = true := by
  decide +kernel

theorem chkC_3_d5000 : (List.range' 5000 8).all (fun t => (!(pOK tl tl (t % 231) (t / 231)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 231 % 77) * 282) (x2Tab o (t / 231 / 77) (t % 231))) (x2Tab t3 (t / 231) (t % 231)))) = true := by
  decide +kernel

theorem chkC_3_d5008 : (List.range' 5008 8).all (fun t => (!(pOK tl tl (t % 231) (t / 231)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 231 % 77) * 282) (x2Tab o (t / 231 / 77) (t % 231))) (x2Tab t3 (t / 231) (t % 231)))) = true := by
  decide +kernel

theorem chkC_3_d5016 : (List.range' 5016 8).all (fun t => (!(pOK tl tl (t % 231) (t / 231)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 231 % 77) * 282) (x2Tab o (t / 231 / 77) (t % 231))) (x2Tab t3 (t / 231) (t % 231)))) = true := by
  decide +kernel

theorem chkC_3_d5024 : (List.range' 5024 8).all (fun t => (!(pOK tl tl (t % 231) (t / 231)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 231 % 77) * 282) (x2Tab o (t / 231 / 77) (t % 231))) (x2Tab t3 (t / 231) (t % 231)))) = true := by
  decide +kernel

theorem chkC_3_d5032 : (List.range' 5032 8).all (fun t => (!(pOK tl tl (t % 231) (t / 231)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 231 % 77) * 282) (x2Tab o (t / 231 / 77) (t % 231))) (x2Tab t3 (t / 231) (t % 231)))) = true := by
  decide +kernel

theorem chkC_3_d5040 : (List.range' 5040 8).all (fun t => (!(pOK tl tl (t % 231) (t / 231)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 231 % 77) * 282) (x2Tab o (t / 231 / 77) (t % 231))) (x2Tab t3 (t / 231) (t % 231)))) = true := by
  decide +kernel

theorem chkC_3_d5048 : (List.range' 5048 8).all (fun t => (!(pOK tl tl (t % 231) (t / 231)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 231 % 77) * 282) (x2Tab o (t / 231 / 77) (t % 231))) (x2Tab t3 (t / 231) (t % 231)))) = true := by
  decide +kernel

theorem chkC_3_d5056 : (List.range' 5056 8).all (fun t => (!(pOK tl tl (t % 231) (t / 231)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 231 % 77) * 282) (x2Tab o (t / 231 / 77) (t % 231))) (x2Tab t3 (t / 231) (t % 231)))) = true := by
  decide +kernel

theorem chkC_3_d5064 : (List.range' 5064 8).all (fun t => (!(pOK tl tl (t % 231) (t / 231)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 231 % 77) * 282) (x2Tab o (t / 231 / 77) (t % 231))) (x2Tab t3 (t / 231) (t % 231)))) = true := by
  decide +kernel

theorem chkC_3_d5072 : (List.range' 5072 8).all (fun t => (!(pOK tl tl (t % 231) (t / 231)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 231 % 77) * 282) (x2Tab o (t / 231 / 77) (t % 231))) (x2Tab t3 (t / 231) (t % 231)))) = true := by
  decide +kernel

theorem chkC_3_d5080 : (List.range' 5080 8).all (fun t => (!(pOK tl tl (t % 231) (t / 231)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 231 % 77) * 282) (x2Tab o (t / 231 / 77) (t % 231))) (x2Tab t3 (t / 231) (t % 231)))) = true := by
  decide +kernel

theorem chkC_3_d5088 : (List.range' 5088 8).all (fun t => (!(pOK tl tl (t % 231) (t / 231)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 231 % 77) * 282) (x2Tab o (t / 231 / 77) (t % 231))) (x2Tab t3 (t / 231) (t % 231)))) = true := by
  decide +kernel

theorem chkC_3_d5096 : (List.range' 5096 8).all (fun t => (!(pOK tl tl (t % 231) (t / 231)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 231 % 77) * 282) (x2Tab o (t / 231 / 77) (t % 231))) (x2Tab t3 (t / 231) (t % 231)))) = true := by
  decide +kernel

theorem chkC_3_d5104 : (List.range' 5104 8).all (fun t => (!(pOK tl tl (t % 231) (t / 231)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 231 % 77) * 282) (x2Tab o (t / 231 / 77) (t % 231))) (x2Tab t3 (t / 231) (t % 231)))) = true := by
  decide +kernel

theorem chkC_3_d5112 : (List.range' 5112 8).all (fun t => (!(pOK tl tl (t % 231) (t / 231)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 231 % 77) * 282) (x2Tab o (t / 231 / 77) (t % 231))) (x2Tab t3 (t / 231) (t % 231)))) = true := by
  decide +kernel

theorem chkC_3_d5120 : (List.range' 5120 8).all (fun t => (!(pOK tl tl (t % 231) (t / 231)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 231 % 77) * 282) (x2Tab o (t / 231 / 77) (t % 231))) (x2Tab t3 (t / 231) (t % 231)))) = true := by
  decide +kernel

theorem chkC_3_d5128 : (List.range' 5128 8).all (fun t => (!(pOK tl tl (t % 231) (t / 231)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 231 % 77) * 282) (x2Tab o (t / 231 / 77) (t % 231))) (x2Tab t3 (t / 231) (t % 231)))) = true := by
  decide +kernel

theorem chkC_3_d5136 : (List.range' 5136 8).all (fun t => (!(pOK tl tl (t % 231) (t / 231)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 231 % 77) * 282) (x2Tab o (t / 231 / 77) (t % 231))) (x2Tab t3 (t / 231) (t % 231)))) = true := by
  decide +kernel

theorem chkC_3_d5144 : (List.range' 5144 8).all (fun t => (!(pOK tl tl (t % 231) (t / 231)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 231 % 77) * 282) (x2Tab o (t / 231 / 77) (t % 231))) (x2Tab t3 (t / 231) (t % 231)))) = true := by
  decide +kernel

theorem chkC_3_d5152 : (List.range' 5152 8).all (fun t => (!(pOK tl tl (t % 231) (t / 231)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 231 % 77) * 282) (x2Tab o (t / 231 / 77) (t % 231))) (x2Tab t3 (t / 231) (t % 231)))) = true := by
  decide +kernel

theorem chkC_3_d5160 : (List.range' 5160 8).all (fun t => (!(pOK tl tl (t % 231) (t / 231)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 231 % 77) * 282) (x2Tab o (t / 231 / 77) (t % 231))) (x2Tab t3 (t / 231) (t % 231)))) = true := by
  decide +kernel

theorem chkC_3_d5168 : (List.range' 5168 8).all (fun t => (!(pOK tl tl (t % 231) (t / 231)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 231 % 77) * 282) (x2Tab o (t / 231 / 77) (t % 231))) (x2Tab t3 (t / 231) (t % 231)))) = true := by
  decide +kernel

theorem chkC_3_d5176 : (List.range' 5176 8).all (fun t => (!(pOK tl tl (t % 231) (t / 231)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 231 % 77) * 282) (x2Tab o (t / 231 / 77) (t % 231))) (x2Tab t3 (t / 231) (t % 231)))) = true := by
  decide +kernel

theorem chkC_3_d5184 : (List.range' 5184 8).all (fun t => (!(pOK tl tl (t % 231) (t / 231)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 231 % 77) * 282) (x2Tab o (t / 231 / 77) (t % 231))) (x2Tab t3 (t / 231) (t % 231)))) = true := by
  decide +kernel

theorem chkC_3_d5192 : (List.range' 5192 8).all (fun t => (!(pOK tl tl (t % 231) (t / 231)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 231 % 77) * 282) (x2Tab o (t / 231 / 77) (t % 231))) (x2Tab t3 (t / 231) (t % 231)))) = true := by
  decide +kernel

theorem chkC_3_d5200 : (List.range' 5200 8).all (fun t => (!(pOK tl tl (t % 231) (t / 231)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 231 % 77) * 282) (x2Tab o (t / 231 / 77) (t % 231))) (x2Tab t3 (t / 231) (t % 231)))) = true := by
  decide +kernel

theorem chkC_3_d5208 : (List.range' 5208 8).all (fun t => (!(pOK tl tl (t % 231) (t / 231)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 231 % 77) * 282) (x2Tab o (t / 231 / 77) (t % 231))) (x2Tab t3 (t / 231) (t % 231)))) = true := by
  decide +kernel

theorem chkC_3_d5216 : (List.range' 5216 8).all (fun t => (!(pOK tl tl (t % 231) (t / 231)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 231 % 77) * 282) (x2Tab o (t / 231 / 77) (t % 231))) (x2Tab t3 (t / 231) (t % 231)))) = true := by
  decide +kernel

theorem chkC_3_d5224 : (List.range' 5224 8).all (fun t => (!(pOK tl tl (t % 231) (t / 231)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 231 % 77) * 282) (x2Tab o (t / 231 / 77) (t % 231))) (x2Tab t3 (t / 231) (t % 231)))) = true := by
  decide +kernel

theorem chkC_3_d5232 : (List.range' 5232 8).all (fun t => (!(pOK tl tl (t % 231) (t / 231)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 231 % 77) * 282) (x2Tab o (t / 231 / 77) (t % 231))) (x2Tab t3 (t / 231) (t % 231)))) = true := by
  decide +kernel

theorem chkC_3_d5240 : (List.range' 5240 8).all (fun t => (!(pOK tl tl (t % 231) (t / 231)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 231 % 77) * 282) (x2Tab o (t / 231 / 77) (t % 231))) (x2Tab t3 (t / 231) (t % 231)))) = true := by
  decide +kernel

theorem chkC_3_d5248 : (List.range' 5248 8).all (fun t => (!(pOK tl tl (t % 231) (t / 231)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 231 % 77) * 282) (x2Tab o (t / 231 / 77) (t % 231))) (x2Tab t3 (t / 231) (t % 231)))) = true := by
  decide +kernel

theorem chkC_3_d5256 : (List.range' 5256 8).all (fun t => (!(pOK tl tl (t % 231) (t / 231)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 231 % 77) * 282) (x2Tab o (t / 231 / 77) (t % 231))) (x2Tab t3 (t / 231) (t % 231)))) = true := by
  decide +kernel

theorem chkC_3_d5264 : (List.range' 5264 8).all (fun t => (!(pOK tl tl (t % 231) (t / 231)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 231 % 77) * 282) (x2Tab o (t / 231 / 77) (t % 231))) (x2Tab t3 (t / 231) (t % 231)))) = true := by
  decide +kernel

theorem chkC_3_d5272 : (List.range' 5272 8).all (fun t => (!(pOK tl tl (t % 231) (t / 231)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 231 % 77) * 282) (x2Tab o (t / 231 / 77) (t % 231))) (x2Tab t3 (t / 231) (t % 231)))) = true := by
  decide +kernel

theorem chkC_3_d5280 : (List.range' 5280 8).all (fun t => (!(pOK tl tl (t % 231) (t / 231)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 231 % 77) * 282) (x2Tab o (t / 231 / 77) (t % 231))) (x2Tab t3 (t / 231) (t % 231)))) = true := by
  decide +kernel

theorem chkC_3_d5288 : (List.range' 5288 8).all (fun t => (!(pOK tl tl (t % 231) (t / 231)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 231 % 77) * 282) (x2Tab o (t / 231 / 77) (t % 231))) (x2Tab t3 (t / 231) (t % 231)))) = true := by
  decide +kernel

theorem chkC_3_d5296 : (List.range' 5296 8).all (fun t => (!(pOK tl tl (t % 231) (t / 231)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 231 % 77) * 282) (x2Tab o (t / 231 / 77) (t % 231))) (x2Tab t3 (t / 231) (t % 231)))) = true := by
  decide +kernel

theorem chkC_3_d5304 : (List.range' 5304 8).all (fun t => (!(pOK tl tl (t % 231) (t / 231)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 231 % 77) * 282) (x2Tab o (t / 231 / 77) (t % 231))) (x2Tab t3 (t / 231) (t % 231)))) = true := by
  decide +kernel

theorem chkC_3_d5312 : (List.range' 5312 8).all (fun t => (!(pOK tl tl (t % 231) (t / 231)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 231 % 77) * 282) (x2Tab o (t / 231 / 77) (t % 231))) (x2Tab t3 (t / 231) (t % 231)))) = true := by
  decide +kernel

theorem chkC_3_d5320 : (List.range' 5320 8).all (fun t => (!(pOK tl tl (t % 231) (t / 231)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 231 % 77) * 282) (x2Tab o (t / 231 / 77) (t % 231))) (x2Tab t3 (t / 231) (t % 231)))) = true := by
  decide +kernel

theorem chkC_3_d5328 : (List.range' 5328 8).all (fun t => (!(pOK tl tl (t % 231) (t / 231)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 231 % 77) * 282) (x2Tab o (t / 231 / 77) (t % 231))) (x2Tab t3 (t / 231) (t % 231)))) = true := by
  decide +kernel

theorem chkC_3_d5336 : (List.range' 5336 8).all (fun t => (!(pOK tl tl (t % 231) (t / 231)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 231 % 77) * 282) (x2Tab o (t / 231 / 77) (t % 231))) (x2Tab t3 (t / 231) (t % 231)))) = true := by
  decide +kernel

theorem chkC_3_d5344 : (List.range' 5344 8).all (fun t => (!(pOK tl tl (t % 231) (t / 231)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 231 % 77) * 282) (x2Tab o (t / 231 / 77) (t % 231))) (x2Tab t3 (t / 231) (t % 231)))) = true := by
  decide +kernel

theorem chkC_3_d5352 : (List.range' 5352 8).all (fun t => (!(pOK tl tl (t % 231) (t / 231)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 231 % 77) * 282) (x2Tab o (t / 231 / 77) (t % 231))) (x2Tab t3 (t / 231) (t % 231)))) = true := by
  decide +kernel

theorem chkC_3_d5360 : (List.range' 5360 8).all (fun t => (!(pOK tl tl (t % 231) (t / 231)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 231 % 77) * 282) (x2Tab o (t / 231 / 77) (t % 231))) (x2Tab t3 (t / 231) (t % 231)))) = true := by
  decide +kernel

theorem chkC_3_d5368 : (List.range' 5368 8).all (fun t => (!(pOK tl tl (t % 231) (t / 231)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 231 % 77) * 282) (x2Tab o (t / 231 / 77) (t % 231))) (x2Tab t3 (t / 231) (t % 231)))) = true := by
  decide +kernel

theorem chkC_3_d5376 : (List.range' 5376 8).all (fun t => (!(pOK tl tl (t % 231) (t / 231)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 231 % 77) * 282) (x2Tab o (t / 231 / 77) (t % 231))) (x2Tab t3 (t / 231) (t % 231)))) = true := by
  decide +kernel

theorem chkC_3_d5384 : (List.range' 5384 8).all (fun t => (!(pOK tl tl (t % 231) (t / 231)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 231 % 77) * 282) (x2Tab o (t / 231 / 77) (t % 231))) (x2Tab t3 (t / 231) (t % 231)))) = true := by
  decide +kernel

theorem chkC_3_d5392 : (List.range' 5392 8).all (fun t => (!(pOK tl tl (t % 231) (t / 231)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 231 % 77) * 282) (x2Tab o (t / 231 / 77) (t % 231))) (x2Tab t3 (t / 231) (t % 231)))) = true := by
  decide +kernel

theorem chkC_3_d5400 : (List.range' 5400 8).all (fun t => (!(pOK tl tl (t % 231) (t / 231)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 231 % 77) * 282) (x2Tab o (t / 231 / 77) (t % 231))) (x2Tab t3 (t / 231) (t % 231)))) = true := by
  decide +kernel

theorem chkC_3_d5408 : (List.range' 5408 8).all (fun t => (!(pOK tl tl (t % 231) (t / 231)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 231 % 77) * 282) (x2Tab o (t / 231 / 77) (t % 231))) (x2Tab t3 (t / 231) (t % 231)))) = true := by
  decide +kernel

theorem chkC_3_d5416 : (List.range' 5416 8).all (fun t => (!(pOK tl tl (t % 231) (t / 231)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 231 % 77) * 282) (x2Tab o (t / 231 / 77) (t % 231))) (x2Tab t3 (t / 231) (t % 231)))) = true := by
  decide +kernel

theorem chkC_3_d5424 : (List.range' 5424 8).all (fun t => (!(pOK tl tl (t % 231) (t / 231)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 231 % 77) * 282) (x2Tab o (t / 231 / 77) (t % 231))) (x2Tab t3 (t / 231) (t % 231)))) = true := by
  decide +kernel

theorem chkC_3_d5432 : (List.range' 5432 8).all (fun t => (!(pOK tl tl (t % 231) (t / 231)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 231 % 77) * 282) (x2Tab o (t / 231 / 77) (t % 231))) (x2Tab t3 (t / 231) (t % 231)))) = true := by
  decide +kernel

theorem chkC_3_d5440 : (List.range' 5440 8).all (fun t => (!(pOK tl tl (t % 231) (t / 231)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 231 % 77) * 282) (x2Tab o (t / 231 / 77) (t % 231))) (x2Tab t3 (t / 231) (t % 231)))) = true := by
  decide +kernel

theorem chkC_3_d5448 : (List.range' 5448 8).all (fun t => (!(pOK tl tl (t % 231) (t / 231)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 231 % 77) * 282) (x2Tab o (t / 231 / 77) (t % 231))) (x2Tab t3 (t / 231) (t % 231)))) = true := by
  decide +kernel

theorem chkC_3_d5456 : (List.range' 5456 8).all (fun t => (!(pOK tl tl (t % 231) (t / 231)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 231 % 77) * 282) (x2Tab o (t / 231 / 77) (t % 231))) (x2Tab t3 (t / 231) (t % 231)))) = true := by
  decide +kernel

theorem chkC_3_d5464 : (List.range' 5464 8).all (fun t => (!(pOK tl tl (t % 231) (t / 231)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 231 % 77) * 282) (x2Tab o (t / 231 / 77) (t % 231))) (x2Tab t3 (t / 231) (t % 231)))) = true := by
  decide +kernel

theorem chkC_3_d5472 : (List.range' 5472 8).all (fun t => (!(pOK tl tl (t % 231) (t / 231)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 231 % 77) * 282) (x2Tab o (t / 231 / 77) (t % 231))) (x2Tab t3 (t / 231) (t % 231)))) = true := by
  decide +kernel

theorem chkC_3_d5480 : (List.range' 5480 8).all (fun t => (!(pOK tl tl (t % 231) (t / 231)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 231 % 77) * 282) (x2Tab o (t / 231 / 77) (t % 231))) (x2Tab t3 (t / 231) (t % 231)))) = true := by
  decide +kernel

theorem chkC_3_d5488 : (List.range' 5488 8).all (fun t => (!(pOK tl tl (t % 231) (t / 231)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 231 % 77) * 282) (x2Tab o (t / 231 / 77) (t % 231))) (x2Tab t3 (t / 231) (t % 231)))) = true := by
  decide +kernel

theorem chkC_3_d5496 : (List.range' 5496 8).all (fun t => (!(pOK tl tl (t % 231) (t / 231)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 231 % 77) * 282) (x2Tab o (t / 231 / 77) (t % 231))) (x2Tab t3 (t / 231) (t % 231)))) = true := by
  decide +kernel

theorem chkC_3_d5504 : (List.range' 5504 8).all (fun t => (!(pOK tl tl (t % 231) (t / 231)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 231 % 77) * 282) (x2Tab o (t / 231 / 77) (t % 231))) (x2Tab t3 (t / 231) (t % 231)))) = true := by
  decide +kernel

theorem chkC_3_d5512 : (List.range' 5512 8).all (fun t => (!(pOK tl tl (t % 231) (t / 231)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 231 % 77) * 282) (x2Tab o (t / 231 / 77) (t % 231))) (x2Tab t3 (t / 231) (t % 231)))) = true := by
  decide +kernel

theorem chkC_3_d5520 : (List.range' 5520 8).all (fun t => (!(pOK tl tl (t % 231) (t / 231)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 231 % 77) * 282) (x2Tab o (t / 231 / 77) (t % 231))) (x2Tab t3 (t / 231) (t % 231)))) = true := by
  decide +kernel

theorem chkC_3_d5528 : (List.range' 5528 8).all (fun t => (!(pOK tl tl (t % 231) (t / 231)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 231 % 77) * 282) (x2Tab o (t / 231 / 77) (t % 231))) (x2Tab t3 (t / 231) (t % 231)))) = true := by
  decide +kernel

theorem chkC_3_d5536 : (List.range' 5536 8).all (fun t => (!(pOK tl tl (t % 231) (t / 231)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 231 % 77) * 282) (x2Tab o (t / 231 / 77) (t % 231))) (x2Tab t3 (t / 231) (t % 231)))) = true := by
  decide +kernel

theorem chkC_3_d5544 : (List.range' 5544 8).all (fun t => (!(pOK tl tl (t % 231) (t / 231)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 231 % 77) * 282) (x2Tab o (t / 231 / 77) (t % 231))) (x2Tab t3 (t / 231) (t % 231)))) = true := by
  decide +kernel

theorem chkC_3_d5552 : (List.range' 5552 8).all (fun t => (!(pOK tl tl (t % 231) (t / 231)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 231 % 77) * 282) (x2Tab o (t / 231 / 77) (t % 231))) (x2Tab t3 (t / 231) (t % 231)))) = true := by
  decide +kernel

theorem chkC_3_d5560 : (List.range' 5560 8).all (fun t => (!(pOK tl tl (t % 231) (t / 231)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 231 % 77) * 282) (x2Tab o (t / 231 / 77) (t % 231))) (x2Tab t3 (t / 231) (t % 231)))) = true := by
  decide +kernel

theorem chkC_3_d5568 : (List.range' 5568 8).all (fun t => (!(pOK tl tl (t % 231) (t / 231)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 231 % 77) * 282) (x2Tab o (t / 231 / 77) (t % 231))) (x2Tab t3 (t / 231) (t % 231)))) = true := by
  decide +kernel

theorem chkC_3_d5576 : (List.range' 5576 8).all (fun t => (!(pOK tl tl (t % 231) (t / 231)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 231 % 77) * 282) (x2Tab o (t / 231 / 77) (t % 231))) (x2Tab t3 (t / 231) (t % 231)))) = true := by
  decide +kernel

theorem chkC_3_d5584 : (List.range' 5584 8).all (fun t => (!(pOK tl tl (t % 231) (t / 231)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 231 % 77) * 282) (x2Tab o (t / 231 / 77) (t % 231))) (x2Tab t3 (t / 231) (t % 231)))) = true := by
  decide +kernel

theorem chkC_3_d5592 : (List.range' 5592 8).all (fun t => (!(pOK tl tl (t % 231) (t / 231)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 231 % 77) * 282) (x2Tab o (t / 231 / 77) (t % 231))) (x2Tab t3 (t / 231) (t % 231)))) = true := by
  decide +kernel

theorem chkC_3_d5600 : (List.range' 5600 8).all (fun t => (!(pOK tl tl (t % 231) (t / 231)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 231 % 77) * 282) (x2Tab o (t / 231 / 77) (t % 231))) (x2Tab t3 (t / 231) (t % 231)))) = true := by
  decide +kernel

theorem chkC_3_d5608 : (List.range' 5608 8).all (fun t => (!(pOK tl tl (t % 231) (t / 231)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 231 % 77) * 282) (x2Tab o (t / 231 / 77) (t % 231))) (x2Tab t3 (t / 231) (t % 231)))) = true := by
  decide +kernel

theorem chkC_3_d5616 : (List.range' 5616 8).all (fun t => (!(pOK tl tl (t % 231) (t / 231)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 231 % 77) * 282) (x2Tab o (t / 231 / 77) (t % 231))) (x2Tab t3 (t / 231) (t % 231)))) = true := by
  decide +kernel

theorem chkC_3_d5624 : (List.range' 5624 8).all (fun t => (!(pOK tl tl (t % 231) (t / 231)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 231 % 77) * 282) (x2Tab o (t / 231 / 77) (t % 231))) (x2Tab t3 (t / 231) (t % 231)))) = true := by
  decide +kernel

theorem chkC_3_d5632 : (List.range' 5632 8).all (fun t => (!(pOK tl tl (t % 231) (t / 231)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 231 % 77) * 282) (x2Tab o (t / 231 / 77) (t % 231))) (x2Tab t3 (t / 231) (t % 231)))) = true := by
  decide +kernel

theorem chkC_3_d5640 : (List.range' 5640 8).all (fun t => (!(pOK tl tl (t % 231) (t / 231)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 231 % 77) * 282) (x2Tab o (t / 231 / 77) (t % 231))) (x2Tab t3 (t / 231) (t % 231)))) = true := by
  decide +kernel

theorem chkC_3_d5648 : (List.range' 5648 8).all (fun t => (!(pOK tl tl (t % 231) (t / 231)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 231 % 77) * 282) (x2Tab o (t / 231 / 77) (t % 231))) (x2Tab t3 (t / 231) (t % 231)))) = true := by
  decide +kernel

theorem chkC_3_d5656 : (List.range' 5656 8).all (fun t => (!(pOK tl tl (t % 231) (t / 231)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 231 % 77) * 282) (x2Tab o (t / 231 / 77) (t % 231))) (x2Tab t3 (t / 231) (t % 231)))) = true := by
  decide +kernel

theorem chkC_3_d5664 : (List.range' 5664 8).all (fun t => (!(pOK tl tl (t % 231) (t / 231)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 231 % 77) * 282) (x2Tab o (t / 231 / 77) (t % 231))) (x2Tab t3 (t / 231) (t % 231)))) = true := by
  decide +kernel

theorem chkC_3_d5672 : (List.range' 5672 8).all (fun t => (!(pOK tl tl (t % 231) (t / 231)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 231 % 77) * 282) (x2Tab o (t / 231 / 77) (t % 231))) (x2Tab t3 (t / 231) (t % 231)))) = true := by
  decide +kernel

theorem chkC_3_d5680 : (List.range' 5680 8).all (fun t => (!(pOK tl tl (t % 231) (t / 231)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 231 % 77) * 282) (x2Tab o (t / 231 / 77) (t % 231))) (x2Tab t3 (t / 231) (t % 231)))) = true := by
  decide +kernel

theorem chkC_3_d5688 : (List.range' 5688 8).all (fun t => (!(pOK tl tl (t % 231) (t / 231)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 231 % 77) * 282) (x2Tab o (t / 231 / 77) (t % 231))) (x2Tab t3 (t / 231) (t % 231)))) = true := by
  decide +kernel

theorem chkC_3_d5696 : (List.range' 5696 8).all (fun t => (!(pOK tl tl (t % 231) (t / 231)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 231 % 77) * 282) (x2Tab o (t / 231 / 77) (t % 231))) (x2Tab t3 (t / 231) (t % 231)))) = true := by
  decide +kernel

theorem chkC_3_d5704 : (List.range' 5704 8).all (fun t => (!(pOK tl tl (t % 231) (t / 231)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 231 % 77) * 282) (x2Tab o (t / 231 / 77) (t % 231))) (x2Tab t3 (t / 231) (t % 231)))) = true := by
  decide +kernel

theorem chkC_3_d5712 : (List.range' 5712 8).all (fun t => (!(pOK tl tl (t % 231) (t / 231)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 231 % 77) * 282) (x2Tab o (t / 231 / 77) (t % 231))) (x2Tab t3 (t / 231) (t % 231)))) = true := by
  decide +kernel

theorem chkC_3_d5720 : (List.range' 5720 8).all (fun t => (!(pOK tl tl (t % 231) (t / 231)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 231 % 77) * 282) (x2Tab o (t / 231 / 77) (t % 231))) (x2Tab t3 (t / 231) (t % 231)))) = true := by
  decide +kernel

theorem chkC_3_d5728 : (List.range' 5728 8).all (fun t => (!(pOK tl tl (t % 231) (t / 231)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 231 % 77) * 282) (x2Tab o (t / 231 / 77) (t % 231))) (x2Tab t3 (t / 231) (t % 231)))) = true := by
  decide +kernel

theorem chkC_3_d5736 : (List.range' 5736 8).all (fun t => (!(pOK tl tl (t % 231) (t / 231)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 231 % 77) * 282) (x2Tab o (t / 231 / 77) (t % 231))) (x2Tab t3 (t / 231) (t % 231)))) = true := by
  decide +kernel

theorem chkC_3_d5744 : (List.range' 5744 8).all (fun t => (!(pOK tl tl (t % 231) (t / 231)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 231 % 77) * 282) (x2Tab o (t / 231 / 77) (t % 231))) (x2Tab t3 (t / 231) (t % 231)))) = true := by
  decide +kernel

theorem chkC_3_d5752 : (List.range' 5752 8).all (fun t => (!(pOK tl tl (t % 231) (t / 231)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 231 % 77) * 282) (x2Tab o (t / 231 / 77) (t % 231))) (x2Tab t3 (t / 231) (t % 231)))) = true := by
  decide +kernel

theorem chkC_3_d5760 : (List.range' 5760 8).all (fun t => (!(pOK tl tl (t % 231) (t / 231)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 231 % 77) * 282) (x2Tab o (t / 231 / 77) (t % 231))) (x2Tab t3 (t / 231) (t % 231)))) = true := by
  decide +kernel

theorem chkC_3_d5768 : (List.range' 5768 8).all (fun t => (!(pOK tl tl (t % 231) (t / 231)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 231 % 77) * 282) (x2Tab o (t / 231 / 77) (t % 231))) (x2Tab t3 (t / 231) (t % 231)))) = true := by
  decide +kernel

theorem chkC_3_d5776 : (List.range' 5776 8).all (fun t => (!(pOK tl tl (t % 231) (t / 231)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 231 % 77) * 282) (x2Tab o (t / 231 / 77) (t % 231))) (x2Tab t3 (t / 231) (t % 231)))) = true := by
  decide +kernel

theorem chkC_3_d5784 : (List.range' 5784 8).all (fun t => (!(pOK tl tl (t % 231) (t / 231)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 231 % 77) * 282) (x2Tab o (t / 231 / 77) (t % 231))) (x2Tab t3 (t / 231) (t % 231)))) = true := by
  decide +kernel

theorem chkC_3_d5792 : (List.range' 5792 8).all (fun t => (!(pOK tl tl (t % 231) (t / 231)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 231 % 77) * 282) (x2Tab o (t / 231 / 77) (t % 231))) (x2Tab t3 (t / 231) (t % 231)))) = true := by
  decide +kernel

theorem chkC_3_d5800 : (List.range' 5800 8).all (fun t => (!(pOK tl tl (t % 231) (t / 231)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 231 % 77) * 282) (x2Tab o (t / 231 / 77) (t % 231))) (x2Tab t3 (t / 231) (t % 231)))) = true := by
  decide +kernel

theorem chkC_3_d5808 : (List.range' 5808 8).all (fun t => (!(pOK tl tl (t % 231) (t / 231)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 231 % 77) * 282) (x2Tab o (t / 231 / 77) (t % 231))) (x2Tab t3 (t / 231) (t % 231)))) = true := by
  decide +kernel

theorem chkC_3_d5816 : (List.range' 5816 8).all (fun t => (!(pOK tl tl (t % 231) (t / 231)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 231 % 77) * 282) (x2Tab o (t / 231 / 77) (t % 231))) (x2Tab t3 (t / 231) (t % 231)))) = true := by
  decide +kernel

theorem chkC_3_d5824 : (List.range' 5824 8).all (fun t => (!(pOK tl tl (t % 231) (t / 231)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 231 % 77) * 282) (x2Tab o (t / 231 / 77) (t % 231))) (x2Tab t3 (t / 231) (t % 231)))) = true := by
  decide +kernel

theorem chkC_3_d5832 : (List.range' 5832 8).all (fun t => (!(pOK tl tl (t % 231) (t / 231)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 231 % 77) * 282) (x2Tab o (t / 231 / 77) (t % 231))) (x2Tab t3 (t / 231) (t % 231)))) = true := by
  decide +kernel

theorem chkC_3_d5840 : (List.range' 5840 8).all (fun t => (!(pOK tl tl (t % 231) (t / 231)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 231 % 77) * 282) (x2Tab o (t / 231 / 77) (t % 231))) (x2Tab t3 (t / 231) (t % 231)))) = true := by
  decide +kernel

theorem chkC_3_d5848 : (List.range' 5848 8).all (fun t => (!(pOK tl tl (t % 231) (t / 231)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 231 % 77) * 282) (x2Tab o (t / 231 / 77) (t % 231))) (x2Tab t3 (t / 231) (t % 231)))) = true := by
  decide +kernel

theorem chkC_3_d5856 : (List.range' 5856 8).all (fun t => (!(pOK tl tl (t % 231) (t / 231)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 231 % 77) * 282) (x2Tab o (t / 231 / 77) (t % 231))) (x2Tab t3 (t / 231) (t % 231)))) = true := by
  decide +kernel

theorem chkC_3_d5864 : (List.range' 5864 8).all (fun t => (!(pOK tl tl (t % 231) (t / 231)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 231 % 77) * 282) (x2Tab o (t / 231 / 77) (t % 231))) (x2Tab t3 (t / 231) (t % 231)))) = true := by
  decide +kernel

theorem chkC_3_d5872 : (List.range' 5872 8).all (fun t => (!(pOK tl tl (t % 231) (t / 231)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 231 % 77) * 282) (x2Tab o (t / 231 / 77) (t % 231))) (x2Tab t3 (t / 231) (t % 231)))) = true := by
  decide +kernel

theorem chkC_3_d5880 : (List.range' 5880 8).all (fun t => (!(pOK tl tl (t % 231) (t / 231)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 231 % 77) * 282) (x2Tab o (t / 231 / 77) (t % 231))) (x2Tab t3 (t / 231) (t % 231)))) = true := by
  decide +kernel

theorem chkC_3_d5888 : (List.range' 5888 8).all (fun t => (!(pOK tl tl (t % 231) (t / 231)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 231 % 77) * 282) (x2Tab o (t / 231 / 77) (t % 231))) (x2Tab t3 (t / 231) (t % 231)))) = true := by
  decide +kernel

theorem chkC_3_d5896 : (List.range' 5896 8).all (fun t => (!(pOK tl tl (t % 231) (t / 231)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 231 % 77) * 282) (x2Tab o (t / 231 / 77) (t % 231))) (x2Tab t3 (t / 231) (t % 231)))) = true := by
  decide +kernel

theorem chkC_3_d5904 : (List.range' 5904 8).all (fun t => (!(pOK tl tl (t % 231) (t / 231)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 231 % 77) * 282) (x2Tab o (t / 231 / 77) (t % 231))) (x2Tab t3 (t / 231) (t % 231)))) = true := by
  decide +kernel

theorem chkC_3_d5912 : (List.range' 5912 8).all (fun t => (!(pOK tl tl (t % 231) (t / 231)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 231 % 77) * 282) (x2Tab o (t / 231 / 77) (t % 231))) (x2Tab t3 (t / 231) (t % 231)))) = true := by
  decide +kernel

theorem chkC_3_d5920 : (List.range' 5920 8).all (fun t => (!(pOK tl tl (t % 231) (t / 231)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 231 % 77) * 282) (x2Tab o (t / 231 / 77) (t % 231))) (x2Tab t3 (t / 231) (t % 231)))) = true := by
  decide +kernel

theorem chkC_3_d5928 : (List.range' 5928 8).all (fun t => (!(pOK tl tl (t % 231) (t / 231)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 231 % 77) * 282) (x2Tab o (t / 231 / 77) (t % 231))) (x2Tab t3 (t / 231) (t % 231)))) = true := by
  decide +kernel

theorem chkC_3_d5936 : (List.range' 5936 8).all (fun t => (!(pOK tl tl (t % 231) (t / 231)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 231 % 77) * 282) (x2Tab o (t / 231 / 77) (t % 231))) (x2Tab t3 (t / 231) (t % 231)))) = true := by
  decide +kernel

theorem chkC_3_d5944 : (List.range' 5944 8).all (fun t => (!(pOK tl tl (t % 231) (t / 231)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 231 % 77) * 282) (x2Tab o (t / 231 / 77) (t % 231))) (x2Tab t3 (t / 231) (t % 231)))) = true := by
  decide +kernel

theorem chkC_3_d5952 : (List.range' 5952 8).all (fun t => (!(pOK tl tl (t % 231) (t / 231)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 231 % 77) * 282) (x2Tab o (t / 231 / 77) (t % 231))) (x2Tab t3 (t / 231) (t % 231)))) = true := by
  decide +kernel

theorem chkC_3_d5960 : (List.range' 5960 8).all (fun t => (!(pOK tl tl (t % 231) (t / 231)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 231 % 77) * 282) (x2Tab o (t / 231 / 77) (t % 231))) (x2Tab t3 (t / 231) (t % 231)))) = true := by
  decide +kernel

theorem chkC_3_d5968 : (List.range' 5968 8).all (fun t => (!(pOK tl tl (t % 231) (t / 231)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 231 % 77) * 282) (x2Tab o (t / 231 / 77) (t % 231))) (x2Tab t3 (t / 231) (t % 231)))) = true := by
  decide +kernel

theorem chkC_3_d5976 : (List.range' 5976 8).all (fun t => (!(pOK tl tl (t % 231) (t / 231)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 231 % 77) * 282) (x2Tab o (t / 231 / 77) (t % 231))) (x2Tab t3 (t / 231) (t % 231)))) = true := by
  decide +kernel

theorem chkC_3_d5984 : (List.range' 5984 8).all (fun t => (!(pOK tl tl (t % 231) (t / 231)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 231 % 77) * 282) (x2Tab o (t / 231 / 77) (t % 231))) (x2Tab t3 (t / 231) (t % 231)))) = true := by
  decide +kernel

theorem chkC_3_d5992 : (List.range' 5992 8).all (fun t => (!(pOK tl tl (t % 231) (t / 231)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 231 % 77) * 282) (x2Tab o (t / 231 / 77) (t % 231))) (x2Tab t3 (t / 231) (t % 231)))) = true := by
  decide +kernel

theorem chkC_3_d6000 : (List.range' 6000 8).all (fun t => (!(pOK tl tl (t % 231) (t / 231)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 231 % 77) * 282) (x2Tab o (t / 231 / 77) (t % 231))) (x2Tab t3 (t / 231) (t % 231)))) = true := by
  decide +kernel

theorem chkC_3_d6008 : (List.range' 6008 8).all (fun t => (!(pOK tl tl (t % 231) (t / 231)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 231 % 77) * 282) (x2Tab o (t / 231 / 77) (t % 231))) (x2Tab t3 (t / 231) (t % 231)))) = true := by
  decide +kernel

theorem chkC_3_d6016 : (List.range' 6016 8).all (fun t => (!(pOK tl tl (t % 231) (t / 231)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 231 % 77) * 282) (x2Tab o (t / 231 / 77) (t % 231))) (x2Tab t3 (t / 231) (t % 231)))) = true := by
  decide +kernel

theorem chkC_3_d6024 : (List.range' 6024 8).all (fun t => (!(pOK tl tl (t % 231) (t / 231)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 231 % 77) * 282) (x2Tab o (t / 231 / 77) (t % 231))) (x2Tab t3 (t / 231) (t % 231)))) = true := by
  decide +kernel

theorem chkC_3_d6032 : (List.range' 6032 8).all (fun t => (!(pOK tl tl (t % 231) (t / 231)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 231 % 77) * 282) (x2Tab o (t / 231 / 77) (t % 231))) (x2Tab t3 (t / 231) (t % 231)))) = true := by
  decide +kernel

theorem chkC_3_d6040 : (List.range' 6040 8).all (fun t => (!(pOK tl tl (t % 231) (t / 231)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 231 % 77) * 282) (x2Tab o (t / 231 / 77) (t % 231))) (x2Tab t3 (t / 231) (t % 231)))) = true := by
  decide +kernel

theorem chkC_3_d6048 : (List.range' 6048 8).all (fun t => (!(pOK tl tl (t % 231) (t / 231)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 231 % 77) * 282) (x2Tab o (t / 231 / 77) (t % 231))) (x2Tab t3 (t / 231) (t % 231)))) = true := by
  decide +kernel

theorem chkC_3_d6056 : (List.range' 6056 8).all (fun t => (!(pOK tl tl (t % 231) (t / 231)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 231 % 77) * 282) (x2Tab o (t / 231 / 77) (t % 231))) (x2Tab t3 (t / 231) (t % 231)))) = true := by
  decide +kernel

theorem chkC_3_d6064 : (List.range' 6064 8).all (fun t => (!(pOK tl tl (t % 231) (t / 231)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 231 % 77) * 282) (x2Tab o (t / 231 / 77) (t % 231))) (x2Tab t3 (t / 231) (t % 231)))) = true := by
  decide +kernel

theorem chkC_3_d6072 : (List.range' 6072 8).all (fun t => (!(pOK tl tl (t % 231) (t / 231)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 231 % 77) * 282) (x2Tab o (t / 231 / 77) (t % 231))) (x2Tab t3 (t / 231) (t % 231)))) = true := by
  decide +kernel

theorem chkC_3_d6080 : (List.range' 6080 8).all (fun t => (!(pOK tl tl (t % 231) (t / 231)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 231 % 77) * 282) (x2Tab o (t / 231 / 77) (t % 231))) (x2Tab t3 (t / 231) (t % 231)))) = true := by
  decide +kernel

theorem chkC_3_d6088 : (List.range' 6088 8).all (fun t => (!(pOK tl tl (t % 231) (t / 231)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 231 % 77) * 282) (x2Tab o (t / 231 / 77) (t % 231))) (x2Tab t3 (t / 231) (t % 231)))) = true := by
  decide +kernel

theorem chkC_3_d6096 : (List.range' 6096 8).all (fun t => (!(pOK tl tl (t % 231) (t / 231)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 231 % 77) * 282) (x2Tab o (t / 231 / 77) (t % 231))) (x2Tab t3 (t / 231) (t % 231)))) = true := by
  decide +kernel

theorem chkC_3_d6104 : (List.range' 6104 8).all (fun t => (!(pOK tl tl (t % 231) (t / 231)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 231 % 77) * 282) (x2Tab o (t / 231 / 77) (t % 231))) (x2Tab t3 (t / 231) (t % 231)))) = true := by
  decide +kernel

theorem chkC_3_d6112 : (List.range' 6112 8).all (fun t => (!(pOK tl tl (t % 231) (t / 231)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 231 % 77) * 282) (x2Tab o (t / 231 / 77) (t % 231))) (x2Tab t3 (t / 231) (t % 231)))) = true := by
  decide +kernel

theorem chkC_3_d6120 : (List.range' 6120 8).all (fun t => (!(pOK tl tl (t % 231) (t / 231)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 231 % 77) * 282) (x2Tab o (t / 231 / 77) (t % 231))) (x2Tab t3 (t / 231) (t % 231)))) = true := by
  decide +kernel

theorem chkC_3_d6128 : (List.range' 6128 8).all (fun t => (!(pOK tl tl (t % 231) (t / 231)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 231 % 77) * 282) (x2Tab o (t / 231 / 77) (t % 231))) (x2Tab t3 (t / 231) (t % 231)))) = true := by
  decide +kernel

theorem chkC_3_d6136 : (List.range' 6136 8).all (fun t => (!(pOK tl tl (t % 231) (t / 231)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 231 % 77) * 282) (x2Tab o (t / 231 / 77) (t % 231))) (x2Tab t3 (t / 231) (t % 231)))) = true := by
  decide +kernel

theorem chkC_3_d6144 : (List.range' 6144 8).all (fun t => (!(pOK tl tl (t % 231) (t / 231)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 231 % 77) * 282) (x2Tab o (t / 231 / 77) (t % 231))) (x2Tab t3 (t / 231) (t % 231)))) = true := by
  decide +kernel

theorem chkC_3_d6152 : (List.range' 6152 8).all (fun t => (!(pOK tl tl (t % 231) (t / 231)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 231 % 77) * 282) (x2Tab o (t / 231 / 77) (t % 231))) (x2Tab t3 (t / 231) (t % 231)))) = true := by
  decide +kernel

theorem chkC_3_d6160 : (List.range' 6160 8).all (fun t => (!(pOK tl tl (t % 231) (t / 231)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 231 % 77) * 282) (x2Tab o (t / 231 / 77) (t % 231))) (x2Tab t3 (t / 231) (t % 231)))) = true := by
  decide +kernel

theorem chkC_3_d6168 : (List.range' 6168 8).all (fun t => (!(pOK tl tl (t % 231) (t / 231)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 231 % 77) * 282) (x2Tab o (t / 231 / 77) (t % 231))) (x2Tab t3 (t / 231) (t % 231)))) = true := by
  decide +kernel

theorem chkC_3_d6176 : (List.range' 6176 8).all (fun t => (!(pOK tl tl (t % 231) (t / 231)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 231 % 77) * 282) (x2Tab o (t / 231 / 77) (t % 231))) (x2Tab t3 (t / 231) (t % 231)))) = true := by
  decide +kernel

theorem chkC_3_d6184 : (List.range' 6184 8).all (fun t => (!(pOK tl tl (t % 231) (t / 231)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 231 % 77) * 282) (x2Tab o (t / 231 / 77) (t % 231))) (x2Tab t3 (t / 231) (t % 231)))) = true := by
  decide +kernel

theorem chkC_3_d6192 : (List.range' 6192 8).all (fun t => (!(pOK tl tl (t % 231) (t / 231)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 231 % 77) * 282) (x2Tab o (t / 231 / 77) (t % 231))) (x2Tab t3 (t / 231) (t % 231)))) = true := by
  decide +kernel

theorem chkC_3_d6200 : (List.range' 6200 8).all (fun t => (!(pOK tl tl (t % 231) (t / 231)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 231 % 77) * 282) (x2Tab o (t / 231 / 77) (t % 231))) (x2Tab t3 (t / 231) (t % 231)))) = true := by
  decide +kernel

theorem chkC_3_d6208 : (List.range' 6208 8).all (fun t => (!(pOK tl tl (t % 231) (t / 231)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 231 % 77) * 282) (x2Tab o (t / 231 / 77) (t % 231))) (x2Tab t3 (t / 231) (t % 231)))) = true := by
  decide +kernel

theorem chkC_3_d6216 : (List.range' 6216 8).all (fun t => (!(pOK tl tl (t % 231) (t / 231)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 231 % 77) * 282) (x2Tab o (t / 231 / 77) (t % 231))) (x2Tab t3 (t / 231) (t % 231)))) = true := by
  decide +kernel

theorem chkC_3_d6224 : (List.range' 6224 8).all (fun t => (!(pOK tl tl (t % 231) (t / 231)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 231 % 77) * 282) (x2Tab o (t / 231 / 77) (t % 231))) (x2Tab t3 (t / 231) (t % 231)))) = true := by
  decide +kernel

theorem chkC_3_d6232 : (List.range' 6232 8).all (fun t => (!(pOK tl tl (t % 231) (t / 231)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 231 % 77) * 282) (x2Tab o (t / 231 / 77) (t % 231))) (x2Tab t3 (t / 231) (t % 231)))) = true := by
  decide +kernel

theorem chkC_3_d6240 : (List.range' 6240 8).all (fun t => (!(pOK tl tl (t % 231) (t / 231)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 231 % 77) * 282) (x2Tab o (t / 231 / 77) (t % 231))) (x2Tab t3 (t / 231) (t % 231)))) = true := by
  decide +kernel

theorem chkC_3_d6248 : (List.range' 6248 8).all (fun t => (!(pOK tl tl (t % 231) (t / 231)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 231 % 77) * 282) (x2Tab o (t / 231 / 77) (t % 231))) (x2Tab t3 (t / 231) (t % 231)))) = true := by
  decide +kernel

theorem chkC_3_d6256 : (List.range' 6256 8).all (fun t => (!(pOK tl tl (t % 231) (t / 231)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 231 % 77) * 282) (x2Tab o (t / 231 / 77) (t % 231))) (x2Tab t3 (t / 231) (t % 231)))) = true := by
  decide +kernel

theorem chkC_3_d6264 : (List.range' 6264 8).all (fun t => (!(pOK tl tl (t % 231) (t / 231)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 231 % 77) * 282) (x2Tab o (t / 231 / 77) (t % 231))) (x2Tab t3 (t / 231) (t % 231)))) = true := by
  decide +kernel

theorem chkC_3_d6272 : (List.range' 6272 8).all (fun t => (!(pOK tl tl (t % 231) (t / 231)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 231 % 77) * 282) (x2Tab o (t / 231 / 77) (t % 231))) (x2Tab t3 (t / 231) (t % 231)))) = true := by
  decide +kernel

theorem chkC_3_d6280 : (List.range' 6280 8).all (fun t => (!(pOK tl tl (t % 231) (t / 231)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 231 % 77) * 282) (x2Tab o (t / 231 / 77) (t % 231))) (x2Tab t3 (t / 231) (t % 231)))) = true := by
  decide +kernel

theorem chkC_3_d6288 : (List.range' 6288 8).all (fun t => (!(pOK tl tl (t % 231) (t / 231)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 231 % 77) * 282) (x2Tab o (t / 231 / 77) (t % 231))) (x2Tab t3 (t / 231) (t % 231)))) = true := by
  decide +kernel

theorem chkC_3_d6296 : (List.range' 6296 8).all (fun t => (!(pOK tl tl (t % 231) (t / 231)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 231 % 77) * 282) (x2Tab o (t / 231 / 77) (t % 231))) (x2Tab t3 (t / 231) (t % 231)))) = true := by
  decide +kernel

theorem chkC_3_d6304 : (List.range' 6304 8).all (fun t => (!(pOK tl tl (t % 231) (t / 231)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 231 % 77) * 282) (x2Tab o (t / 231 / 77) (t % 231))) (x2Tab t3 (t / 231) (t % 231)))) = true := by
  decide +kernel

theorem chkC_3_d6312 : (List.range' 6312 8).all (fun t => (!(pOK tl tl (t % 231) (t / 231)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 231 % 77) * 282) (x2Tab o (t / 231 / 77) (t % 231))) (x2Tab t3 (t / 231) (t % 231)))) = true := by
  decide +kernel

theorem chkC_3_d6320 : (List.range' 6320 8).all (fun t => (!(pOK tl tl (t % 231) (t / 231)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 231 % 77) * 282) (x2Tab o (t / 231 / 77) (t % 231))) (x2Tab t3 (t / 231) (t % 231)))) = true := by
  decide +kernel

theorem chkC_3_d6328 : (List.range' 6328 8).all (fun t => (!(pOK tl tl (t % 231) (t / 231)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 231 % 77) * 282) (x2Tab o (t / 231 / 77) (t % 231))) (x2Tab t3 (t / 231) (t % 231)))) = true := by
  decide +kernel

theorem chkC_3_d6336 : (List.range' 6336 8).all (fun t => (!(pOK tl tl (t % 231) (t / 231)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 231 % 77) * 282) (x2Tab o (t / 231 / 77) (t % 231))) (x2Tab t3 (t / 231) (t % 231)))) = true := by
  decide +kernel

theorem chkC_3_d6344 : (List.range' 6344 8).all (fun t => (!(pOK tl tl (t % 231) (t / 231)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 231 % 77) * 282) (x2Tab o (t / 231 / 77) (t % 231))) (x2Tab t3 (t / 231) (t % 231)))) = true := by
  decide +kernel

theorem chkC_3_d6352 : (List.range' 6352 8).all (fun t => (!(pOK tl tl (t % 231) (t / 231)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 231 % 77) * 282) (x2Tab o (t / 231 / 77) (t % 231))) (x2Tab t3 (t / 231) (t % 231)))) = true := by
  decide +kernel

theorem chkC_3_d6360 : (List.range' 6360 8).all (fun t => (!(pOK tl tl (t % 231) (t / 231)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 231 % 77) * 282) (x2Tab o (t / 231 / 77) (t % 231))) (x2Tab t3 (t / 231) (t % 231)))) = true := by
  decide +kernel

theorem chkC_3_d6368 : (List.range' 6368 8).all (fun t => (!(pOK tl tl (t % 231) (t / 231)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 231 % 77) * 282) (x2Tab o (t / 231 / 77) (t % 231))) (x2Tab t3 (t / 231) (t % 231)))) = true := by
  decide +kernel

theorem chkC_3_d6376 : (List.range' 6376 8).all (fun t => (!(pOK tl tl (t % 231) (t / 231)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 231 % 77) * 282) (x2Tab o (t / 231 / 77) (t % 231))) (x2Tab t3 (t / 231) (t % 231)))) = true := by
  decide +kernel

theorem chkC_3_d6384 : (List.range' 6384 8).all (fun t => (!(pOK tl tl (t % 231) (t / 231)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 231 % 77) * 282) (x2Tab o (t / 231 / 77) (t % 231))) (x2Tab t3 (t / 231) (t % 231)))) = true := by
  decide +kernel

theorem chkC_3_d6392 : (List.range' 6392 8).all (fun t => (!(pOK tl tl (t % 231) (t / 231)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 231 % 77) * 282) (x2Tab o (t / 231 / 77) (t % 231))) (x2Tab t3 (t / 231) (t % 231)))) = true := by
  decide +kernel

theorem chkC_3 : ∀ t, 4800 ≤ t → t < 6400 → ((!(pOK tl tl (t % 231) (t / 231)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 231 % 77) * 282) (x2Tab o (t / 231 / 77) (t % 231))) (x2Tab t3 (t / 231) (t % 231)))) = true := by
  exact (x2c_join _ 4800 4808 6400 (x2c_range_all (fun t => (!(pOK tl tl (t % 231) (t / 231)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 231 % 77) * 282) (x2Tab o (t / 231 / 77) (t % 231))) (x2Tab t3 (t / 231) (t % 231)))) 4800 8 chkC_3_d4800) (x2c_join _ 4808 4816 6400 (x2c_range_all (fun t => (!(pOK tl tl (t % 231) (t / 231)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 231 % 77) * 282) (x2Tab o (t / 231 / 77) (t % 231))) (x2Tab t3 (t / 231) (t % 231)))) 4808 8 chkC_3_d4808) (x2c_join _ 4816 4824 6400 (x2c_range_all (fun t => (!(pOK tl tl (t % 231) (t / 231)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 231 % 77) * 282) (x2Tab o (t / 231 / 77) (t % 231))) (x2Tab t3 (t / 231) (t % 231)))) 4816 8 chkC_3_d4816) (x2c_join _ 4824 4832 6400 (x2c_range_all (fun t => (!(pOK tl tl (t % 231) (t / 231)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 231 % 77) * 282) (x2Tab o (t / 231 / 77) (t % 231))) (x2Tab t3 (t / 231) (t % 231)))) 4824 8 chkC_3_d4824) (x2c_join _ 4832 4840 6400 (x2c_range_all (fun t => (!(pOK tl tl (t % 231) (t / 231)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 231 % 77) * 282) (x2Tab o (t / 231 / 77) (t % 231))) (x2Tab t3 (t / 231) (t % 231)))) 4832 8 chkC_3_d4832) (x2c_join _ 4840 4848 6400 (x2c_range_all (fun t => (!(pOK tl tl (t % 231) (t / 231)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 231 % 77) * 282) (x2Tab o (t / 231 / 77) (t % 231))) (x2Tab t3 (t / 231) (t % 231)))) 4840 8 chkC_3_d4840) (x2c_join _ 4848 4856 6400 (x2c_range_all (fun t => (!(pOK tl tl (t % 231) (t / 231)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 231 % 77) * 282) (x2Tab o (t / 231 / 77) (t % 231))) (x2Tab t3 (t / 231) (t % 231)))) 4848 8 chkC_3_d4848) (x2c_join _ 4856 4864 6400 (x2c_range_all (fun t => (!(pOK tl tl (t % 231) (t / 231)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 231 % 77) * 282) (x2Tab o (t / 231 / 77) (t % 231))) (x2Tab t3 (t / 231) (t % 231)))) 4856 8 chkC_3_d4856) (x2c_join _ 4864 4872 6400 (x2c_range_all (fun t => (!(pOK tl tl (t % 231) (t / 231)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 231 % 77) * 282) (x2Tab o (t / 231 / 77) (t % 231))) (x2Tab t3 (t / 231) (t % 231)))) 4864 8 chkC_3_d4864) (x2c_join _ 4872 4880 6400 (x2c_range_all (fun t => (!(pOK tl tl (t % 231) (t / 231)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 231 % 77) * 282) (x2Tab o (t / 231 / 77) (t % 231))) (x2Tab t3 (t / 231) (t % 231)))) 4872 8 chkC_3_d4872) (x2c_join _ 4880 4888 6400 (x2c_range_all (fun t => (!(pOK tl tl (t % 231) (t / 231)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 231 % 77) * 282) (x2Tab o (t / 231 / 77) (t % 231))) (x2Tab t3 (t / 231) (t % 231)))) 4880 8 chkC_3_d4880) (x2c_join _ 4888 4896 6400 (x2c_range_all (fun t => (!(pOK tl tl (t % 231) (t / 231)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 231 % 77) * 282) (x2Tab o (t / 231 / 77) (t % 231))) (x2Tab t3 (t / 231) (t % 231)))) 4888 8 chkC_3_d4888) (x2c_join _ 4896 4904 6400 (x2c_range_all (fun t => (!(pOK tl tl (t % 231) (t / 231)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 231 % 77) * 282) (x2Tab o (t / 231 / 77) (t % 231))) (x2Tab t3 (t / 231) (t % 231)))) 4896 8 chkC_3_d4896) (x2c_join _ 4904 4912 6400 (x2c_range_all (fun t => (!(pOK tl tl (t % 231) (t / 231)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 231 % 77) * 282) (x2Tab o (t / 231 / 77) (t % 231))) (x2Tab t3 (t / 231) (t % 231)))) 4904 8 chkC_3_d4904) (x2c_join _ 4912 4920 6400 (x2c_range_all (fun t => (!(pOK tl tl (t % 231) (t / 231)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 231 % 77) * 282) (x2Tab o (t / 231 / 77) (t % 231))) (x2Tab t3 (t / 231) (t % 231)))) 4912 8 chkC_3_d4912) (x2c_join _ 4920 4928 6400 (x2c_range_all (fun t => (!(pOK tl tl (t % 231) (t / 231)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 231 % 77) * 282) (x2Tab o (t / 231 / 77) (t % 231))) (x2Tab t3 (t / 231) (t % 231)))) 4920 8 chkC_3_d4920) (x2c_join _ 4928 4936 6400 (x2c_range_all (fun t => (!(pOK tl tl (t % 231) (t / 231)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 231 % 77) * 282) (x2Tab o (t / 231 / 77) (t % 231))) (x2Tab t3 (t / 231) (t % 231)))) 4928 8 chkC_3_d4928) (x2c_join _ 4936 4944 6400 (x2c_range_all (fun t => (!(pOK tl tl (t % 231) (t / 231)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 231 % 77) * 282) (x2Tab o (t / 231 / 77) (t % 231))) (x2Tab t3 (t / 231) (t % 231)))) 4936 8 chkC_3_d4936) (x2c_join _ 4944 4952 6400 (x2c_range_all (fun t => (!(pOK tl tl (t % 231) (t / 231)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 231 % 77) * 282) (x2Tab o (t / 231 / 77) (t % 231))) (x2Tab t3 (t / 231) (t % 231)))) 4944 8 chkC_3_d4944) (x2c_join _ 4952 4960 6400 (x2c_range_all (fun t => (!(pOK tl tl (t % 231) (t / 231)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 231 % 77) * 282) (x2Tab o (t / 231 / 77) (t % 231))) (x2Tab t3 (t / 231) (t % 231)))) 4952 8 chkC_3_d4952) (x2c_join _ 4960 4968 6400 (x2c_range_all (fun t => (!(pOK tl tl (t % 231) (t / 231)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 231 % 77) * 282) (x2Tab o (t / 231 / 77) (t % 231))) (x2Tab t3 (t / 231) (t % 231)))) 4960 8 chkC_3_d4960) (x2c_join _ 4968 4976 6400 (x2c_range_all (fun t => (!(pOK tl tl (t % 231) (t / 231)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 231 % 77) * 282) (x2Tab o (t / 231 / 77) (t % 231))) (x2Tab t3 (t / 231) (t % 231)))) 4968 8 chkC_3_d4968) (x2c_join _ 4976 4984 6400 (x2c_range_all (fun t => (!(pOK tl tl (t % 231) (t / 231)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 231 % 77) * 282) (x2Tab o (t / 231 / 77) (t % 231))) (x2Tab t3 (t / 231) (t % 231)))) 4976 8 chkC_3_d4976) (x2c_join _ 4984 4992 6400 (x2c_range_all (fun t => (!(pOK tl tl (t % 231) (t / 231)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 231 % 77) * 282) (x2Tab o (t / 231 / 77) (t % 231))) (x2Tab t3 (t / 231) (t % 231)))) 4984 8 chkC_3_d4984) (x2c_join _ 4992 5000 6400 (x2c_range_all (fun t => (!(pOK tl tl (t % 231) (t / 231)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 231 % 77) * 282) (x2Tab o (t / 231 / 77) (t % 231))) (x2Tab t3 (t / 231) (t % 231)))) 4992 8 chkC_3_d4992) (x2c_join _ 5000 5008 6400 (x2c_range_all (fun t => (!(pOK tl tl (t % 231) (t / 231)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 231 % 77) * 282) (x2Tab o (t / 231 / 77) (t % 231))) (x2Tab t3 (t / 231) (t % 231)))) 5000 8 chkC_3_d5000) (x2c_join _ 5008 5016 6400 (x2c_range_all (fun t => (!(pOK tl tl (t % 231) (t / 231)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 231 % 77) * 282) (x2Tab o (t / 231 / 77) (t % 231))) (x2Tab t3 (t / 231) (t % 231)))) 5008 8 chkC_3_d5008) (x2c_join _ 5016 5024 6400 (x2c_range_all (fun t => (!(pOK tl tl (t % 231) (t / 231)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 231 % 77) * 282) (x2Tab o (t / 231 / 77) (t % 231))) (x2Tab t3 (t / 231) (t % 231)))) 5016 8 chkC_3_d5016) (x2c_join _ 5024 5032 6400 (x2c_range_all (fun t => (!(pOK tl tl (t % 231) (t / 231)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 231 % 77) * 282) (x2Tab o (t / 231 / 77) (t % 231))) (x2Tab t3 (t / 231) (t % 231)))) 5024 8 chkC_3_d5024) (x2c_join _ 5032 5040 6400 (x2c_range_all (fun t => (!(pOK tl tl (t % 231) (t / 231)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 231 % 77) * 282) (x2Tab o (t / 231 / 77) (t % 231))) (x2Tab t3 (t / 231) (t % 231)))) 5032 8 chkC_3_d5032) (x2c_join _ 5040 5048 6400 (x2c_range_all (fun t => (!(pOK tl tl (t % 231) (t / 231)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 231 % 77) * 282) (x2Tab o (t / 231 / 77) (t % 231))) (x2Tab t3 (t / 231) (t % 231)))) 5040 8 chkC_3_d5040) (x2c_join _ 5048 5056 6400 (x2c_range_all (fun t => (!(pOK tl tl (t % 231) (t / 231)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 231 % 77) * 282) (x2Tab o (t / 231 / 77) (t % 231))) (x2Tab t3 (t / 231) (t % 231)))) 5048 8 chkC_3_d5048) (x2c_join _ 5056 5064 6400 (x2c_range_all (fun t => (!(pOK tl tl (t % 231) (t / 231)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 231 % 77) * 282) (x2Tab o (t / 231 / 77) (t % 231))) (x2Tab t3 (t / 231) (t % 231)))) 5056 8 chkC_3_d5056) (x2c_join _ 5064 5072 6400 (x2c_range_all (fun t => (!(pOK tl tl (t % 231) (t / 231)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 231 % 77) * 282) (x2Tab o (t / 231 / 77) (t % 231))) (x2Tab t3 (t / 231) (t % 231)))) 5064 8 chkC_3_d5064) (x2c_join _ 5072 5080 6400 (x2c_range_all (fun t => (!(pOK tl tl (t % 231) (t / 231)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 231 % 77) * 282) (x2Tab o (t / 231 / 77) (t % 231))) (x2Tab t3 (t / 231) (t % 231)))) 5072 8 chkC_3_d5072) (x2c_join _ 5080 5088 6400 (x2c_range_all (fun t => (!(pOK tl tl (t % 231) (t / 231)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 231 % 77) * 282) (x2Tab o (t / 231 / 77) (t % 231))) (x2Tab t3 (t / 231) (t % 231)))) 5080 8 chkC_3_d5080) (x2c_join _ 5088 5096 6400 (x2c_range_all (fun t => (!(pOK tl tl (t % 231) (t / 231)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 231 % 77) * 282) (x2Tab o (t / 231 / 77) (t % 231))) (x2Tab t3 (t / 231) (t % 231)))) 5088 8 chkC_3_d5088) (x2c_join _ 5096 5104 6400 (x2c_range_all (fun t => (!(pOK tl tl (t % 231) (t / 231)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 231 % 77) * 282) (x2Tab o (t / 231 / 77) (t % 231))) (x2Tab t3 (t / 231) (t % 231)))) 5096 8 chkC_3_d5096) (x2c_join _ 5104 5112 6400 (x2c_range_all (fun t => (!(pOK tl tl (t % 231) (t / 231)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 231 % 77) * 282) (x2Tab o (t / 231 / 77) (t % 231))) (x2Tab t3 (t / 231) (t % 231)))) 5104 8 chkC_3_d5104) (x2c_join _ 5112 5120 6400 (x2c_range_all (fun t => (!(pOK tl tl (t % 231) (t / 231)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 231 % 77) * 282) (x2Tab o (t / 231 / 77) (t % 231))) (x2Tab t3 (t / 231) (t % 231)))) 5112 8 chkC_3_d5112) (x2c_join _ 5120 5128 6400 (x2c_range_all (fun t => (!(pOK tl tl (t % 231) (t / 231)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 231 % 77) * 282) (x2Tab o (t / 231 / 77) (t % 231))) (x2Tab t3 (t / 231) (t % 231)))) 5120 8 chkC_3_d5120) (x2c_join _ 5128 5136 6400 (x2c_range_all (fun t => (!(pOK tl tl (t % 231) (t / 231)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 231 % 77) * 282) (x2Tab o (t / 231 / 77) (t % 231))) (x2Tab t3 (t / 231) (t % 231)))) 5128 8 chkC_3_d5128) (x2c_join _ 5136 5144 6400 (x2c_range_all (fun t => (!(pOK tl tl (t % 231) (t / 231)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 231 % 77) * 282) (x2Tab o (t / 231 / 77) (t % 231))) (x2Tab t3 (t / 231) (t % 231)))) 5136 8 chkC_3_d5136) (x2c_join _ 5144 5152 6400 (x2c_range_all (fun t => (!(pOK tl tl (t % 231) (t / 231)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 231 % 77) * 282) (x2Tab o (t / 231 / 77) (t % 231))) (x2Tab t3 (t / 231) (t % 231)))) 5144 8 chkC_3_d5144) (x2c_join _ 5152 5160 6400 (x2c_range_all (fun t => (!(pOK tl tl (t % 231) (t / 231)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 231 % 77) * 282) (x2Tab o (t / 231 / 77) (t % 231))) (x2Tab t3 (t / 231) (t % 231)))) 5152 8 chkC_3_d5152) (x2c_join _ 5160 5168 6400 (x2c_range_all (fun t => (!(pOK tl tl (t % 231) (t / 231)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 231 % 77) * 282) (x2Tab o (t / 231 / 77) (t % 231))) (x2Tab t3 (t / 231) (t % 231)))) 5160 8 chkC_3_d5160) (x2c_join _ 5168 5176 6400 (x2c_range_all (fun t => (!(pOK tl tl (t % 231) (t / 231)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 231 % 77) * 282) (x2Tab o (t / 231 / 77) (t % 231))) (x2Tab t3 (t / 231) (t % 231)))) 5168 8 chkC_3_d5168) (x2c_join _ 5176 5184 6400 (x2c_range_all (fun t => (!(pOK tl tl (t % 231) (t / 231)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 231 % 77) * 282) (x2Tab o (t / 231 / 77) (t % 231))) (x2Tab t3 (t / 231) (t % 231)))) 5176 8 chkC_3_d5176) (x2c_join _ 5184 5192 6400 (x2c_range_all (fun t => (!(pOK tl tl (t % 231) (t / 231)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 231 % 77) * 282) (x2Tab o (t / 231 / 77) (t % 231))) (x2Tab t3 (t / 231) (t % 231)))) 5184 8 chkC_3_d5184) (x2c_join _ 5192 5200 6400 (x2c_range_all (fun t => (!(pOK tl tl (t % 231) (t / 231)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 231 % 77) * 282) (x2Tab o (t / 231 / 77) (t % 231))) (x2Tab t3 (t / 231) (t % 231)))) 5192 8 chkC_3_d5192) (x2c_join _ 5200 5208 6400 (x2c_range_all (fun t => (!(pOK tl tl (t % 231) (t / 231)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 231 % 77) * 282) (x2Tab o (t / 231 / 77) (t % 231))) (x2Tab t3 (t / 231) (t % 231)))) 5200 8 chkC_3_d5200) (x2c_join _ 5208 5216 6400 (x2c_range_all (fun t => (!(pOK tl tl (t % 231) (t / 231)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 231 % 77) * 282) (x2Tab o (t / 231 / 77) (t % 231))) (x2Tab t3 (t / 231) (t % 231)))) 5208 8 chkC_3_d5208) (x2c_join _ 5216 5224 6400 (x2c_range_all (fun t => (!(pOK tl tl (t % 231) (t / 231)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 231 % 77) * 282) (x2Tab o (t / 231 / 77) (t % 231))) (x2Tab t3 (t / 231) (t % 231)))) 5216 8 chkC_3_d5216) (x2c_join _ 5224 5232 6400 (x2c_range_all (fun t => (!(pOK tl tl (t % 231) (t / 231)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 231 % 77) * 282) (x2Tab o (t / 231 / 77) (t % 231))) (x2Tab t3 (t / 231) (t % 231)))) 5224 8 chkC_3_d5224) (x2c_join _ 5232 5240 6400 (x2c_range_all (fun t => (!(pOK tl tl (t % 231) (t / 231)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 231 % 77) * 282) (x2Tab o (t / 231 / 77) (t % 231))) (x2Tab t3 (t / 231) (t % 231)))) 5232 8 chkC_3_d5232) (x2c_join _ 5240 5248 6400 (x2c_range_all (fun t => (!(pOK tl tl (t % 231) (t / 231)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 231 % 77) * 282) (x2Tab o (t / 231 / 77) (t % 231))) (x2Tab t3 (t / 231) (t % 231)))) 5240 8 chkC_3_d5240) (x2c_join _ 5248 5256 6400 (x2c_range_all (fun t => (!(pOK tl tl (t % 231) (t / 231)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 231 % 77) * 282) (x2Tab o (t / 231 / 77) (t % 231))) (x2Tab t3 (t / 231) (t % 231)))) 5248 8 chkC_3_d5248) (x2c_join _ 5256 5264 6400 (x2c_range_all (fun t => (!(pOK tl tl (t % 231) (t / 231)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 231 % 77) * 282) (x2Tab o (t / 231 / 77) (t % 231))) (x2Tab t3 (t / 231) (t % 231)))) 5256 8 chkC_3_d5256) (x2c_join _ 5264 5272 6400 (x2c_range_all (fun t => (!(pOK tl tl (t % 231) (t / 231)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 231 % 77) * 282) (x2Tab o (t / 231 / 77) (t % 231))) (x2Tab t3 (t / 231) (t % 231)))) 5264 8 chkC_3_d5264) (x2c_join _ 5272 5280 6400 (x2c_range_all (fun t => (!(pOK tl tl (t % 231) (t / 231)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 231 % 77) * 282) (x2Tab o (t / 231 / 77) (t % 231))) (x2Tab t3 (t / 231) (t % 231)))) 5272 8 chkC_3_d5272) (x2c_join _ 5280 5288 6400 (x2c_range_all (fun t => (!(pOK tl tl (t % 231) (t / 231)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 231 % 77) * 282) (x2Tab o (t / 231 / 77) (t % 231))) (x2Tab t3 (t / 231) (t % 231)))) 5280 8 chkC_3_d5280) (x2c_join _ 5288 5296 6400 (x2c_range_all (fun t => (!(pOK tl tl (t % 231) (t / 231)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 231 % 77) * 282) (x2Tab o (t / 231 / 77) (t % 231))) (x2Tab t3 (t / 231) (t % 231)))) 5288 8 chkC_3_d5288) (x2c_join _ 5296 5304 6400 (x2c_range_all (fun t => (!(pOK tl tl (t % 231) (t / 231)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 231 % 77) * 282) (x2Tab o (t / 231 / 77) (t % 231))) (x2Tab t3 (t / 231) (t % 231)))) 5296 8 chkC_3_d5296) (x2c_join _ 5304 5312 6400 (x2c_range_all (fun t => (!(pOK tl tl (t % 231) (t / 231)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 231 % 77) * 282) (x2Tab o (t / 231 / 77) (t % 231))) (x2Tab t3 (t / 231) (t % 231)))) 5304 8 chkC_3_d5304) (x2c_join _ 5312 5320 6400 (x2c_range_all (fun t => (!(pOK tl tl (t % 231) (t / 231)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 231 % 77) * 282) (x2Tab o (t / 231 / 77) (t % 231))) (x2Tab t3 (t / 231) (t % 231)))) 5312 8 chkC_3_d5312) (x2c_join _ 5320 5328 6400 (x2c_range_all (fun t => (!(pOK tl tl (t % 231) (t / 231)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 231 % 77) * 282) (x2Tab o (t / 231 / 77) (t % 231))) (x2Tab t3 (t / 231) (t % 231)))) 5320 8 chkC_3_d5320) (x2c_join _ 5328 5336 6400 (x2c_range_all (fun t => (!(pOK tl tl (t % 231) (t / 231)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 231 % 77) * 282) (x2Tab o (t / 231 / 77) (t % 231))) (x2Tab t3 (t / 231) (t % 231)))) 5328 8 chkC_3_d5328) (x2c_join _ 5336 5344 6400 (x2c_range_all (fun t => (!(pOK tl tl (t % 231) (t / 231)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 231 % 77) * 282) (x2Tab o (t / 231 / 77) (t % 231))) (x2Tab t3 (t / 231) (t % 231)))) 5336 8 chkC_3_d5336) (x2c_join _ 5344 5352 6400 (x2c_range_all (fun t => (!(pOK tl tl (t % 231) (t / 231)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 231 % 77) * 282) (x2Tab o (t / 231 / 77) (t % 231))) (x2Tab t3 (t / 231) (t % 231)))) 5344 8 chkC_3_d5344) (x2c_join _ 5352 5360 6400 (x2c_range_all (fun t => (!(pOK tl tl (t % 231) (t / 231)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 231 % 77) * 282) (x2Tab o (t / 231 / 77) (t % 231))) (x2Tab t3 (t / 231) (t % 231)))) 5352 8 chkC_3_d5352) (x2c_join _ 5360 5368 6400 (x2c_range_all (fun t => (!(pOK tl tl (t % 231) (t / 231)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 231 % 77) * 282) (x2Tab o (t / 231 / 77) (t % 231))) (x2Tab t3 (t / 231) (t % 231)))) 5360 8 chkC_3_d5360) (x2c_join _ 5368 5376 6400 (x2c_range_all (fun t => (!(pOK tl tl (t % 231) (t / 231)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 231 % 77) * 282) (x2Tab o (t / 231 / 77) (t % 231))) (x2Tab t3 (t / 231) (t % 231)))) 5368 8 chkC_3_d5368) (x2c_join _ 5376 5384 6400 (x2c_range_all (fun t => (!(pOK tl tl (t % 231) (t / 231)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 231 % 77) * 282) (x2Tab o (t / 231 / 77) (t % 231))) (x2Tab t3 (t / 231) (t % 231)))) 5376 8 chkC_3_d5376) (x2c_join _ 5384 5392 6400 (x2c_range_all (fun t => (!(pOK tl tl (t % 231) (t / 231)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 231 % 77) * 282) (x2Tab o (t / 231 / 77) (t % 231))) (x2Tab t3 (t / 231) (t % 231)))) 5384 8 chkC_3_d5384) (x2c_join _ 5392 5400 6400 (x2c_range_all (fun t => (!(pOK tl tl (t % 231) (t / 231)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 231 % 77) * 282) (x2Tab o (t / 231 / 77) (t % 231))) (x2Tab t3 (t / 231) (t % 231)))) 5392 8 chkC_3_d5392) (x2c_join _ 5400 5408 6400 (x2c_range_all (fun t => (!(pOK tl tl (t % 231) (t / 231)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 231 % 77) * 282) (x2Tab o (t / 231 / 77) (t % 231))) (x2Tab t3 (t / 231) (t % 231)))) 5400 8 chkC_3_d5400) (x2c_join _ 5408 5416 6400 (x2c_range_all (fun t => (!(pOK tl tl (t % 231) (t / 231)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 231 % 77) * 282) (x2Tab o (t / 231 / 77) (t % 231))) (x2Tab t3 (t / 231) (t % 231)))) 5408 8 chkC_3_d5408) (x2c_join _ 5416 5424 6400 (x2c_range_all (fun t => (!(pOK tl tl (t % 231) (t / 231)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 231 % 77) * 282) (x2Tab o (t / 231 / 77) (t % 231))) (x2Tab t3 (t / 231) (t % 231)))) 5416 8 chkC_3_d5416) (x2c_join _ 5424 5432 6400 (x2c_range_all (fun t => (!(pOK tl tl (t % 231) (t / 231)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 231 % 77) * 282) (x2Tab o (t / 231 / 77) (t % 231))) (x2Tab t3 (t / 231) (t % 231)))) 5424 8 chkC_3_d5424) (x2c_join _ 5432 5440 6400 (x2c_range_all (fun t => (!(pOK tl tl (t % 231) (t / 231)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 231 % 77) * 282) (x2Tab o (t / 231 / 77) (t % 231))) (x2Tab t3 (t / 231) (t % 231)))) 5432 8 chkC_3_d5432) (x2c_join _ 5440 5448 6400 (x2c_range_all (fun t => (!(pOK tl tl (t % 231) (t / 231)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 231 % 77) * 282) (x2Tab o (t / 231 / 77) (t % 231))) (x2Tab t3 (t / 231) (t % 231)))) 5440 8 chkC_3_d5440) (x2c_join _ 5448 5456 6400 (x2c_range_all (fun t => (!(pOK tl tl (t % 231) (t / 231)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 231 % 77) * 282) (x2Tab o (t / 231 / 77) (t % 231))) (x2Tab t3 (t / 231) (t % 231)))) 5448 8 chkC_3_d5448) (x2c_join _ 5456 5464 6400 (x2c_range_all (fun t => (!(pOK tl tl (t % 231) (t / 231)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 231 % 77) * 282) (x2Tab o (t / 231 / 77) (t % 231))) (x2Tab t3 (t / 231) (t % 231)))) 5456 8 chkC_3_d5456) (x2c_join _ 5464 5472 6400 (x2c_range_all (fun t => (!(pOK tl tl (t % 231) (t / 231)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 231 % 77) * 282) (x2Tab o (t / 231 / 77) (t % 231))) (x2Tab t3 (t / 231) (t % 231)))) 5464 8 chkC_3_d5464) (x2c_join _ 5472 5480 6400 (x2c_range_all (fun t => (!(pOK tl tl (t % 231) (t / 231)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 231 % 77) * 282) (x2Tab o (t / 231 / 77) (t % 231))) (x2Tab t3 (t / 231) (t % 231)))) 5472 8 chkC_3_d5472) (x2c_join _ 5480 5488 6400 (x2c_range_all (fun t => (!(pOK tl tl (t % 231) (t / 231)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 231 % 77) * 282) (x2Tab o (t / 231 / 77) (t % 231))) (x2Tab t3 (t / 231) (t % 231)))) 5480 8 chkC_3_d5480) (x2c_join _ 5488 5496 6400 (x2c_range_all (fun t => (!(pOK tl tl (t % 231) (t / 231)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 231 % 77) * 282) (x2Tab o (t / 231 / 77) (t % 231))) (x2Tab t3 (t / 231) (t % 231)))) 5488 8 chkC_3_d5488) (x2c_join _ 5496 5504 6400 (x2c_range_all (fun t => (!(pOK tl tl (t % 231) (t / 231)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 231 % 77) * 282) (x2Tab o (t / 231 / 77) (t % 231))) (x2Tab t3 (t / 231) (t % 231)))) 5496 8 chkC_3_d5496) (x2c_join _ 5504 5512 6400 (x2c_range_all (fun t => (!(pOK tl tl (t % 231) (t / 231)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 231 % 77) * 282) (x2Tab o (t / 231 / 77) (t % 231))) (x2Tab t3 (t / 231) (t % 231)))) 5504 8 chkC_3_d5504) (x2c_join _ 5512 5520 6400 (x2c_range_all (fun t => (!(pOK tl tl (t % 231) (t / 231)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 231 % 77) * 282) (x2Tab o (t / 231 / 77) (t % 231))) (x2Tab t3 (t / 231) (t % 231)))) 5512 8 chkC_3_d5512) (x2c_join _ 5520 5528 6400 (x2c_range_all (fun t => (!(pOK tl tl (t % 231) (t / 231)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 231 % 77) * 282) (x2Tab o (t / 231 / 77) (t % 231))) (x2Tab t3 (t / 231) (t % 231)))) 5520 8 chkC_3_d5520) (x2c_join _ 5528 5536 6400 (x2c_range_all (fun t => (!(pOK tl tl (t % 231) (t / 231)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 231 % 77) * 282) (x2Tab o (t / 231 / 77) (t % 231))) (x2Tab t3 (t / 231) (t % 231)))) 5528 8 chkC_3_d5528) (x2c_join _ 5536 5544 6400 (x2c_range_all (fun t => (!(pOK tl tl (t % 231) (t / 231)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 231 % 77) * 282) (x2Tab o (t / 231 / 77) (t % 231))) (x2Tab t3 (t / 231) (t % 231)))) 5536 8 chkC_3_d5536) (x2c_join _ 5544 5552 6400 (x2c_range_all (fun t => (!(pOK tl tl (t % 231) (t / 231)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 231 % 77) * 282) (x2Tab o (t / 231 / 77) (t % 231))) (x2Tab t3 (t / 231) (t % 231)))) 5544 8 chkC_3_d5544) (x2c_join _ 5552 5560 6400 (x2c_range_all (fun t => (!(pOK tl tl (t % 231) (t / 231)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 231 % 77) * 282) (x2Tab o (t / 231 / 77) (t % 231))) (x2Tab t3 (t / 231) (t % 231)))) 5552 8 chkC_3_d5552) (x2c_join _ 5560 5568 6400 (x2c_range_all (fun t => (!(pOK tl tl (t % 231) (t / 231)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 231 % 77) * 282) (x2Tab o (t / 231 / 77) (t % 231))) (x2Tab t3 (t / 231) (t % 231)))) 5560 8 chkC_3_d5560) (x2c_join _ 5568 5576 6400 (x2c_range_all (fun t => (!(pOK tl tl (t % 231) (t / 231)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 231 % 77) * 282) (x2Tab o (t / 231 / 77) (t % 231))) (x2Tab t3 (t / 231) (t % 231)))) 5568 8 chkC_3_d5568) (x2c_join _ 5576 5584 6400 (x2c_range_all (fun t => (!(pOK tl tl (t % 231) (t / 231)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 231 % 77) * 282) (x2Tab o (t / 231 / 77) (t % 231))) (x2Tab t3 (t / 231) (t % 231)))) 5576 8 chkC_3_d5576) (x2c_join _ 5584 5592 6400 (x2c_range_all (fun t => (!(pOK tl tl (t % 231) (t / 231)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 231 % 77) * 282) (x2Tab o (t / 231 / 77) (t % 231))) (x2Tab t3 (t / 231) (t % 231)))) 5584 8 chkC_3_d5584) (x2c_join _ 5592 5600 6400 (x2c_range_all (fun t => (!(pOK tl tl (t % 231) (t / 231)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 231 % 77) * 282) (x2Tab o (t / 231 / 77) (t % 231))) (x2Tab t3 (t / 231) (t % 231)))) 5592 8 chkC_3_d5592) (x2c_join _ 5600 5608 6400 (x2c_range_all (fun t => (!(pOK tl tl (t % 231) (t / 231)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 231 % 77) * 282) (x2Tab o (t / 231 / 77) (t % 231))) (x2Tab t3 (t / 231) (t % 231)))) 5600 8 chkC_3_d5600) (x2c_join _ 5608 5616 6400 (x2c_range_all (fun t => (!(pOK tl tl (t % 231) (t / 231)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 231 % 77) * 282) (x2Tab o (t / 231 / 77) (t % 231))) (x2Tab t3 (t / 231) (t % 231)))) 5608 8 chkC_3_d5608) (x2c_join _ 5616 5624 6400 (x2c_range_all (fun t => (!(pOK tl tl (t % 231) (t / 231)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 231 % 77) * 282) (x2Tab o (t / 231 / 77) (t % 231))) (x2Tab t3 (t / 231) (t % 231)))) 5616 8 chkC_3_d5616) (x2c_join _ 5624 5632 6400 (x2c_range_all (fun t => (!(pOK tl tl (t % 231) (t / 231)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 231 % 77) * 282) (x2Tab o (t / 231 / 77) (t % 231))) (x2Tab t3 (t / 231) (t % 231)))) 5624 8 chkC_3_d5624) (x2c_join _ 5632 5640 6400 (x2c_range_all (fun t => (!(pOK tl tl (t % 231) (t / 231)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 231 % 77) * 282) (x2Tab o (t / 231 / 77) (t % 231))) (x2Tab t3 (t / 231) (t % 231)))) 5632 8 chkC_3_d5632) (x2c_join _ 5640 5648 6400 (x2c_range_all (fun t => (!(pOK tl tl (t % 231) (t / 231)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 231 % 77) * 282) (x2Tab o (t / 231 / 77) (t % 231))) (x2Tab t3 (t / 231) (t % 231)))) 5640 8 chkC_3_d5640) (x2c_join _ 5648 5656 6400 (x2c_range_all (fun t => (!(pOK tl tl (t % 231) (t / 231)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 231 % 77) * 282) (x2Tab o (t / 231 / 77) (t % 231))) (x2Tab t3 (t / 231) (t % 231)))) 5648 8 chkC_3_d5648) (x2c_join _ 5656 5664 6400 (x2c_range_all (fun t => (!(pOK tl tl (t % 231) (t / 231)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 231 % 77) * 282) (x2Tab o (t / 231 / 77) (t % 231))) (x2Tab t3 (t / 231) (t % 231)))) 5656 8 chkC_3_d5656) (x2c_join _ 5664 5672 6400 (x2c_range_all (fun t => (!(pOK tl tl (t % 231) (t / 231)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 231 % 77) * 282) (x2Tab o (t / 231 / 77) (t % 231))) (x2Tab t3 (t / 231) (t % 231)))) 5664 8 chkC_3_d5664) (x2c_join _ 5672 5680 6400 (x2c_range_all (fun t => (!(pOK tl tl (t % 231) (t / 231)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 231 % 77) * 282) (x2Tab o (t / 231 / 77) (t % 231))) (x2Tab t3 (t / 231) (t % 231)))) 5672 8 chkC_3_d5672) (x2c_join _ 5680 5688 6400 (x2c_range_all (fun t => (!(pOK tl tl (t % 231) (t / 231)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 231 % 77) * 282) (x2Tab o (t / 231 / 77) (t % 231))) (x2Tab t3 (t / 231) (t % 231)))) 5680 8 chkC_3_d5680) (x2c_join _ 5688 5696 6400 (x2c_range_all (fun t => (!(pOK tl tl (t % 231) (t / 231)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 231 % 77) * 282) (x2Tab o (t / 231 / 77) (t % 231))) (x2Tab t3 (t / 231) (t % 231)))) 5688 8 chkC_3_d5688) (x2c_join _ 5696 5704 6400 (x2c_range_all (fun t => (!(pOK tl tl (t % 231) (t / 231)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 231 % 77) * 282) (x2Tab o (t / 231 / 77) (t % 231))) (x2Tab t3 (t / 231) (t % 231)))) 5696 8 chkC_3_d5696) (x2c_join _ 5704 5712 6400 (x2c_range_all (fun t => (!(pOK tl tl (t % 231) (t / 231)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 231 % 77) * 282) (x2Tab o (t / 231 / 77) (t % 231))) (x2Tab t3 (t / 231) (t % 231)))) 5704 8 chkC_3_d5704) (x2c_join _ 5712 5720 6400 (x2c_range_all (fun t => (!(pOK tl tl (t % 231) (t / 231)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 231 % 77) * 282) (x2Tab o (t / 231 / 77) (t % 231))) (x2Tab t3 (t / 231) (t % 231)))) 5712 8 chkC_3_d5712) (x2c_join _ 5720 5728 6400 (x2c_range_all (fun t => (!(pOK tl tl (t % 231) (t / 231)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 231 % 77) * 282) (x2Tab o (t / 231 / 77) (t % 231))) (x2Tab t3 (t / 231) (t % 231)))) 5720 8 chkC_3_d5720) (x2c_join _ 5728 5736 6400 (x2c_range_all (fun t => (!(pOK tl tl (t % 231) (t / 231)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 231 % 77) * 282) (x2Tab o (t / 231 / 77) (t % 231))) (x2Tab t3 (t / 231) (t % 231)))) 5728 8 chkC_3_d5728) (x2c_join _ 5736 5744 6400 (x2c_range_all (fun t => (!(pOK tl tl (t % 231) (t / 231)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 231 % 77) * 282) (x2Tab o (t / 231 / 77) (t % 231))) (x2Tab t3 (t / 231) (t % 231)))) 5736 8 chkC_3_d5736) (x2c_join _ 5744 5752 6400 (x2c_range_all (fun t => (!(pOK tl tl (t % 231) (t / 231)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 231 % 77) * 282) (x2Tab o (t / 231 / 77) (t % 231))) (x2Tab t3 (t / 231) (t % 231)))) 5744 8 chkC_3_d5744) (x2c_join _ 5752 5760 6400 (x2c_range_all (fun t => (!(pOK tl tl (t % 231) (t / 231)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 231 % 77) * 282) (x2Tab o (t / 231 / 77) (t % 231))) (x2Tab t3 (t / 231) (t % 231)))) 5752 8 chkC_3_d5752) (x2c_join _ 5760 5768 6400 (x2c_range_all (fun t => (!(pOK tl tl (t % 231) (t / 231)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 231 % 77) * 282) (x2Tab o (t / 231 / 77) (t % 231))) (x2Tab t3 (t / 231) (t % 231)))) 5760 8 chkC_3_d5760) (x2c_join _ 5768 5776 6400 (x2c_range_all (fun t => (!(pOK tl tl (t % 231) (t / 231)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 231 % 77) * 282) (x2Tab o (t / 231 / 77) (t % 231))) (x2Tab t3 (t / 231) (t % 231)))) 5768 8 chkC_3_d5768) (x2c_join _ 5776 5784 6400 (x2c_range_all (fun t => (!(pOK tl tl (t % 231) (t / 231)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 231 % 77) * 282) (x2Tab o (t / 231 / 77) (t % 231))) (x2Tab t3 (t / 231) (t % 231)))) 5776 8 chkC_3_d5776) (x2c_join _ 5784 5792 6400 (x2c_range_all (fun t => (!(pOK tl tl (t % 231) (t / 231)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 231 % 77) * 282) (x2Tab o (t / 231 / 77) (t % 231))) (x2Tab t3 (t / 231) (t % 231)))) 5784 8 chkC_3_d5784) (x2c_join _ 5792 5800 6400 (x2c_range_all (fun t => (!(pOK tl tl (t % 231) (t / 231)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 231 % 77) * 282) (x2Tab o (t / 231 / 77) (t % 231))) (x2Tab t3 (t / 231) (t % 231)))) 5792 8 chkC_3_d5792) (x2c_join _ 5800 5808 6400 (x2c_range_all (fun t => (!(pOK tl tl (t % 231) (t / 231)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 231 % 77) * 282) (x2Tab o (t / 231 / 77) (t % 231))) (x2Tab t3 (t / 231) (t % 231)))) 5800 8 chkC_3_d5800) (x2c_join _ 5808 5816 6400 (x2c_range_all (fun t => (!(pOK tl tl (t % 231) (t / 231)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 231 % 77) * 282) (x2Tab o (t / 231 / 77) (t % 231))) (x2Tab t3 (t / 231) (t % 231)))) 5808 8 chkC_3_d5808) (x2c_join _ 5816 5824 6400 (x2c_range_all (fun t => (!(pOK tl tl (t % 231) (t / 231)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 231 % 77) * 282) (x2Tab o (t / 231 / 77) (t % 231))) (x2Tab t3 (t / 231) (t % 231)))) 5816 8 chkC_3_d5816) (x2c_join _ 5824 5832 6400 (x2c_range_all (fun t => (!(pOK tl tl (t % 231) (t / 231)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 231 % 77) * 282) (x2Tab o (t / 231 / 77) (t % 231))) (x2Tab t3 (t / 231) (t % 231)))) 5824 8 chkC_3_d5824) (x2c_join _ 5832 5840 6400 (x2c_range_all (fun t => (!(pOK tl tl (t % 231) (t / 231)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 231 % 77) * 282) (x2Tab o (t / 231 / 77) (t % 231))) (x2Tab t3 (t / 231) (t % 231)))) 5832 8 chkC_3_d5832) (x2c_join _ 5840 5848 6400 (x2c_range_all (fun t => (!(pOK tl tl (t % 231) (t / 231)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 231 % 77) * 282) (x2Tab o (t / 231 / 77) (t % 231))) (x2Tab t3 (t / 231) (t % 231)))) 5840 8 chkC_3_d5840) (x2c_join _ 5848 5856 6400 (x2c_range_all (fun t => (!(pOK tl tl (t % 231) (t / 231)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 231 % 77) * 282) (x2Tab o (t / 231 / 77) (t % 231))) (x2Tab t3 (t / 231) (t % 231)))) 5848 8 chkC_3_d5848) (x2c_join _ 5856 5864 6400 (x2c_range_all (fun t => (!(pOK tl tl (t % 231) (t / 231)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 231 % 77) * 282) (x2Tab o (t / 231 / 77) (t % 231))) (x2Tab t3 (t / 231) (t % 231)))) 5856 8 chkC_3_d5856) (x2c_join _ 5864 5872 6400 (x2c_range_all (fun t => (!(pOK tl tl (t % 231) (t / 231)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 231 % 77) * 282) (x2Tab o (t / 231 / 77) (t % 231))) (x2Tab t3 (t / 231) (t % 231)))) 5864 8 chkC_3_d5864) (x2c_join _ 5872 5880 6400 (x2c_range_all (fun t => (!(pOK tl tl (t % 231) (t / 231)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 231 % 77) * 282) (x2Tab o (t / 231 / 77) (t % 231))) (x2Tab t3 (t / 231) (t % 231)))) 5872 8 chkC_3_d5872) (x2c_join _ 5880 5888 6400 (x2c_range_all (fun t => (!(pOK tl tl (t % 231) (t / 231)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 231 % 77) * 282) (x2Tab o (t / 231 / 77) (t % 231))) (x2Tab t3 (t / 231) (t % 231)))) 5880 8 chkC_3_d5880) (x2c_join _ 5888 5896 6400 (x2c_range_all (fun t => (!(pOK tl tl (t % 231) (t / 231)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 231 % 77) * 282) (x2Tab o (t / 231 / 77) (t % 231))) (x2Tab t3 (t / 231) (t % 231)))) 5888 8 chkC_3_d5888) (x2c_join _ 5896 5904 6400 (x2c_range_all (fun t => (!(pOK tl tl (t % 231) (t / 231)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 231 % 77) * 282) (x2Tab o (t / 231 / 77) (t % 231))) (x2Tab t3 (t / 231) (t % 231)))) 5896 8 chkC_3_d5896) (x2c_join _ 5904 5912 6400 (x2c_range_all (fun t => (!(pOK tl tl (t % 231) (t / 231)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 231 % 77) * 282) (x2Tab o (t / 231 / 77) (t % 231))) (x2Tab t3 (t / 231) (t % 231)))) 5904 8 chkC_3_d5904) (x2c_join _ 5912 5920 6400 (x2c_range_all (fun t => (!(pOK tl tl (t % 231) (t / 231)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 231 % 77) * 282) (x2Tab o (t / 231 / 77) (t % 231))) (x2Tab t3 (t / 231) (t % 231)))) 5912 8 chkC_3_d5912) (x2c_join _ 5920 5928 6400 (x2c_range_all (fun t => (!(pOK tl tl (t % 231) (t / 231)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 231 % 77) * 282) (x2Tab o (t / 231 / 77) (t % 231))) (x2Tab t3 (t / 231) (t % 231)))) 5920 8 chkC_3_d5920) (x2c_join _ 5928 5936 6400 (x2c_range_all (fun t => (!(pOK tl tl (t % 231) (t / 231)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 231 % 77) * 282) (x2Tab o (t / 231 / 77) (t % 231))) (x2Tab t3 (t / 231) (t % 231)))) 5928 8 chkC_3_d5928) (x2c_join _ 5936 5944 6400 (x2c_range_all (fun t => (!(pOK tl tl (t % 231) (t / 231)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 231 % 77) * 282) (x2Tab o (t / 231 / 77) (t % 231))) (x2Tab t3 (t / 231) (t % 231)))) 5936 8 chkC_3_d5936) (x2c_join _ 5944 5952 6400 (x2c_range_all (fun t => (!(pOK tl tl (t % 231) (t / 231)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 231 % 77) * 282) (x2Tab o (t / 231 / 77) (t % 231))) (x2Tab t3 (t / 231) (t % 231)))) 5944 8 chkC_3_d5944) (x2c_join _ 5952 5960 6400 (x2c_range_all (fun t => (!(pOK tl tl (t % 231) (t / 231)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 231 % 77) * 282) (x2Tab o (t / 231 / 77) (t % 231))) (x2Tab t3 (t / 231) (t % 231)))) 5952 8 chkC_3_d5952) (x2c_join _ 5960 5968 6400 (x2c_range_all (fun t => (!(pOK tl tl (t % 231) (t / 231)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 231 % 77) * 282) (x2Tab o (t / 231 / 77) (t % 231))) (x2Tab t3 (t / 231) (t % 231)))) 5960 8 chkC_3_d5960) (x2c_join _ 5968 5976 6400 (x2c_range_all (fun t => (!(pOK tl tl (t % 231) (t / 231)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 231 % 77) * 282) (x2Tab o (t / 231 / 77) (t % 231))) (x2Tab t3 (t / 231) (t % 231)))) 5968 8 chkC_3_d5968) (x2c_join _ 5976 5984 6400 (x2c_range_all (fun t => (!(pOK tl tl (t % 231) (t / 231)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 231 % 77) * 282) (x2Tab o (t / 231 / 77) (t % 231))) (x2Tab t3 (t / 231) (t % 231)))) 5976 8 chkC_3_d5976) (x2c_join _ 5984 5992 6400 (x2c_range_all (fun t => (!(pOK tl tl (t % 231) (t / 231)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 231 % 77) * 282) (x2Tab o (t / 231 / 77) (t % 231))) (x2Tab t3 (t / 231) (t % 231)))) 5984 8 chkC_3_d5984) (x2c_join _ 5992 6000 6400 (x2c_range_all (fun t => (!(pOK tl tl (t % 231) (t / 231)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 231 % 77) * 282) (x2Tab o (t / 231 / 77) (t % 231))) (x2Tab t3 (t / 231) (t % 231)))) 5992 8 chkC_3_d5992) (x2c_join _ 6000 6008 6400 (x2c_range_all (fun t => (!(pOK tl tl (t % 231) (t / 231)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 231 % 77) * 282) (x2Tab o (t / 231 / 77) (t % 231))) (x2Tab t3 (t / 231) (t % 231)))) 6000 8 chkC_3_d6000) (x2c_join _ 6008 6016 6400 (x2c_range_all (fun t => (!(pOK tl tl (t % 231) (t / 231)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 231 % 77) * 282) (x2Tab o (t / 231 / 77) (t % 231))) (x2Tab t3 (t / 231) (t % 231)))) 6008 8 chkC_3_d6008) (x2c_join _ 6016 6024 6400 (x2c_range_all (fun t => (!(pOK tl tl (t % 231) (t / 231)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 231 % 77) * 282) (x2Tab o (t / 231 / 77) (t % 231))) (x2Tab t3 (t / 231) (t % 231)))) 6016 8 chkC_3_d6016) (x2c_join _ 6024 6032 6400 (x2c_range_all (fun t => (!(pOK tl tl (t % 231) (t / 231)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 231 % 77) * 282) (x2Tab o (t / 231 / 77) (t % 231))) (x2Tab t3 (t / 231) (t % 231)))) 6024 8 chkC_3_d6024) (x2c_join _ 6032 6040 6400 (x2c_range_all (fun t => (!(pOK tl tl (t % 231) (t / 231)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 231 % 77) * 282) (x2Tab o (t / 231 / 77) (t % 231))) (x2Tab t3 (t / 231) (t % 231)))) 6032 8 chkC_3_d6032) (x2c_join _ 6040 6048 6400 (x2c_range_all (fun t => (!(pOK tl tl (t % 231) (t / 231)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 231 % 77) * 282) (x2Tab o (t / 231 / 77) (t % 231))) (x2Tab t3 (t / 231) (t % 231)))) 6040 8 chkC_3_d6040) (x2c_join _ 6048 6056 6400 (x2c_range_all (fun t => (!(pOK tl tl (t % 231) (t / 231)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 231 % 77) * 282) (x2Tab o (t / 231 / 77) (t % 231))) (x2Tab t3 (t / 231) (t % 231)))) 6048 8 chkC_3_d6048) (x2c_join _ 6056 6064 6400 (x2c_range_all (fun t => (!(pOK tl tl (t % 231) (t / 231)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 231 % 77) * 282) (x2Tab o (t / 231 / 77) (t % 231))) (x2Tab t3 (t / 231) (t % 231)))) 6056 8 chkC_3_d6056) (x2c_join _ 6064 6072 6400 (x2c_range_all (fun t => (!(pOK tl tl (t % 231) (t / 231)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 231 % 77) * 282) (x2Tab o (t / 231 / 77) (t % 231))) (x2Tab t3 (t / 231) (t % 231)))) 6064 8 chkC_3_d6064) (x2c_join _ 6072 6080 6400 (x2c_range_all (fun t => (!(pOK tl tl (t % 231) (t / 231)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 231 % 77) * 282) (x2Tab o (t / 231 / 77) (t % 231))) (x2Tab t3 (t / 231) (t % 231)))) 6072 8 chkC_3_d6072) (x2c_join _ 6080 6088 6400 (x2c_range_all (fun t => (!(pOK tl tl (t % 231) (t / 231)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 231 % 77) * 282) (x2Tab o (t / 231 / 77) (t % 231))) (x2Tab t3 (t / 231) (t % 231)))) 6080 8 chkC_3_d6080) (x2c_join _ 6088 6096 6400 (x2c_range_all (fun t => (!(pOK tl tl (t % 231) (t / 231)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 231 % 77) * 282) (x2Tab o (t / 231 / 77) (t % 231))) (x2Tab t3 (t / 231) (t % 231)))) 6088 8 chkC_3_d6088) (x2c_join _ 6096 6104 6400 (x2c_range_all (fun t => (!(pOK tl tl (t % 231) (t / 231)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 231 % 77) * 282) (x2Tab o (t / 231 / 77) (t % 231))) (x2Tab t3 (t / 231) (t % 231)))) 6096 8 chkC_3_d6096) (x2c_join _ 6104 6112 6400 (x2c_range_all (fun t => (!(pOK tl tl (t % 231) (t / 231)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 231 % 77) * 282) (x2Tab o (t / 231 / 77) (t % 231))) (x2Tab t3 (t / 231) (t % 231)))) 6104 8 chkC_3_d6104) (x2c_join _ 6112 6120 6400 (x2c_range_all (fun t => (!(pOK tl tl (t % 231) (t / 231)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 231 % 77) * 282) (x2Tab o (t / 231 / 77) (t % 231))) (x2Tab t3 (t / 231) (t % 231)))) 6112 8 chkC_3_d6112) (x2c_join _ 6120 6128 6400 (x2c_range_all (fun t => (!(pOK tl tl (t % 231) (t / 231)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 231 % 77) * 282) (x2Tab o (t / 231 / 77) (t % 231))) (x2Tab t3 (t / 231) (t % 231)))) 6120 8 chkC_3_d6120) (x2c_join _ 6128 6136 6400 (x2c_range_all (fun t => (!(pOK tl tl (t % 231) (t / 231)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 231 % 77) * 282) (x2Tab o (t / 231 / 77) (t % 231))) (x2Tab t3 (t / 231) (t % 231)))) 6128 8 chkC_3_d6128) (x2c_join _ 6136 6144 6400 (x2c_range_all (fun t => (!(pOK tl tl (t % 231) (t / 231)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 231 % 77) * 282) (x2Tab o (t / 231 / 77) (t % 231))) (x2Tab t3 (t / 231) (t % 231)))) 6136 8 chkC_3_d6136) (x2c_join _ 6144 6152 6400 (x2c_range_all (fun t => (!(pOK tl tl (t % 231) (t / 231)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 231 % 77) * 282) (x2Tab o (t / 231 / 77) (t % 231))) (x2Tab t3 (t / 231) (t % 231)))) 6144 8 chkC_3_d6144) (x2c_join _ 6152 6160 6400 (x2c_range_all (fun t => (!(pOK tl tl (t % 231) (t / 231)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 231 % 77) * 282) (x2Tab o (t / 231 / 77) (t % 231))) (x2Tab t3 (t / 231) (t % 231)))) 6152 8 chkC_3_d6152) (x2c_join _ 6160 6168 6400 (x2c_range_all (fun t => (!(pOK tl tl (t % 231) (t / 231)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 231 % 77) * 282) (x2Tab o (t / 231 / 77) (t % 231))) (x2Tab t3 (t / 231) (t % 231)))) 6160 8 chkC_3_d6160) (x2c_join _ 6168 6176 6400 (x2c_range_all (fun t => (!(pOK tl tl (t % 231) (t / 231)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 231 % 77) * 282) (x2Tab o (t / 231 / 77) (t % 231))) (x2Tab t3 (t / 231) (t % 231)))) 6168 8 chkC_3_d6168) (x2c_join _ 6176 6184 6400 (x2c_range_all (fun t => (!(pOK tl tl (t % 231) (t / 231)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 231 % 77) * 282) (x2Tab o (t / 231 / 77) (t % 231))) (x2Tab t3 (t / 231) (t % 231)))) 6176 8 chkC_3_d6176) (x2c_join _ 6184 6192 6400 (x2c_range_all (fun t => (!(pOK tl tl (t % 231) (t / 231)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 231 % 77) * 282) (x2Tab o (t / 231 / 77) (t % 231))) (x2Tab t3 (t / 231) (t % 231)))) 6184 8 chkC_3_d6184) (x2c_join _ 6192 6200 6400 (x2c_range_all (fun t => (!(pOK tl tl (t % 231) (t / 231)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 231 % 77) * 282) (x2Tab o (t / 231 / 77) (t % 231))) (x2Tab t3 (t / 231) (t % 231)))) 6192 8 chkC_3_d6192) (x2c_join _ 6200 6208 6400 (x2c_range_all (fun t => (!(pOK tl tl (t % 231) (t / 231)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 231 % 77) * 282) (x2Tab o (t / 231 / 77) (t % 231))) (x2Tab t3 (t / 231) (t % 231)))) 6200 8 chkC_3_d6200) (x2c_join _ 6208 6216 6400 (x2c_range_all (fun t => (!(pOK tl tl (t % 231) (t / 231)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 231 % 77) * 282) (x2Tab o (t / 231 / 77) (t % 231))) (x2Tab t3 (t / 231) (t % 231)))) 6208 8 chkC_3_d6208) (x2c_join _ 6216 6224 6400 (x2c_range_all (fun t => (!(pOK tl tl (t % 231) (t / 231)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 231 % 77) * 282) (x2Tab o (t / 231 / 77) (t % 231))) (x2Tab t3 (t / 231) (t % 231)))) 6216 8 chkC_3_d6216) (x2c_join _ 6224 6232 6400 (x2c_range_all (fun t => (!(pOK tl tl (t % 231) (t / 231)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 231 % 77) * 282) (x2Tab o (t / 231 / 77) (t % 231))) (x2Tab t3 (t / 231) (t % 231)))) 6224 8 chkC_3_d6224) (x2c_join _ 6232 6240 6400 (x2c_range_all (fun t => (!(pOK tl tl (t % 231) (t / 231)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 231 % 77) * 282) (x2Tab o (t / 231 / 77) (t % 231))) (x2Tab t3 (t / 231) (t % 231)))) 6232 8 chkC_3_d6232) (x2c_join _ 6240 6248 6400 (x2c_range_all (fun t => (!(pOK tl tl (t % 231) (t / 231)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 231 % 77) * 282) (x2Tab o (t / 231 / 77) (t % 231))) (x2Tab t3 (t / 231) (t % 231)))) 6240 8 chkC_3_d6240) (x2c_join _ 6248 6256 6400 (x2c_range_all (fun t => (!(pOK tl tl (t % 231) (t / 231)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 231 % 77) * 282) (x2Tab o (t / 231 / 77) (t % 231))) (x2Tab t3 (t / 231) (t % 231)))) 6248 8 chkC_3_d6248) (x2c_join _ 6256 6264 6400 (x2c_range_all (fun t => (!(pOK tl tl (t % 231) (t / 231)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 231 % 77) * 282) (x2Tab o (t / 231 / 77) (t % 231))) (x2Tab t3 (t / 231) (t % 231)))) 6256 8 chkC_3_d6256) (x2c_join _ 6264 6272 6400 (x2c_range_all (fun t => (!(pOK tl tl (t % 231) (t / 231)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 231 % 77) * 282) (x2Tab o (t / 231 / 77) (t % 231))) (x2Tab t3 (t / 231) (t % 231)))) 6264 8 chkC_3_d6264) (x2c_join _ 6272 6280 6400 (x2c_range_all (fun t => (!(pOK tl tl (t % 231) (t / 231)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 231 % 77) * 282) (x2Tab o (t / 231 / 77) (t % 231))) (x2Tab t3 (t / 231) (t % 231)))) 6272 8 chkC_3_d6272) (x2c_join _ 6280 6288 6400 (x2c_range_all (fun t => (!(pOK tl tl (t % 231) (t / 231)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 231 % 77) * 282) (x2Tab o (t / 231 / 77) (t % 231))) (x2Tab t3 (t / 231) (t % 231)))) 6280 8 chkC_3_d6280) (x2c_join _ 6288 6296 6400 (x2c_range_all (fun t => (!(pOK tl tl (t % 231) (t / 231)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 231 % 77) * 282) (x2Tab o (t / 231 / 77) (t % 231))) (x2Tab t3 (t / 231) (t % 231)))) 6288 8 chkC_3_d6288) (x2c_join _ 6296 6304 6400 (x2c_range_all (fun t => (!(pOK tl tl (t % 231) (t / 231)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 231 % 77) * 282) (x2Tab o (t / 231 / 77) (t % 231))) (x2Tab t3 (t / 231) (t % 231)))) 6296 8 chkC_3_d6296) (x2c_join _ 6304 6312 6400 (x2c_range_all (fun t => (!(pOK tl tl (t % 231) (t / 231)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 231 % 77) * 282) (x2Tab o (t / 231 / 77) (t % 231))) (x2Tab t3 (t / 231) (t % 231)))) 6304 8 chkC_3_d6304) (x2c_join _ 6312 6320 6400 (x2c_range_all (fun t => (!(pOK tl tl (t % 231) (t / 231)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 231 % 77) * 282) (x2Tab o (t / 231 / 77) (t % 231))) (x2Tab t3 (t / 231) (t % 231)))) 6312 8 chkC_3_d6312) (x2c_join _ 6320 6328 6400 (x2c_range_all (fun t => (!(pOK tl tl (t % 231) (t / 231)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 231 % 77) * 282) (x2Tab o (t / 231 / 77) (t % 231))) (x2Tab t3 (t / 231) (t % 231)))) 6320 8 chkC_3_d6320) (x2c_join _ 6328 6336 6400 (x2c_range_all (fun t => (!(pOK tl tl (t % 231) (t / 231)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 231 % 77) * 282) (x2Tab o (t / 231 / 77) (t % 231))) (x2Tab t3 (t / 231) (t % 231)))) 6328 8 chkC_3_d6328) (x2c_join _ 6336 6344 6400 (x2c_range_all (fun t => (!(pOK tl tl (t % 231) (t / 231)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 231 % 77) * 282) (x2Tab o (t / 231 / 77) (t % 231))) (x2Tab t3 (t / 231) (t % 231)))) 6336 8 chkC_3_d6336) (x2c_join _ 6344 6352 6400 (x2c_range_all (fun t => (!(pOK tl tl (t % 231) (t / 231)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 231 % 77) * 282) (x2Tab o (t / 231 / 77) (t % 231))) (x2Tab t3 (t / 231) (t % 231)))) 6344 8 chkC_3_d6344) (x2c_join _ 6352 6360 6400 (x2c_range_all (fun t => (!(pOK tl tl (t % 231) (t / 231)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 231 % 77) * 282) (x2Tab o (t / 231 / 77) (t % 231))) (x2Tab t3 (t / 231) (t % 231)))) 6352 8 chkC_3_d6352) (x2c_join _ 6360 6368 6400 (x2c_range_all (fun t => (!(pOK tl tl (t % 231) (t / 231)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 231 % 77) * 282) (x2Tab o (t / 231 / 77) (t % 231))) (x2Tab t3 (t / 231) (t % 231)))) 6360 8 chkC_3_d6360) (x2c_join _ 6368 6376 6400 (x2c_range_all (fun t => (!(pOK tl tl (t % 231) (t / 231)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 231 % 77) * 282) (x2Tab o (t / 231 / 77) (t % 231))) (x2Tab t3 (t / 231) (t % 231)))) 6368 8 chkC_3_d6368) (x2c_join _ 6376 6384 6400 (x2c_range_all (fun t => (!(pOK tl tl (t % 231) (t / 231)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 231 % 77) * 282) (x2Tab o (t / 231 / 77) (t % 231))) (x2Tab t3 (t / 231) (t % 231)))) 6376 8 chkC_3_d6376) (x2c_join _ 6384 6392 6400 (x2c_range_all (fun t => (!(pOK tl tl (t % 231) (t / 231)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 231 % 77) * 282) (x2Tab o (t / 231 / 77) (t % 231))) (x2Tab t3 (t / 231) (t % 231)))) 6384 8 chkC_3_d6384) (x2c_range_all (fun t => (!(pOK tl tl (t % 231) (t / 231)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 231 % 77) * 282) (x2Tab o (t / 231 / 77) (t % 231))) (x2Tab t3 (t / 231) (t % 231)))) 6392 8 chkC_3_d6392))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))


end ThreeCopyQutritWerner.X2.CoreA1g
