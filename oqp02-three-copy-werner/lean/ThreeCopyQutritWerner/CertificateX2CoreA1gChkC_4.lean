module

public import ThreeCopyQutritWerner.CertificateX2CoreA1gT3
public import ThreeCopyQutritWerner.CertificateX2Trans
public import ThreeCopyQutritWerner.CertificateX2CoreBatchGen
public import ThreeCopyQutritWerner.CertificateX2CoreBatchFlat

@[expose] public section


/-! Batched core A1g: axis-0 stage, selected pairs, flat indices 6400..7999. -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option exponentiation.threshold 1000000

namespace ThreeCopyQutritWerner.X2.CoreA1g
open ThreeCopyQutritWerner ThreeCopyQutritWerner.X2

theorem chkC_4_d6400 : (List.range' 6400 8).all (fun t => (!(pOK tl tl (t % 231) (t / 231)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 231 % 77) * 282) (x2Tab o (t / 231 / 77) (t % 231))) (x2Tab t3 (t / 231) (t % 231)))) = true := by
  decide +kernel

theorem chkC_4_d6408 : (List.range' 6408 8).all (fun t => (!(pOK tl tl (t % 231) (t / 231)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 231 % 77) * 282) (x2Tab o (t / 231 / 77) (t % 231))) (x2Tab t3 (t / 231) (t % 231)))) = true := by
  decide +kernel

theorem chkC_4_d6416 : (List.range' 6416 8).all (fun t => (!(pOK tl tl (t % 231) (t / 231)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 231 % 77) * 282) (x2Tab o (t / 231 / 77) (t % 231))) (x2Tab t3 (t / 231) (t % 231)))) = true := by
  decide +kernel

theorem chkC_4_d6424 : (List.range' 6424 8).all (fun t => (!(pOK tl tl (t % 231) (t / 231)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 231 % 77) * 282) (x2Tab o (t / 231 / 77) (t % 231))) (x2Tab t3 (t / 231) (t % 231)))) = true := by
  decide +kernel

theorem chkC_4_d6432 : (List.range' 6432 8).all (fun t => (!(pOK tl tl (t % 231) (t / 231)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 231 % 77) * 282) (x2Tab o (t / 231 / 77) (t % 231))) (x2Tab t3 (t / 231) (t % 231)))) = true := by
  decide +kernel

theorem chkC_4_d6440 : (List.range' 6440 8).all (fun t => (!(pOK tl tl (t % 231) (t / 231)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 231 % 77) * 282) (x2Tab o (t / 231 / 77) (t % 231))) (x2Tab t3 (t / 231) (t % 231)))) = true := by
  decide +kernel

theorem chkC_4_d6448 : (List.range' 6448 8).all (fun t => (!(pOK tl tl (t % 231) (t / 231)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 231 % 77) * 282) (x2Tab o (t / 231 / 77) (t % 231))) (x2Tab t3 (t / 231) (t % 231)))) = true := by
  decide +kernel

theorem chkC_4_d6456 : (List.range' 6456 8).all (fun t => (!(pOK tl tl (t % 231) (t / 231)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 231 % 77) * 282) (x2Tab o (t / 231 / 77) (t % 231))) (x2Tab t3 (t / 231) (t % 231)))) = true := by
  decide +kernel

theorem chkC_4_d6464 : (List.range' 6464 8).all (fun t => (!(pOK tl tl (t % 231) (t / 231)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 231 % 77) * 282) (x2Tab o (t / 231 / 77) (t % 231))) (x2Tab t3 (t / 231) (t % 231)))) = true := by
  decide +kernel

theorem chkC_4_d6472 : (List.range' 6472 8).all (fun t => (!(pOK tl tl (t % 231) (t / 231)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 231 % 77) * 282) (x2Tab o (t / 231 / 77) (t % 231))) (x2Tab t3 (t / 231) (t % 231)))) = true := by
  decide +kernel

theorem chkC_4_d6480 : (List.range' 6480 8).all (fun t => (!(pOK tl tl (t % 231) (t / 231)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 231 % 77) * 282) (x2Tab o (t / 231 / 77) (t % 231))) (x2Tab t3 (t / 231) (t % 231)))) = true := by
  decide +kernel

theorem chkC_4_d6488 : (List.range' 6488 8).all (fun t => (!(pOK tl tl (t % 231) (t / 231)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 231 % 77) * 282) (x2Tab o (t / 231 / 77) (t % 231))) (x2Tab t3 (t / 231) (t % 231)))) = true := by
  decide +kernel

theorem chkC_4_d6496 : (List.range' 6496 8).all (fun t => (!(pOK tl tl (t % 231) (t / 231)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 231 % 77) * 282) (x2Tab o (t / 231 / 77) (t % 231))) (x2Tab t3 (t / 231) (t % 231)))) = true := by
  decide +kernel

theorem chkC_4_d6504 : (List.range' 6504 8).all (fun t => (!(pOK tl tl (t % 231) (t / 231)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 231 % 77) * 282) (x2Tab o (t / 231 / 77) (t % 231))) (x2Tab t3 (t / 231) (t % 231)))) = true := by
  decide +kernel

theorem chkC_4_d6512 : (List.range' 6512 8).all (fun t => (!(pOK tl tl (t % 231) (t / 231)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 231 % 77) * 282) (x2Tab o (t / 231 / 77) (t % 231))) (x2Tab t3 (t / 231) (t % 231)))) = true := by
  decide +kernel

theorem chkC_4_d6520 : (List.range' 6520 8).all (fun t => (!(pOK tl tl (t % 231) (t / 231)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 231 % 77) * 282) (x2Tab o (t / 231 / 77) (t % 231))) (x2Tab t3 (t / 231) (t % 231)))) = true := by
  decide +kernel

theorem chkC_4_d6528 : (List.range' 6528 8).all (fun t => (!(pOK tl tl (t % 231) (t / 231)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 231 % 77) * 282) (x2Tab o (t / 231 / 77) (t % 231))) (x2Tab t3 (t / 231) (t % 231)))) = true := by
  decide +kernel

theorem chkC_4_d6536 : (List.range' 6536 8).all (fun t => (!(pOK tl tl (t % 231) (t / 231)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 231 % 77) * 282) (x2Tab o (t / 231 / 77) (t % 231))) (x2Tab t3 (t / 231) (t % 231)))) = true := by
  decide +kernel

theorem chkC_4_d6544 : (List.range' 6544 8).all (fun t => (!(pOK tl tl (t % 231) (t / 231)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 231 % 77) * 282) (x2Tab o (t / 231 / 77) (t % 231))) (x2Tab t3 (t / 231) (t % 231)))) = true := by
  decide +kernel

theorem chkC_4_d6552 : (List.range' 6552 8).all (fun t => (!(pOK tl tl (t % 231) (t / 231)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 231 % 77) * 282) (x2Tab o (t / 231 / 77) (t % 231))) (x2Tab t3 (t / 231) (t % 231)))) = true := by
  decide +kernel

theorem chkC_4_d6560 : (List.range' 6560 8).all (fun t => (!(pOK tl tl (t % 231) (t / 231)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 231 % 77) * 282) (x2Tab o (t / 231 / 77) (t % 231))) (x2Tab t3 (t / 231) (t % 231)))) = true := by
  decide +kernel

theorem chkC_4_d6568 : (List.range' 6568 8).all (fun t => (!(pOK tl tl (t % 231) (t / 231)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 231 % 77) * 282) (x2Tab o (t / 231 / 77) (t % 231))) (x2Tab t3 (t / 231) (t % 231)))) = true := by
  decide +kernel

theorem chkC_4_d6576 : (List.range' 6576 8).all (fun t => (!(pOK tl tl (t % 231) (t / 231)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 231 % 77) * 282) (x2Tab o (t / 231 / 77) (t % 231))) (x2Tab t3 (t / 231) (t % 231)))) = true := by
  decide +kernel

theorem chkC_4_d6584 : (List.range' 6584 8).all (fun t => (!(pOK tl tl (t % 231) (t / 231)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 231 % 77) * 282) (x2Tab o (t / 231 / 77) (t % 231))) (x2Tab t3 (t / 231) (t % 231)))) = true := by
  decide +kernel

theorem chkC_4_d6592 : (List.range' 6592 8).all (fun t => (!(pOK tl tl (t % 231) (t / 231)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 231 % 77) * 282) (x2Tab o (t / 231 / 77) (t % 231))) (x2Tab t3 (t / 231) (t % 231)))) = true := by
  decide +kernel

theorem chkC_4_d6600 : (List.range' 6600 8).all (fun t => (!(pOK tl tl (t % 231) (t / 231)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 231 % 77) * 282) (x2Tab o (t / 231 / 77) (t % 231))) (x2Tab t3 (t / 231) (t % 231)))) = true := by
  decide +kernel

theorem chkC_4_d6608 : (List.range' 6608 8).all (fun t => (!(pOK tl tl (t % 231) (t / 231)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 231 % 77) * 282) (x2Tab o (t / 231 / 77) (t % 231))) (x2Tab t3 (t / 231) (t % 231)))) = true := by
  decide +kernel

theorem chkC_4_d6616 : (List.range' 6616 8).all (fun t => (!(pOK tl tl (t % 231) (t / 231)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 231 % 77) * 282) (x2Tab o (t / 231 / 77) (t % 231))) (x2Tab t3 (t / 231) (t % 231)))) = true := by
  decide +kernel

theorem chkC_4_d6624 : (List.range' 6624 8).all (fun t => (!(pOK tl tl (t % 231) (t / 231)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 231 % 77) * 282) (x2Tab o (t / 231 / 77) (t % 231))) (x2Tab t3 (t / 231) (t % 231)))) = true := by
  decide +kernel

theorem chkC_4_d6632 : (List.range' 6632 8).all (fun t => (!(pOK tl tl (t % 231) (t / 231)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 231 % 77) * 282) (x2Tab o (t / 231 / 77) (t % 231))) (x2Tab t3 (t / 231) (t % 231)))) = true := by
  decide +kernel

theorem chkC_4_d6640 : (List.range' 6640 8).all (fun t => (!(pOK tl tl (t % 231) (t / 231)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 231 % 77) * 282) (x2Tab o (t / 231 / 77) (t % 231))) (x2Tab t3 (t / 231) (t % 231)))) = true := by
  decide +kernel

theorem chkC_4_d6648 : (List.range' 6648 8).all (fun t => (!(pOK tl tl (t % 231) (t / 231)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 231 % 77) * 282) (x2Tab o (t / 231 / 77) (t % 231))) (x2Tab t3 (t / 231) (t % 231)))) = true := by
  decide +kernel

theorem chkC_4_d6656 : (List.range' 6656 8).all (fun t => (!(pOK tl tl (t % 231) (t / 231)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 231 % 77) * 282) (x2Tab o (t / 231 / 77) (t % 231))) (x2Tab t3 (t / 231) (t % 231)))) = true := by
  decide +kernel

theorem chkC_4_d6664 : (List.range' 6664 8).all (fun t => (!(pOK tl tl (t % 231) (t / 231)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 231 % 77) * 282) (x2Tab o (t / 231 / 77) (t % 231))) (x2Tab t3 (t / 231) (t % 231)))) = true := by
  decide +kernel

theorem chkC_4_d6672 : (List.range' 6672 8).all (fun t => (!(pOK tl tl (t % 231) (t / 231)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 231 % 77) * 282) (x2Tab o (t / 231 / 77) (t % 231))) (x2Tab t3 (t / 231) (t % 231)))) = true := by
  decide +kernel

theorem chkC_4_d6680 : (List.range' 6680 8).all (fun t => (!(pOK tl tl (t % 231) (t / 231)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 231 % 77) * 282) (x2Tab o (t / 231 / 77) (t % 231))) (x2Tab t3 (t / 231) (t % 231)))) = true := by
  decide +kernel

theorem chkC_4_d6688 : (List.range' 6688 8).all (fun t => (!(pOK tl tl (t % 231) (t / 231)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 231 % 77) * 282) (x2Tab o (t / 231 / 77) (t % 231))) (x2Tab t3 (t / 231) (t % 231)))) = true := by
  decide +kernel

theorem chkC_4_d6696 : (List.range' 6696 8).all (fun t => (!(pOK tl tl (t % 231) (t / 231)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 231 % 77) * 282) (x2Tab o (t / 231 / 77) (t % 231))) (x2Tab t3 (t / 231) (t % 231)))) = true := by
  decide +kernel

theorem chkC_4_d6704 : (List.range' 6704 8).all (fun t => (!(pOK tl tl (t % 231) (t / 231)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 231 % 77) * 282) (x2Tab o (t / 231 / 77) (t % 231))) (x2Tab t3 (t / 231) (t % 231)))) = true := by
  decide +kernel

theorem chkC_4_d6712 : (List.range' 6712 8).all (fun t => (!(pOK tl tl (t % 231) (t / 231)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 231 % 77) * 282) (x2Tab o (t / 231 / 77) (t % 231))) (x2Tab t3 (t / 231) (t % 231)))) = true := by
  decide +kernel

theorem chkC_4_d6720 : (List.range' 6720 8).all (fun t => (!(pOK tl tl (t % 231) (t / 231)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 231 % 77) * 282) (x2Tab o (t / 231 / 77) (t % 231))) (x2Tab t3 (t / 231) (t % 231)))) = true := by
  decide +kernel

theorem chkC_4_d6728 : (List.range' 6728 8).all (fun t => (!(pOK tl tl (t % 231) (t / 231)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 231 % 77) * 282) (x2Tab o (t / 231 / 77) (t % 231))) (x2Tab t3 (t / 231) (t % 231)))) = true := by
  decide +kernel

theorem chkC_4_d6736 : (List.range' 6736 8).all (fun t => (!(pOK tl tl (t % 231) (t / 231)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 231 % 77) * 282) (x2Tab o (t / 231 / 77) (t % 231))) (x2Tab t3 (t / 231) (t % 231)))) = true := by
  decide +kernel

theorem chkC_4_d6744 : (List.range' 6744 8).all (fun t => (!(pOK tl tl (t % 231) (t / 231)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 231 % 77) * 282) (x2Tab o (t / 231 / 77) (t % 231))) (x2Tab t3 (t / 231) (t % 231)))) = true := by
  decide +kernel

theorem chkC_4_d6752 : (List.range' 6752 8).all (fun t => (!(pOK tl tl (t % 231) (t / 231)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 231 % 77) * 282) (x2Tab o (t / 231 / 77) (t % 231))) (x2Tab t3 (t / 231) (t % 231)))) = true := by
  decide +kernel

theorem chkC_4_d6760 : (List.range' 6760 8).all (fun t => (!(pOK tl tl (t % 231) (t / 231)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 231 % 77) * 282) (x2Tab o (t / 231 / 77) (t % 231))) (x2Tab t3 (t / 231) (t % 231)))) = true := by
  decide +kernel

theorem chkC_4_d6768 : (List.range' 6768 8).all (fun t => (!(pOK tl tl (t % 231) (t / 231)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 231 % 77) * 282) (x2Tab o (t / 231 / 77) (t % 231))) (x2Tab t3 (t / 231) (t % 231)))) = true := by
  decide +kernel

theorem chkC_4_d6776 : (List.range' 6776 8).all (fun t => (!(pOK tl tl (t % 231) (t / 231)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 231 % 77) * 282) (x2Tab o (t / 231 / 77) (t % 231))) (x2Tab t3 (t / 231) (t % 231)))) = true := by
  decide +kernel

theorem chkC_4_d6784 : (List.range' 6784 8).all (fun t => (!(pOK tl tl (t % 231) (t / 231)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 231 % 77) * 282) (x2Tab o (t / 231 / 77) (t % 231))) (x2Tab t3 (t / 231) (t % 231)))) = true := by
  decide +kernel

theorem chkC_4_d6792 : (List.range' 6792 8).all (fun t => (!(pOK tl tl (t % 231) (t / 231)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 231 % 77) * 282) (x2Tab o (t / 231 / 77) (t % 231))) (x2Tab t3 (t / 231) (t % 231)))) = true := by
  decide +kernel

theorem chkC_4_d6800 : (List.range' 6800 8).all (fun t => (!(pOK tl tl (t % 231) (t / 231)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 231 % 77) * 282) (x2Tab o (t / 231 / 77) (t % 231))) (x2Tab t3 (t / 231) (t % 231)))) = true := by
  decide +kernel

theorem chkC_4_d6808 : (List.range' 6808 8).all (fun t => (!(pOK tl tl (t % 231) (t / 231)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 231 % 77) * 282) (x2Tab o (t / 231 / 77) (t % 231))) (x2Tab t3 (t / 231) (t % 231)))) = true := by
  decide +kernel

theorem chkC_4_d6816 : (List.range' 6816 8).all (fun t => (!(pOK tl tl (t % 231) (t / 231)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 231 % 77) * 282) (x2Tab o (t / 231 / 77) (t % 231))) (x2Tab t3 (t / 231) (t % 231)))) = true := by
  decide +kernel

theorem chkC_4_d6824 : (List.range' 6824 8).all (fun t => (!(pOK tl tl (t % 231) (t / 231)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 231 % 77) * 282) (x2Tab o (t / 231 / 77) (t % 231))) (x2Tab t3 (t / 231) (t % 231)))) = true := by
  decide +kernel

theorem chkC_4_d6832 : (List.range' 6832 8).all (fun t => (!(pOK tl tl (t % 231) (t / 231)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 231 % 77) * 282) (x2Tab o (t / 231 / 77) (t % 231))) (x2Tab t3 (t / 231) (t % 231)))) = true := by
  decide +kernel

theorem chkC_4_d6840 : (List.range' 6840 8).all (fun t => (!(pOK tl tl (t % 231) (t / 231)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 231 % 77) * 282) (x2Tab o (t / 231 / 77) (t % 231))) (x2Tab t3 (t / 231) (t % 231)))) = true := by
  decide +kernel

theorem chkC_4_d6848 : (List.range' 6848 8).all (fun t => (!(pOK tl tl (t % 231) (t / 231)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 231 % 77) * 282) (x2Tab o (t / 231 / 77) (t % 231))) (x2Tab t3 (t / 231) (t % 231)))) = true := by
  decide +kernel

theorem chkC_4_d6856 : (List.range' 6856 8).all (fun t => (!(pOK tl tl (t % 231) (t / 231)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 231 % 77) * 282) (x2Tab o (t / 231 / 77) (t % 231))) (x2Tab t3 (t / 231) (t % 231)))) = true := by
  decide +kernel

theorem chkC_4_d6864 : (List.range' 6864 8).all (fun t => (!(pOK tl tl (t % 231) (t / 231)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 231 % 77) * 282) (x2Tab o (t / 231 / 77) (t % 231))) (x2Tab t3 (t / 231) (t % 231)))) = true := by
  decide +kernel

theorem chkC_4_d6872 : (List.range' 6872 8).all (fun t => (!(pOK tl tl (t % 231) (t / 231)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 231 % 77) * 282) (x2Tab o (t / 231 / 77) (t % 231))) (x2Tab t3 (t / 231) (t % 231)))) = true := by
  decide +kernel

theorem chkC_4_d6880 : (List.range' 6880 8).all (fun t => (!(pOK tl tl (t % 231) (t / 231)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 231 % 77) * 282) (x2Tab o (t / 231 / 77) (t % 231))) (x2Tab t3 (t / 231) (t % 231)))) = true := by
  decide +kernel

theorem chkC_4_d6888 : (List.range' 6888 8).all (fun t => (!(pOK tl tl (t % 231) (t / 231)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 231 % 77) * 282) (x2Tab o (t / 231 / 77) (t % 231))) (x2Tab t3 (t / 231) (t % 231)))) = true := by
  decide +kernel

theorem chkC_4_d6896 : (List.range' 6896 8).all (fun t => (!(pOK tl tl (t % 231) (t / 231)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 231 % 77) * 282) (x2Tab o (t / 231 / 77) (t % 231))) (x2Tab t3 (t / 231) (t % 231)))) = true := by
  decide +kernel

theorem chkC_4_d6904 : (List.range' 6904 8).all (fun t => (!(pOK tl tl (t % 231) (t / 231)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 231 % 77) * 282) (x2Tab o (t / 231 / 77) (t % 231))) (x2Tab t3 (t / 231) (t % 231)))) = true := by
  decide +kernel

theorem chkC_4_d6912 : (List.range' 6912 8).all (fun t => (!(pOK tl tl (t % 231) (t / 231)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 231 % 77) * 282) (x2Tab o (t / 231 / 77) (t % 231))) (x2Tab t3 (t / 231) (t % 231)))) = true := by
  decide +kernel

theorem chkC_4_d6920 : (List.range' 6920 8).all (fun t => (!(pOK tl tl (t % 231) (t / 231)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 231 % 77) * 282) (x2Tab o (t / 231 / 77) (t % 231))) (x2Tab t3 (t / 231) (t % 231)))) = true := by
  decide +kernel

theorem chkC_4_d6928 : (List.range' 6928 8).all (fun t => (!(pOK tl tl (t % 231) (t / 231)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 231 % 77) * 282) (x2Tab o (t / 231 / 77) (t % 231))) (x2Tab t3 (t / 231) (t % 231)))) = true := by
  decide +kernel

theorem chkC_4_d6936 : (List.range' 6936 8).all (fun t => (!(pOK tl tl (t % 231) (t / 231)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 231 % 77) * 282) (x2Tab o (t / 231 / 77) (t % 231))) (x2Tab t3 (t / 231) (t % 231)))) = true := by
  decide +kernel

theorem chkC_4_d6944 : (List.range' 6944 8).all (fun t => (!(pOK tl tl (t % 231) (t / 231)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 231 % 77) * 282) (x2Tab o (t / 231 / 77) (t % 231))) (x2Tab t3 (t / 231) (t % 231)))) = true := by
  decide +kernel

theorem chkC_4_d6952 : (List.range' 6952 8).all (fun t => (!(pOK tl tl (t % 231) (t / 231)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 231 % 77) * 282) (x2Tab o (t / 231 / 77) (t % 231))) (x2Tab t3 (t / 231) (t % 231)))) = true := by
  decide +kernel

theorem chkC_4_d6960 : (List.range' 6960 8).all (fun t => (!(pOK tl tl (t % 231) (t / 231)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 231 % 77) * 282) (x2Tab o (t / 231 / 77) (t % 231))) (x2Tab t3 (t / 231) (t % 231)))) = true := by
  decide +kernel

theorem chkC_4_d6968 : (List.range' 6968 8).all (fun t => (!(pOK tl tl (t % 231) (t / 231)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 231 % 77) * 282) (x2Tab o (t / 231 / 77) (t % 231))) (x2Tab t3 (t / 231) (t % 231)))) = true := by
  decide +kernel

theorem chkC_4_d6976 : (List.range' 6976 8).all (fun t => (!(pOK tl tl (t % 231) (t / 231)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 231 % 77) * 282) (x2Tab o (t / 231 / 77) (t % 231))) (x2Tab t3 (t / 231) (t % 231)))) = true := by
  decide +kernel

theorem chkC_4_d6984 : (List.range' 6984 8).all (fun t => (!(pOK tl tl (t % 231) (t / 231)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 231 % 77) * 282) (x2Tab o (t / 231 / 77) (t % 231))) (x2Tab t3 (t / 231) (t % 231)))) = true := by
  decide +kernel

theorem chkC_4_d6992 : (List.range' 6992 8).all (fun t => (!(pOK tl tl (t % 231) (t / 231)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 231 % 77) * 282) (x2Tab o (t / 231 / 77) (t % 231))) (x2Tab t3 (t / 231) (t % 231)))) = true := by
  decide +kernel

theorem chkC_4_d7000 : (List.range' 7000 8).all (fun t => (!(pOK tl tl (t % 231) (t / 231)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 231 % 77) * 282) (x2Tab o (t / 231 / 77) (t % 231))) (x2Tab t3 (t / 231) (t % 231)))) = true := by
  decide +kernel

theorem chkC_4_d7008 : (List.range' 7008 8).all (fun t => (!(pOK tl tl (t % 231) (t / 231)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 231 % 77) * 282) (x2Tab o (t / 231 / 77) (t % 231))) (x2Tab t3 (t / 231) (t % 231)))) = true := by
  decide +kernel

theorem chkC_4_d7016 : (List.range' 7016 8).all (fun t => (!(pOK tl tl (t % 231) (t / 231)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 231 % 77) * 282) (x2Tab o (t / 231 / 77) (t % 231))) (x2Tab t3 (t / 231) (t % 231)))) = true := by
  decide +kernel

theorem chkC_4_d7024 : (List.range' 7024 8).all (fun t => (!(pOK tl tl (t % 231) (t / 231)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 231 % 77) * 282) (x2Tab o (t / 231 / 77) (t % 231))) (x2Tab t3 (t / 231) (t % 231)))) = true := by
  decide +kernel

theorem chkC_4_d7032 : (List.range' 7032 8).all (fun t => (!(pOK tl tl (t % 231) (t / 231)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 231 % 77) * 282) (x2Tab o (t / 231 / 77) (t % 231))) (x2Tab t3 (t / 231) (t % 231)))) = true := by
  decide +kernel

theorem chkC_4_d7040 : (List.range' 7040 8).all (fun t => (!(pOK tl tl (t % 231) (t / 231)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 231 % 77) * 282) (x2Tab o (t / 231 / 77) (t % 231))) (x2Tab t3 (t / 231) (t % 231)))) = true := by
  decide +kernel

theorem chkC_4_d7048 : (List.range' 7048 8).all (fun t => (!(pOK tl tl (t % 231) (t / 231)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 231 % 77) * 282) (x2Tab o (t / 231 / 77) (t % 231))) (x2Tab t3 (t / 231) (t % 231)))) = true := by
  decide +kernel

theorem chkC_4_d7056 : (List.range' 7056 8).all (fun t => (!(pOK tl tl (t % 231) (t / 231)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 231 % 77) * 282) (x2Tab o (t / 231 / 77) (t % 231))) (x2Tab t3 (t / 231) (t % 231)))) = true := by
  decide +kernel

theorem chkC_4_d7064 : (List.range' 7064 8).all (fun t => (!(pOK tl tl (t % 231) (t / 231)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 231 % 77) * 282) (x2Tab o (t / 231 / 77) (t % 231))) (x2Tab t3 (t / 231) (t % 231)))) = true := by
  decide +kernel

theorem chkC_4_d7072 : (List.range' 7072 8).all (fun t => (!(pOK tl tl (t % 231) (t / 231)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 231 % 77) * 282) (x2Tab o (t / 231 / 77) (t % 231))) (x2Tab t3 (t / 231) (t % 231)))) = true := by
  decide +kernel

theorem chkC_4_d7080 : (List.range' 7080 8).all (fun t => (!(pOK tl tl (t % 231) (t / 231)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 231 % 77) * 282) (x2Tab o (t / 231 / 77) (t % 231))) (x2Tab t3 (t / 231) (t % 231)))) = true := by
  decide +kernel

theorem chkC_4_d7088 : (List.range' 7088 8).all (fun t => (!(pOK tl tl (t % 231) (t / 231)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 231 % 77) * 282) (x2Tab o (t / 231 / 77) (t % 231))) (x2Tab t3 (t / 231) (t % 231)))) = true := by
  decide +kernel

theorem chkC_4_d7096 : (List.range' 7096 8).all (fun t => (!(pOK tl tl (t % 231) (t / 231)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 231 % 77) * 282) (x2Tab o (t / 231 / 77) (t % 231))) (x2Tab t3 (t / 231) (t % 231)))) = true := by
  decide +kernel

theorem chkC_4_d7104 : (List.range' 7104 8).all (fun t => (!(pOK tl tl (t % 231) (t / 231)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 231 % 77) * 282) (x2Tab o (t / 231 / 77) (t % 231))) (x2Tab t3 (t / 231) (t % 231)))) = true := by
  decide +kernel

theorem chkC_4_d7112 : (List.range' 7112 8).all (fun t => (!(pOK tl tl (t % 231) (t / 231)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 231 % 77) * 282) (x2Tab o (t / 231 / 77) (t % 231))) (x2Tab t3 (t / 231) (t % 231)))) = true := by
  decide +kernel

theorem chkC_4_d7120 : (List.range' 7120 8).all (fun t => (!(pOK tl tl (t % 231) (t / 231)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 231 % 77) * 282) (x2Tab o (t / 231 / 77) (t % 231))) (x2Tab t3 (t / 231) (t % 231)))) = true := by
  decide +kernel

theorem chkC_4_d7128 : (List.range' 7128 8).all (fun t => (!(pOK tl tl (t % 231) (t / 231)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 231 % 77) * 282) (x2Tab o (t / 231 / 77) (t % 231))) (x2Tab t3 (t / 231) (t % 231)))) = true := by
  decide +kernel

theorem chkC_4_d7136 : (List.range' 7136 8).all (fun t => (!(pOK tl tl (t % 231) (t / 231)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 231 % 77) * 282) (x2Tab o (t / 231 / 77) (t % 231))) (x2Tab t3 (t / 231) (t % 231)))) = true := by
  decide +kernel

theorem chkC_4_d7144 : (List.range' 7144 8).all (fun t => (!(pOK tl tl (t % 231) (t / 231)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 231 % 77) * 282) (x2Tab o (t / 231 / 77) (t % 231))) (x2Tab t3 (t / 231) (t % 231)))) = true := by
  decide +kernel

theorem chkC_4_d7152 : (List.range' 7152 8).all (fun t => (!(pOK tl tl (t % 231) (t / 231)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 231 % 77) * 282) (x2Tab o (t / 231 / 77) (t % 231))) (x2Tab t3 (t / 231) (t % 231)))) = true := by
  decide +kernel

theorem chkC_4_d7160 : (List.range' 7160 8).all (fun t => (!(pOK tl tl (t % 231) (t / 231)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 231 % 77) * 282) (x2Tab o (t / 231 / 77) (t % 231))) (x2Tab t3 (t / 231) (t % 231)))) = true := by
  decide +kernel

theorem chkC_4_d7168 : (List.range' 7168 8).all (fun t => (!(pOK tl tl (t % 231) (t / 231)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 231 % 77) * 282) (x2Tab o (t / 231 / 77) (t % 231))) (x2Tab t3 (t / 231) (t % 231)))) = true := by
  decide +kernel

theorem chkC_4_d7176 : (List.range' 7176 8).all (fun t => (!(pOK tl tl (t % 231) (t / 231)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 231 % 77) * 282) (x2Tab o (t / 231 / 77) (t % 231))) (x2Tab t3 (t / 231) (t % 231)))) = true := by
  decide +kernel

theorem chkC_4_d7184 : (List.range' 7184 8).all (fun t => (!(pOK tl tl (t % 231) (t / 231)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 231 % 77) * 282) (x2Tab o (t / 231 / 77) (t % 231))) (x2Tab t3 (t / 231) (t % 231)))) = true := by
  decide +kernel

theorem chkC_4_d7192 : (List.range' 7192 8).all (fun t => (!(pOK tl tl (t % 231) (t / 231)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 231 % 77) * 282) (x2Tab o (t / 231 / 77) (t % 231))) (x2Tab t3 (t / 231) (t % 231)))) = true := by
  decide +kernel

theorem chkC_4_d7200 : (List.range' 7200 8).all (fun t => (!(pOK tl tl (t % 231) (t / 231)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 231 % 77) * 282) (x2Tab o (t / 231 / 77) (t % 231))) (x2Tab t3 (t / 231) (t % 231)))) = true := by
  decide +kernel

theorem chkC_4_d7208 : (List.range' 7208 8).all (fun t => (!(pOK tl tl (t % 231) (t / 231)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 231 % 77) * 282) (x2Tab o (t / 231 / 77) (t % 231))) (x2Tab t3 (t / 231) (t % 231)))) = true := by
  decide +kernel

theorem chkC_4_d7216 : (List.range' 7216 8).all (fun t => (!(pOK tl tl (t % 231) (t / 231)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 231 % 77) * 282) (x2Tab o (t / 231 / 77) (t % 231))) (x2Tab t3 (t / 231) (t % 231)))) = true := by
  decide +kernel

theorem chkC_4_d7224 : (List.range' 7224 8).all (fun t => (!(pOK tl tl (t % 231) (t / 231)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 231 % 77) * 282) (x2Tab o (t / 231 / 77) (t % 231))) (x2Tab t3 (t / 231) (t % 231)))) = true := by
  decide +kernel

theorem chkC_4_d7232 : (List.range' 7232 8).all (fun t => (!(pOK tl tl (t % 231) (t / 231)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 231 % 77) * 282) (x2Tab o (t / 231 / 77) (t % 231))) (x2Tab t3 (t / 231) (t % 231)))) = true := by
  decide +kernel

theorem chkC_4_d7240 : (List.range' 7240 8).all (fun t => (!(pOK tl tl (t % 231) (t / 231)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 231 % 77) * 282) (x2Tab o (t / 231 / 77) (t % 231))) (x2Tab t3 (t / 231) (t % 231)))) = true := by
  decide +kernel

theorem chkC_4_d7248 : (List.range' 7248 8).all (fun t => (!(pOK tl tl (t % 231) (t / 231)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 231 % 77) * 282) (x2Tab o (t / 231 / 77) (t % 231))) (x2Tab t3 (t / 231) (t % 231)))) = true := by
  decide +kernel

theorem chkC_4_d7256 : (List.range' 7256 8).all (fun t => (!(pOK tl tl (t % 231) (t / 231)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 231 % 77) * 282) (x2Tab o (t / 231 / 77) (t % 231))) (x2Tab t3 (t / 231) (t % 231)))) = true := by
  decide +kernel

theorem chkC_4_d7264 : (List.range' 7264 8).all (fun t => (!(pOK tl tl (t % 231) (t / 231)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 231 % 77) * 282) (x2Tab o (t / 231 / 77) (t % 231))) (x2Tab t3 (t / 231) (t % 231)))) = true := by
  decide +kernel

theorem chkC_4_d7272 : (List.range' 7272 8).all (fun t => (!(pOK tl tl (t % 231) (t / 231)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 231 % 77) * 282) (x2Tab o (t / 231 / 77) (t % 231))) (x2Tab t3 (t / 231) (t % 231)))) = true := by
  decide +kernel

theorem chkC_4_d7280 : (List.range' 7280 8).all (fun t => (!(pOK tl tl (t % 231) (t / 231)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 231 % 77) * 282) (x2Tab o (t / 231 / 77) (t % 231))) (x2Tab t3 (t / 231) (t % 231)))) = true := by
  decide +kernel

theorem chkC_4_d7288 : (List.range' 7288 8).all (fun t => (!(pOK tl tl (t % 231) (t / 231)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 231 % 77) * 282) (x2Tab o (t / 231 / 77) (t % 231))) (x2Tab t3 (t / 231) (t % 231)))) = true := by
  decide +kernel

theorem chkC_4_d7296 : (List.range' 7296 8).all (fun t => (!(pOK tl tl (t % 231) (t / 231)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 231 % 77) * 282) (x2Tab o (t / 231 / 77) (t % 231))) (x2Tab t3 (t / 231) (t % 231)))) = true := by
  decide +kernel

theorem chkC_4_d7304 : (List.range' 7304 8).all (fun t => (!(pOK tl tl (t % 231) (t / 231)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 231 % 77) * 282) (x2Tab o (t / 231 / 77) (t % 231))) (x2Tab t3 (t / 231) (t % 231)))) = true := by
  decide +kernel

theorem chkC_4_d7312 : (List.range' 7312 8).all (fun t => (!(pOK tl tl (t % 231) (t / 231)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 231 % 77) * 282) (x2Tab o (t / 231 / 77) (t % 231))) (x2Tab t3 (t / 231) (t % 231)))) = true := by
  decide +kernel

theorem chkC_4_d7320 : (List.range' 7320 8).all (fun t => (!(pOK tl tl (t % 231) (t / 231)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 231 % 77) * 282) (x2Tab o (t / 231 / 77) (t % 231))) (x2Tab t3 (t / 231) (t % 231)))) = true := by
  decide +kernel

theorem chkC_4_d7328 : (List.range' 7328 8).all (fun t => (!(pOK tl tl (t % 231) (t / 231)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 231 % 77) * 282) (x2Tab o (t / 231 / 77) (t % 231))) (x2Tab t3 (t / 231) (t % 231)))) = true := by
  decide +kernel

theorem chkC_4_d7336 : (List.range' 7336 8).all (fun t => (!(pOK tl tl (t % 231) (t / 231)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 231 % 77) * 282) (x2Tab o (t / 231 / 77) (t % 231))) (x2Tab t3 (t / 231) (t % 231)))) = true := by
  decide +kernel

theorem chkC_4_d7344 : (List.range' 7344 8).all (fun t => (!(pOK tl tl (t % 231) (t / 231)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 231 % 77) * 282) (x2Tab o (t / 231 / 77) (t % 231))) (x2Tab t3 (t / 231) (t % 231)))) = true := by
  decide +kernel

theorem chkC_4_d7352 : (List.range' 7352 8).all (fun t => (!(pOK tl tl (t % 231) (t / 231)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 231 % 77) * 282) (x2Tab o (t / 231 / 77) (t % 231))) (x2Tab t3 (t / 231) (t % 231)))) = true := by
  decide +kernel

theorem chkC_4_d7360 : (List.range' 7360 8).all (fun t => (!(pOK tl tl (t % 231) (t / 231)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 231 % 77) * 282) (x2Tab o (t / 231 / 77) (t % 231))) (x2Tab t3 (t / 231) (t % 231)))) = true := by
  decide +kernel

theorem chkC_4_d7368 : (List.range' 7368 8).all (fun t => (!(pOK tl tl (t % 231) (t / 231)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 231 % 77) * 282) (x2Tab o (t / 231 / 77) (t % 231))) (x2Tab t3 (t / 231) (t % 231)))) = true := by
  decide +kernel

theorem chkC_4_d7376 : (List.range' 7376 8).all (fun t => (!(pOK tl tl (t % 231) (t / 231)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 231 % 77) * 282) (x2Tab o (t / 231 / 77) (t % 231))) (x2Tab t3 (t / 231) (t % 231)))) = true := by
  decide +kernel

theorem chkC_4_d7384 : (List.range' 7384 8).all (fun t => (!(pOK tl tl (t % 231) (t / 231)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 231 % 77) * 282) (x2Tab o (t / 231 / 77) (t % 231))) (x2Tab t3 (t / 231) (t % 231)))) = true := by
  decide +kernel

theorem chkC_4_d7392 : (List.range' 7392 8).all (fun t => (!(pOK tl tl (t % 231) (t / 231)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 231 % 77) * 282) (x2Tab o (t / 231 / 77) (t % 231))) (x2Tab t3 (t / 231) (t % 231)))) = true := by
  decide +kernel

theorem chkC_4_d7400 : (List.range' 7400 8).all (fun t => (!(pOK tl tl (t % 231) (t / 231)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 231 % 77) * 282) (x2Tab o (t / 231 / 77) (t % 231))) (x2Tab t3 (t / 231) (t % 231)))) = true := by
  decide +kernel

theorem chkC_4_d7408 : (List.range' 7408 8).all (fun t => (!(pOK tl tl (t % 231) (t / 231)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 231 % 77) * 282) (x2Tab o (t / 231 / 77) (t % 231))) (x2Tab t3 (t / 231) (t % 231)))) = true := by
  decide +kernel

theorem chkC_4_d7416 : (List.range' 7416 8).all (fun t => (!(pOK tl tl (t % 231) (t / 231)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 231 % 77) * 282) (x2Tab o (t / 231 / 77) (t % 231))) (x2Tab t3 (t / 231) (t % 231)))) = true := by
  decide +kernel

theorem chkC_4_d7424 : (List.range' 7424 8).all (fun t => (!(pOK tl tl (t % 231) (t / 231)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 231 % 77) * 282) (x2Tab o (t / 231 / 77) (t % 231))) (x2Tab t3 (t / 231) (t % 231)))) = true := by
  decide +kernel

theorem chkC_4_d7432 : (List.range' 7432 8).all (fun t => (!(pOK tl tl (t % 231) (t / 231)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 231 % 77) * 282) (x2Tab o (t / 231 / 77) (t % 231))) (x2Tab t3 (t / 231) (t % 231)))) = true := by
  decide +kernel

theorem chkC_4_d7440 : (List.range' 7440 8).all (fun t => (!(pOK tl tl (t % 231) (t / 231)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 231 % 77) * 282) (x2Tab o (t / 231 / 77) (t % 231))) (x2Tab t3 (t / 231) (t % 231)))) = true := by
  decide +kernel

theorem chkC_4_d7448 : (List.range' 7448 8).all (fun t => (!(pOK tl tl (t % 231) (t / 231)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 231 % 77) * 282) (x2Tab o (t / 231 / 77) (t % 231))) (x2Tab t3 (t / 231) (t % 231)))) = true := by
  decide +kernel

theorem chkC_4_d7456 : (List.range' 7456 8).all (fun t => (!(pOK tl tl (t % 231) (t / 231)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 231 % 77) * 282) (x2Tab o (t / 231 / 77) (t % 231))) (x2Tab t3 (t / 231) (t % 231)))) = true := by
  decide +kernel

theorem chkC_4_d7464 : (List.range' 7464 8).all (fun t => (!(pOK tl tl (t % 231) (t / 231)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 231 % 77) * 282) (x2Tab o (t / 231 / 77) (t % 231))) (x2Tab t3 (t / 231) (t % 231)))) = true := by
  decide +kernel

theorem chkC_4_d7472 : (List.range' 7472 8).all (fun t => (!(pOK tl tl (t % 231) (t / 231)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 231 % 77) * 282) (x2Tab o (t / 231 / 77) (t % 231))) (x2Tab t3 (t / 231) (t % 231)))) = true := by
  decide +kernel

theorem chkC_4_d7480 : (List.range' 7480 8).all (fun t => (!(pOK tl tl (t % 231) (t / 231)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 231 % 77) * 282) (x2Tab o (t / 231 / 77) (t % 231))) (x2Tab t3 (t / 231) (t % 231)))) = true := by
  decide +kernel

theorem chkC_4_d7488 : (List.range' 7488 8).all (fun t => (!(pOK tl tl (t % 231) (t / 231)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 231 % 77) * 282) (x2Tab o (t / 231 / 77) (t % 231))) (x2Tab t3 (t / 231) (t % 231)))) = true := by
  decide +kernel

theorem chkC_4_d7496 : (List.range' 7496 8).all (fun t => (!(pOK tl tl (t % 231) (t / 231)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 231 % 77) * 282) (x2Tab o (t / 231 / 77) (t % 231))) (x2Tab t3 (t / 231) (t % 231)))) = true := by
  decide +kernel

theorem chkC_4_d7504 : (List.range' 7504 8).all (fun t => (!(pOK tl tl (t % 231) (t / 231)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 231 % 77) * 282) (x2Tab o (t / 231 / 77) (t % 231))) (x2Tab t3 (t / 231) (t % 231)))) = true := by
  decide +kernel

theorem chkC_4_d7512 : (List.range' 7512 8).all (fun t => (!(pOK tl tl (t % 231) (t / 231)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 231 % 77) * 282) (x2Tab o (t / 231 / 77) (t % 231))) (x2Tab t3 (t / 231) (t % 231)))) = true := by
  decide +kernel

theorem chkC_4_d7520 : (List.range' 7520 8).all (fun t => (!(pOK tl tl (t % 231) (t / 231)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 231 % 77) * 282) (x2Tab o (t / 231 / 77) (t % 231))) (x2Tab t3 (t / 231) (t % 231)))) = true := by
  decide +kernel

theorem chkC_4_d7528 : (List.range' 7528 8).all (fun t => (!(pOK tl tl (t % 231) (t / 231)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 231 % 77) * 282) (x2Tab o (t / 231 / 77) (t % 231))) (x2Tab t3 (t / 231) (t % 231)))) = true := by
  decide +kernel

theorem chkC_4_d7536 : (List.range' 7536 8).all (fun t => (!(pOK tl tl (t % 231) (t / 231)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 231 % 77) * 282) (x2Tab o (t / 231 / 77) (t % 231))) (x2Tab t3 (t / 231) (t % 231)))) = true := by
  decide +kernel

theorem chkC_4_d7544 : (List.range' 7544 8).all (fun t => (!(pOK tl tl (t % 231) (t / 231)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 231 % 77) * 282) (x2Tab o (t / 231 / 77) (t % 231))) (x2Tab t3 (t / 231) (t % 231)))) = true := by
  decide +kernel

theorem chkC_4_d7552 : (List.range' 7552 8).all (fun t => (!(pOK tl tl (t % 231) (t / 231)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 231 % 77) * 282) (x2Tab o (t / 231 / 77) (t % 231))) (x2Tab t3 (t / 231) (t % 231)))) = true := by
  decide +kernel

theorem chkC_4_d7560 : (List.range' 7560 8).all (fun t => (!(pOK tl tl (t % 231) (t / 231)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 231 % 77) * 282) (x2Tab o (t / 231 / 77) (t % 231))) (x2Tab t3 (t / 231) (t % 231)))) = true := by
  decide +kernel

theorem chkC_4_d7568 : (List.range' 7568 8).all (fun t => (!(pOK tl tl (t % 231) (t / 231)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 231 % 77) * 282) (x2Tab o (t / 231 / 77) (t % 231))) (x2Tab t3 (t / 231) (t % 231)))) = true := by
  decide +kernel

theorem chkC_4_d7576 : (List.range' 7576 8).all (fun t => (!(pOK tl tl (t % 231) (t / 231)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 231 % 77) * 282) (x2Tab o (t / 231 / 77) (t % 231))) (x2Tab t3 (t / 231) (t % 231)))) = true := by
  decide +kernel

theorem chkC_4_d7584 : (List.range' 7584 8).all (fun t => (!(pOK tl tl (t % 231) (t / 231)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 231 % 77) * 282) (x2Tab o (t / 231 / 77) (t % 231))) (x2Tab t3 (t / 231) (t % 231)))) = true := by
  decide +kernel

theorem chkC_4_d7592 : (List.range' 7592 8).all (fun t => (!(pOK tl tl (t % 231) (t / 231)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 231 % 77) * 282) (x2Tab o (t / 231 / 77) (t % 231))) (x2Tab t3 (t / 231) (t % 231)))) = true := by
  decide +kernel

theorem chkC_4_d7600 : (List.range' 7600 8).all (fun t => (!(pOK tl tl (t % 231) (t / 231)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 231 % 77) * 282) (x2Tab o (t / 231 / 77) (t % 231))) (x2Tab t3 (t / 231) (t % 231)))) = true := by
  decide +kernel

theorem chkC_4_d7608 : (List.range' 7608 8).all (fun t => (!(pOK tl tl (t % 231) (t / 231)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 231 % 77) * 282) (x2Tab o (t / 231 / 77) (t % 231))) (x2Tab t3 (t / 231) (t % 231)))) = true := by
  decide +kernel

theorem chkC_4_d7616 : (List.range' 7616 8).all (fun t => (!(pOK tl tl (t % 231) (t / 231)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 231 % 77) * 282) (x2Tab o (t / 231 / 77) (t % 231))) (x2Tab t3 (t / 231) (t % 231)))) = true := by
  decide +kernel

theorem chkC_4_d7624 : (List.range' 7624 8).all (fun t => (!(pOK tl tl (t % 231) (t / 231)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 231 % 77) * 282) (x2Tab o (t / 231 / 77) (t % 231))) (x2Tab t3 (t / 231) (t % 231)))) = true := by
  decide +kernel

theorem chkC_4_d7632 : (List.range' 7632 8).all (fun t => (!(pOK tl tl (t % 231) (t / 231)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 231 % 77) * 282) (x2Tab o (t / 231 / 77) (t % 231))) (x2Tab t3 (t / 231) (t % 231)))) = true := by
  decide +kernel

theorem chkC_4_d7640 : (List.range' 7640 8).all (fun t => (!(pOK tl tl (t % 231) (t / 231)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 231 % 77) * 282) (x2Tab o (t / 231 / 77) (t % 231))) (x2Tab t3 (t / 231) (t % 231)))) = true := by
  decide +kernel

theorem chkC_4_d7648 : (List.range' 7648 8).all (fun t => (!(pOK tl tl (t % 231) (t / 231)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 231 % 77) * 282) (x2Tab o (t / 231 / 77) (t % 231))) (x2Tab t3 (t / 231) (t % 231)))) = true := by
  decide +kernel

theorem chkC_4_d7656 : (List.range' 7656 8).all (fun t => (!(pOK tl tl (t % 231) (t / 231)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 231 % 77) * 282) (x2Tab o (t / 231 / 77) (t % 231))) (x2Tab t3 (t / 231) (t % 231)))) = true := by
  decide +kernel

theorem chkC_4_d7664 : (List.range' 7664 8).all (fun t => (!(pOK tl tl (t % 231) (t / 231)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 231 % 77) * 282) (x2Tab o (t / 231 / 77) (t % 231))) (x2Tab t3 (t / 231) (t % 231)))) = true := by
  decide +kernel

theorem chkC_4_d7672 : (List.range' 7672 8).all (fun t => (!(pOK tl tl (t % 231) (t / 231)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 231 % 77) * 282) (x2Tab o (t / 231 / 77) (t % 231))) (x2Tab t3 (t / 231) (t % 231)))) = true := by
  decide +kernel

theorem chkC_4_d7680 : (List.range' 7680 8).all (fun t => (!(pOK tl tl (t % 231) (t / 231)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 231 % 77) * 282) (x2Tab o (t / 231 / 77) (t % 231))) (x2Tab t3 (t / 231) (t % 231)))) = true := by
  decide +kernel

theorem chkC_4_d7688 : (List.range' 7688 8).all (fun t => (!(pOK tl tl (t % 231) (t / 231)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 231 % 77) * 282) (x2Tab o (t / 231 / 77) (t % 231))) (x2Tab t3 (t / 231) (t % 231)))) = true := by
  decide +kernel

theorem chkC_4_d7696 : (List.range' 7696 8).all (fun t => (!(pOK tl tl (t % 231) (t / 231)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 231 % 77) * 282) (x2Tab o (t / 231 / 77) (t % 231))) (x2Tab t3 (t / 231) (t % 231)))) = true := by
  decide +kernel

theorem chkC_4_d7704 : (List.range' 7704 8).all (fun t => (!(pOK tl tl (t % 231) (t / 231)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 231 % 77) * 282) (x2Tab o (t / 231 / 77) (t % 231))) (x2Tab t3 (t / 231) (t % 231)))) = true := by
  decide +kernel

theorem chkC_4_d7712 : (List.range' 7712 8).all (fun t => (!(pOK tl tl (t % 231) (t / 231)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 231 % 77) * 282) (x2Tab o (t / 231 / 77) (t % 231))) (x2Tab t3 (t / 231) (t % 231)))) = true := by
  decide +kernel

theorem chkC_4_d7720 : (List.range' 7720 8).all (fun t => (!(pOK tl tl (t % 231) (t / 231)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 231 % 77) * 282) (x2Tab o (t / 231 / 77) (t % 231))) (x2Tab t3 (t / 231) (t % 231)))) = true := by
  decide +kernel

theorem chkC_4_d7728 : (List.range' 7728 8).all (fun t => (!(pOK tl tl (t % 231) (t / 231)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 231 % 77) * 282) (x2Tab o (t / 231 / 77) (t % 231))) (x2Tab t3 (t / 231) (t % 231)))) = true := by
  decide +kernel

theorem chkC_4_d7736 : (List.range' 7736 8).all (fun t => (!(pOK tl tl (t % 231) (t / 231)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 231 % 77) * 282) (x2Tab o (t / 231 / 77) (t % 231))) (x2Tab t3 (t / 231) (t % 231)))) = true := by
  decide +kernel

theorem chkC_4_d7744 : (List.range' 7744 8).all (fun t => (!(pOK tl tl (t % 231) (t / 231)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 231 % 77) * 282) (x2Tab o (t / 231 / 77) (t % 231))) (x2Tab t3 (t / 231) (t % 231)))) = true := by
  decide +kernel

theorem chkC_4_d7752 : (List.range' 7752 8).all (fun t => (!(pOK tl tl (t % 231) (t / 231)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 231 % 77) * 282) (x2Tab o (t / 231 / 77) (t % 231))) (x2Tab t3 (t / 231) (t % 231)))) = true := by
  decide +kernel

theorem chkC_4_d7760 : (List.range' 7760 8).all (fun t => (!(pOK tl tl (t % 231) (t / 231)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 231 % 77) * 282) (x2Tab o (t / 231 / 77) (t % 231))) (x2Tab t3 (t / 231) (t % 231)))) = true := by
  decide +kernel

theorem chkC_4_d7768 : (List.range' 7768 8).all (fun t => (!(pOK tl tl (t % 231) (t / 231)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 231 % 77) * 282) (x2Tab o (t / 231 / 77) (t % 231))) (x2Tab t3 (t / 231) (t % 231)))) = true := by
  decide +kernel

theorem chkC_4_d7776 : (List.range' 7776 8).all (fun t => (!(pOK tl tl (t % 231) (t / 231)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 231 % 77) * 282) (x2Tab o (t / 231 / 77) (t % 231))) (x2Tab t3 (t / 231) (t % 231)))) = true := by
  decide +kernel

theorem chkC_4_d7784 : (List.range' 7784 8).all (fun t => (!(pOK tl tl (t % 231) (t / 231)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 231 % 77) * 282) (x2Tab o (t / 231 / 77) (t % 231))) (x2Tab t3 (t / 231) (t % 231)))) = true := by
  decide +kernel

theorem chkC_4_d7792 : (List.range' 7792 8).all (fun t => (!(pOK tl tl (t % 231) (t / 231)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 231 % 77) * 282) (x2Tab o (t / 231 / 77) (t % 231))) (x2Tab t3 (t / 231) (t % 231)))) = true := by
  decide +kernel

theorem chkC_4_d7800 : (List.range' 7800 8).all (fun t => (!(pOK tl tl (t % 231) (t / 231)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 231 % 77) * 282) (x2Tab o (t / 231 / 77) (t % 231))) (x2Tab t3 (t / 231) (t % 231)))) = true := by
  decide +kernel

theorem chkC_4_d7808 : (List.range' 7808 8).all (fun t => (!(pOK tl tl (t % 231) (t / 231)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 231 % 77) * 282) (x2Tab o (t / 231 / 77) (t % 231))) (x2Tab t3 (t / 231) (t % 231)))) = true := by
  decide +kernel

theorem chkC_4_d7816 : (List.range' 7816 8).all (fun t => (!(pOK tl tl (t % 231) (t / 231)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 231 % 77) * 282) (x2Tab o (t / 231 / 77) (t % 231))) (x2Tab t3 (t / 231) (t % 231)))) = true := by
  decide +kernel

theorem chkC_4_d7824 : (List.range' 7824 8).all (fun t => (!(pOK tl tl (t % 231) (t / 231)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 231 % 77) * 282) (x2Tab o (t / 231 / 77) (t % 231))) (x2Tab t3 (t / 231) (t % 231)))) = true := by
  decide +kernel

theorem chkC_4_d7832 : (List.range' 7832 8).all (fun t => (!(pOK tl tl (t % 231) (t / 231)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 231 % 77) * 282) (x2Tab o (t / 231 / 77) (t % 231))) (x2Tab t3 (t / 231) (t % 231)))) = true := by
  decide +kernel

theorem chkC_4_d7840 : (List.range' 7840 8).all (fun t => (!(pOK tl tl (t % 231) (t / 231)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 231 % 77) * 282) (x2Tab o (t / 231 / 77) (t % 231))) (x2Tab t3 (t / 231) (t % 231)))) = true := by
  decide +kernel

theorem chkC_4_d7848 : (List.range' 7848 8).all (fun t => (!(pOK tl tl (t % 231) (t / 231)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 231 % 77) * 282) (x2Tab o (t / 231 / 77) (t % 231))) (x2Tab t3 (t / 231) (t % 231)))) = true := by
  decide +kernel

theorem chkC_4_d7856 : (List.range' 7856 8).all (fun t => (!(pOK tl tl (t % 231) (t / 231)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 231 % 77) * 282) (x2Tab o (t / 231 / 77) (t % 231))) (x2Tab t3 (t / 231) (t % 231)))) = true := by
  decide +kernel

theorem chkC_4_d7864 : (List.range' 7864 8).all (fun t => (!(pOK tl tl (t % 231) (t / 231)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 231 % 77) * 282) (x2Tab o (t / 231 / 77) (t % 231))) (x2Tab t3 (t / 231) (t % 231)))) = true := by
  decide +kernel

theorem chkC_4_d7872 : (List.range' 7872 8).all (fun t => (!(pOK tl tl (t % 231) (t / 231)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 231 % 77) * 282) (x2Tab o (t / 231 / 77) (t % 231))) (x2Tab t3 (t / 231) (t % 231)))) = true := by
  decide +kernel

theorem chkC_4_d7880 : (List.range' 7880 8).all (fun t => (!(pOK tl tl (t % 231) (t / 231)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 231 % 77) * 282) (x2Tab o (t / 231 / 77) (t % 231))) (x2Tab t3 (t / 231) (t % 231)))) = true := by
  decide +kernel

theorem chkC_4_d7888 : (List.range' 7888 8).all (fun t => (!(pOK tl tl (t % 231) (t / 231)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 231 % 77) * 282) (x2Tab o (t / 231 / 77) (t % 231))) (x2Tab t3 (t / 231) (t % 231)))) = true := by
  decide +kernel

theorem chkC_4_d7896 : (List.range' 7896 8).all (fun t => (!(pOK tl tl (t % 231) (t / 231)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 231 % 77) * 282) (x2Tab o (t / 231 / 77) (t % 231))) (x2Tab t3 (t / 231) (t % 231)))) = true := by
  decide +kernel

theorem chkC_4_d7904 : (List.range' 7904 8).all (fun t => (!(pOK tl tl (t % 231) (t / 231)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 231 % 77) * 282) (x2Tab o (t / 231 / 77) (t % 231))) (x2Tab t3 (t / 231) (t % 231)))) = true := by
  decide +kernel

theorem chkC_4_d7912 : (List.range' 7912 8).all (fun t => (!(pOK tl tl (t % 231) (t / 231)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 231 % 77) * 282) (x2Tab o (t / 231 / 77) (t % 231))) (x2Tab t3 (t / 231) (t % 231)))) = true := by
  decide +kernel

theorem chkC_4_d7920 : (List.range' 7920 8).all (fun t => (!(pOK tl tl (t % 231) (t / 231)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 231 % 77) * 282) (x2Tab o (t / 231 / 77) (t % 231))) (x2Tab t3 (t / 231) (t % 231)))) = true := by
  decide +kernel

theorem chkC_4_d7928 : (List.range' 7928 8).all (fun t => (!(pOK tl tl (t % 231) (t / 231)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 231 % 77) * 282) (x2Tab o (t / 231 / 77) (t % 231))) (x2Tab t3 (t / 231) (t % 231)))) = true := by
  decide +kernel

theorem chkC_4_d7936 : (List.range' 7936 8).all (fun t => (!(pOK tl tl (t % 231) (t / 231)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 231 % 77) * 282) (x2Tab o (t / 231 / 77) (t % 231))) (x2Tab t3 (t / 231) (t % 231)))) = true := by
  decide +kernel

theorem chkC_4_d7944 : (List.range' 7944 8).all (fun t => (!(pOK tl tl (t % 231) (t / 231)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 231 % 77) * 282) (x2Tab o (t / 231 / 77) (t % 231))) (x2Tab t3 (t / 231) (t % 231)))) = true := by
  decide +kernel

theorem chkC_4_d7952 : (List.range' 7952 8).all (fun t => (!(pOK tl tl (t % 231) (t / 231)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 231 % 77) * 282) (x2Tab o (t / 231 / 77) (t % 231))) (x2Tab t3 (t / 231) (t % 231)))) = true := by
  decide +kernel

theorem chkC_4_d7960 : (List.range' 7960 8).all (fun t => (!(pOK tl tl (t % 231) (t / 231)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 231 % 77) * 282) (x2Tab o (t / 231 / 77) (t % 231))) (x2Tab t3 (t / 231) (t % 231)))) = true := by
  decide +kernel

theorem chkC_4_d7968 : (List.range' 7968 8).all (fun t => (!(pOK tl tl (t % 231) (t / 231)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 231 % 77) * 282) (x2Tab o (t / 231 / 77) (t % 231))) (x2Tab t3 (t / 231) (t % 231)))) = true := by
  decide +kernel

theorem chkC_4_d7976 : (List.range' 7976 8).all (fun t => (!(pOK tl tl (t % 231) (t / 231)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 231 % 77) * 282) (x2Tab o (t / 231 / 77) (t % 231))) (x2Tab t3 (t / 231) (t % 231)))) = true := by
  decide +kernel

theorem chkC_4_d7984 : (List.range' 7984 8).all (fun t => (!(pOK tl tl (t % 231) (t / 231)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 231 % 77) * 282) (x2Tab o (t / 231 / 77) (t % 231))) (x2Tab t3 (t / 231) (t % 231)))) = true := by
  decide +kernel

theorem chkC_4_d7992 : (List.range' 7992 8).all (fun t => (!(pOK tl tl (t % 231) (t / 231)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 231 % 77) * 282) (x2Tab o (t / 231 / 77) (t % 231))) (x2Tab t3 (t / 231) (t % 231)))) = true := by
  decide +kernel

theorem chkC_4 : ∀ t, 6400 ≤ t → t < 8000 → ((!(pOK tl tl (t % 231) (t / 231)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 231 % 77) * 282) (x2Tab o (t / 231 / 77) (t % 231))) (x2Tab t3 (t / 231) (t % 231)))) = true := by
  exact (x2c_join _ 6400 6408 8000 (x2c_range_all (fun t => (!(pOK tl tl (t % 231) (t / 231)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 231 % 77) * 282) (x2Tab o (t / 231 / 77) (t % 231))) (x2Tab t3 (t / 231) (t % 231)))) 6400 8 chkC_4_d6400) (x2c_join _ 6408 6416 8000 (x2c_range_all (fun t => (!(pOK tl tl (t % 231) (t / 231)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 231 % 77) * 282) (x2Tab o (t / 231 / 77) (t % 231))) (x2Tab t3 (t / 231) (t % 231)))) 6408 8 chkC_4_d6408) (x2c_join _ 6416 6424 8000 (x2c_range_all (fun t => (!(pOK tl tl (t % 231) (t / 231)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 231 % 77) * 282) (x2Tab o (t / 231 / 77) (t % 231))) (x2Tab t3 (t / 231) (t % 231)))) 6416 8 chkC_4_d6416) (x2c_join _ 6424 6432 8000 (x2c_range_all (fun t => (!(pOK tl tl (t % 231) (t / 231)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 231 % 77) * 282) (x2Tab o (t / 231 / 77) (t % 231))) (x2Tab t3 (t / 231) (t % 231)))) 6424 8 chkC_4_d6424) (x2c_join _ 6432 6440 8000 (x2c_range_all (fun t => (!(pOK tl tl (t % 231) (t / 231)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 231 % 77) * 282) (x2Tab o (t / 231 / 77) (t % 231))) (x2Tab t3 (t / 231) (t % 231)))) 6432 8 chkC_4_d6432) (x2c_join _ 6440 6448 8000 (x2c_range_all (fun t => (!(pOK tl tl (t % 231) (t / 231)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 231 % 77) * 282) (x2Tab o (t / 231 / 77) (t % 231))) (x2Tab t3 (t / 231) (t % 231)))) 6440 8 chkC_4_d6440) (x2c_join _ 6448 6456 8000 (x2c_range_all (fun t => (!(pOK tl tl (t % 231) (t / 231)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 231 % 77) * 282) (x2Tab o (t / 231 / 77) (t % 231))) (x2Tab t3 (t / 231) (t % 231)))) 6448 8 chkC_4_d6448) (x2c_join _ 6456 6464 8000 (x2c_range_all (fun t => (!(pOK tl tl (t % 231) (t / 231)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 231 % 77) * 282) (x2Tab o (t / 231 / 77) (t % 231))) (x2Tab t3 (t / 231) (t % 231)))) 6456 8 chkC_4_d6456) (x2c_join _ 6464 6472 8000 (x2c_range_all (fun t => (!(pOK tl tl (t % 231) (t / 231)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 231 % 77) * 282) (x2Tab o (t / 231 / 77) (t % 231))) (x2Tab t3 (t / 231) (t % 231)))) 6464 8 chkC_4_d6464) (x2c_join _ 6472 6480 8000 (x2c_range_all (fun t => (!(pOK tl tl (t % 231) (t / 231)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 231 % 77) * 282) (x2Tab o (t / 231 / 77) (t % 231))) (x2Tab t3 (t / 231) (t % 231)))) 6472 8 chkC_4_d6472) (x2c_join _ 6480 6488 8000 (x2c_range_all (fun t => (!(pOK tl tl (t % 231) (t / 231)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 231 % 77) * 282) (x2Tab o (t / 231 / 77) (t % 231))) (x2Tab t3 (t / 231) (t % 231)))) 6480 8 chkC_4_d6480) (x2c_join _ 6488 6496 8000 (x2c_range_all (fun t => (!(pOK tl tl (t % 231) (t / 231)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 231 % 77) * 282) (x2Tab o (t / 231 / 77) (t % 231))) (x2Tab t3 (t / 231) (t % 231)))) 6488 8 chkC_4_d6488) (x2c_join _ 6496 6504 8000 (x2c_range_all (fun t => (!(pOK tl tl (t % 231) (t / 231)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 231 % 77) * 282) (x2Tab o (t / 231 / 77) (t % 231))) (x2Tab t3 (t / 231) (t % 231)))) 6496 8 chkC_4_d6496) (x2c_join _ 6504 6512 8000 (x2c_range_all (fun t => (!(pOK tl tl (t % 231) (t / 231)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 231 % 77) * 282) (x2Tab o (t / 231 / 77) (t % 231))) (x2Tab t3 (t / 231) (t % 231)))) 6504 8 chkC_4_d6504) (x2c_join _ 6512 6520 8000 (x2c_range_all (fun t => (!(pOK tl tl (t % 231) (t / 231)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 231 % 77) * 282) (x2Tab o (t / 231 / 77) (t % 231))) (x2Tab t3 (t / 231) (t % 231)))) 6512 8 chkC_4_d6512) (x2c_join _ 6520 6528 8000 (x2c_range_all (fun t => (!(pOK tl tl (t % 231) (t / 231)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 231 % 77) * 282) (x2Tab o (t / 231 / 77) (t % 231))) (x2Tab t3 (t / 231) (t % 231)))) 6520 8 chkC_4_d6520) (x2c_join _ 6528 6536 8000 (x2c_range_all (fun t => (!(pOK tl tl (t % 231) (t / 231)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 231 % 77) * 282) (x2Tab o (t / 231 / 77) (t % 231))) (x2Tab t3 (t / 231) (t % 231)))) 6528 8 chkC_4_d6528) (x2c_join _ 6536 6544 8000 (x2c_range_all (fun t => (!(pOK tl tl (t % 231) (t / 231)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 231 % 77) * 282) (x2Tab o (t / 231 / 77) (t % 231))) (x2Tab t3 (t / 231) (t % 231)))) 6536 8 chkC_4_d6536) (x2c_join _ 6544 6552 8000 (x2c_range_all (fun t => (!(pOK tl tl (t % 231) (t / 231)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 231 % 77) * 282) (x2Tab o (t / 231 / 77) (t % 231))) (x2Tab t3 (t / 231) (t % 231)))) 6544 8 chkC_4_d6544) (x2c_join _ 6552 6560 8000 (x2c_range_all (fun t => (!(pOK tl tl (t % 231) (t / 231)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 231 % 77) * 282) (x2Tab o (t / 231 / 77) (t % 231))) (x2Tab t3 (t / 231) (t % 231)))) 6552 8 chkC_4_d6552) (x2c_join _ 6560 6568 8000 (x2c_range_all (fun t => (!(pOK tl tl (t % 231) (t / 231)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 231 % 77) * 282) (x2Tab o (t / 231 / 77) (t % 231))) (x2Tab t3 (t / 231) (t % 231)))) 6560 8 chkC_4_d6560) (x2c_join _ 6568 6576 8000 (x2c_range_all (fun t => (!(pOK tl tl (t % 231) (t / 231)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 231 % 77) * 282) (x2Tab o (t / 231 / 77) (t % 231))) (x2Tab t3 (t / 231) (t % 231)))) 6568 8 chkC_4_d6568) (x2c_join _ 6576 6584 8000 (x2c_range_all (fun t => (!(pOK tl tl (t % 231) (t / 231)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 231 % 77) * 282) (x2Tab o (t / 231 / 77) (t % 231))) (x2Tab t3 (t / 231) (t % 231)))) 6576 8 chkC_4_d6576) (x2c_join _ 6584 6592 8000 (x2c_range_all (fun t => (!(pOK tl tl (t % 231) (t / 231)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 231 % 77) * 282) (x2Tab o (t / 231 / 77) (t % 231))) (x2Tab t3 (t / 231) (t % 231)))) 6584 8 chkC_4_d6584) (x2c_join _ 6592 6600 8000 (x2c_range_all (fun t => (!(pOK tl tl (t % 231) (t / 231)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 231 % 77) * 282) (x2Tab o (t / 231 / 77) (t % 231))) (x2Tab t3 (t / 231) (t % 231)))) 6592 8 chkC_4_d6592) (x2c_join _ 6600 6608 8000 (x2c_range_all (fun t => (!(pOK tl tl (t % 231) (t / 231)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 231 % 77) * 282) (x2Tab o (t / 231 / 77) (t % 231))) (x2Tab t3 (t / 231) (t % 231)))) 6600 8 chkC_4_d6600) (x2c_join _ 6608 6616 8000 (x2c_range_all (fun t => (!(pOK tl tl (t % 231) (t / 231)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 231 % 77) * 282) (x2Tab o (t / 231 / 77) (t % 231))) (x2Tab t3 (t / 231) (t % 231)))) 6608 8 chkC_4_d6608) (x2c_join _ 6616 6624 8000 (x2c_range_all (fun t => (!(pOK tl tl (t % 231) (t / 231)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 231 % 77) * 282) (x2Tab o (t / 231 / 77) (t % 231))) (x2Tab t3 (t / 231) (t % 231)))) 6616 8 chkC_4_d6616) (x2c_join _ 6624 6632 8000 (x2c_range_all (fun t => (!(pOK tl tl (t % 231) (t / 231)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 231 % 77) * 282) (x2Tab o (t / 231 / 77) (t % 231))) (x2Tab t3 (t / 231) (t % 231)))) 6624 8 chkC_4_d6624) (x2c_join _ 6632 6640 8000 (x2c_range_all (fun t => (!(pOK tl tl (t % 231) (t / 231)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 231 % 77) * 282) (x2Tab o (t / 231 / 77) (t % 231))) (x2Tab t3 (t / 231) (t % 231)))) 6632 8 chkC_4_d6632) (x2c_join _ 6640 6648 8000 (x2c_range_all (fun t => (!(pOK tl tl (t % 231) (t / 231)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 231 % 77) * 282) (x2Tab o (t / 231 / 77) (t % 231))) (x2Tab t3 (t / 231) (t % 231)))) 6640 8 chkC_4_d6640) (x2c_join _ 6648 6656 8000 (x2c_range_all (fun t => (!(pOK tl tl (t % 231) (t / 231)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 231 % 77) * 282) (x2Tab o (t / 231 / 77) (t % 231))) (x2Tab t3 (t / 231) (t % 231)))) 6648 8 chkC_4_d6648) (x2c_join _ 6656 6664 8000 (x2c_range_all (fun t => (!(pOK tl tl (t % 231) (t / 231)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 231 % 77) * 282) (x2Tab o (t / 231 / 77) (t % 231))) (x2Tab t3 (t / 231) (t % 231)))) 6656 8 chkC_4_d6656) (x2c_join _ 6664 6672 8000 (x2c_range_all (fun t => (!(pOK tl tl (t % 231) (t / 231)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 231 % 77) * 282) (x2Tab o (t / 231 / 77) (t % 231))) (x2Tab t3 (t / 231) (t % 231)))) 6664 8 chkC_4_d6664) (x2c_join _ 6672 6680 8000 (x2c_range_all (fun t => (!(pOK tl tl (t % 231) (t / 231)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 231 % 77) * 282) (x2Tab o (t / 231 / 77) (t % 231))) (x2Tab t3 (t / 231) (t % 231)))) 6672 8 chkC_4_d6672) (x2c_join _ 6680 6688 8000 (x2c_range_all (fun t => (!(pOK tl tl (t % 231) (t / 231)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 231 % 77) * 282) (x2Tab o (t / 231 / 77) (t % 231))) (x2Tab t3 (t / 231) (t % 231)))) 6680 8 chkC_4_d6680) (x2c_join _ 6688 6696 8000 (x2c_range_all (fun t => (!(pOK tl tl (t % 231) (t / 231)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 231 % 77) * 282) (x2Tab o (t / 231 / 77) (t % 231))) (x2Tab t3 (t / 231) (t % 231)))) 6688 8 chkC_4_d6688) (x2c_join _ 6696 6704 8000 (x2c_range_all (fun t => (!(pOK tl tl (t % 231) (t / 231)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 231 % 77) * 282) (x2Tab o (t / 231 / 77) (t % 231))) (x2Tab t3 (t / 231) (t % 231)))) 6696 8 chkC_4_d6696) (x2c_join _ 6704 6712 8000 (x2c_range_all (fun t => (!(pOK tl tl (t % 231) (t / 231)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 231 % 77) * 282) (x2Tab o (t / 231 / 77) (t % 231))) (x2Tab t3 (t / 231) (t % 231)))) 6704 8 chkC_4_d6704) (x2c_join _ 6712 6720 8000 (x2c_range_all (fun t => (!(pOK tl tl (t % 231) (t / 231)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 231 % 77) * 282) (x2Tab o (t / 231 / 77) (t % 231))) (x2Tab t3 (t / 231) (t % 231)))) 6712 8 chkC_4_d6712) (x2c_join _ 6720 6728 8000 (x2c_range_all (fun t => (!(pOK tl tl (t % 231) (t / 231)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 231 % 77) * 282) (x2Tab o (t / 231 / 77) (t % 231))) (x2Tab t3 (t / 231) (t % 231)))) 6720 8 chkC_4_d6720) (x2c_join _ 6728 6736 8000 (x2c_range_all (fun t => (!(pOK tl tl (t % 231) (t / 231)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 231 % 77) * 282) (x2Tab o (t / 231 / 77) (t % 231))) (x2Tab t3 (t / 231) (t % 231)))) 6728 8 chkC_4_d6728) (x2c_join _ 6736 6744 8000 (x2c_range_all (fun t => (!(pOK tl tl (t % 231) (t / 231)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 231 % 77) * 282) (x2Tab o (t / 231 / 77) (t % 231))) (x2Tab t3 (t / 231) (t % 231)))) 6736 8 chkC_4_d6736) (x2c_join _ 6744 6752 8000 (x2c_range_all (fun t => (!(pOK tl tl (t % 231) (t / 231)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 231 % 77) * 282) (x2Tab o (t / 231 / 77) (t % 231))) (x2Tab t3 (t / 231) (t % 231)))) 6744 8 chkC_4_d6744) (x2c_join _ 6752 6760 8000 (x2c_range_all (fun t => (!(pOK tl tl (t % 231) (t / 231)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 231 % 77) * 282) (x2Tab o (t / 231 / 77) (t % 231))) (x2Tab t3 (t / 231) (t % 231)))) 6752 8 chkC_4_d6752) (x2c_join _ 6760 6768 8000 (x2c_range_all (fun t => (!(pOK tl tl (t % 231) (t / 231)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 231 % 77) * 282) (x2Tab o (t / 231 / 77) (t % 231))) (x2Tab t3 (t / 231) (t % 231)))) 6760 8 chkC_4_d6760) (x2c_join _ 6768 6776 8000 (x2c_range_all (fun t => (!(pOK tl tl (t % 231) (t / 231)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 231 % 77) * 282) (x2Tab o (t / 231 / 77) (t % 231))) (x2Tab t3 (t / 231) (t % 231)))) 6768 8 chkC_4_d6768) (x2c_join _ 6776 6784 8000 (x2c_range_all (fun t => (!(pOK tl tl (t % 231) (t / 231)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 231 % 77) * 282) (x2Tab o (t / 231 / 77) (t % 231))) (x2Tab t3 (t / 231) (t % 231)))) 6776 8 chkC_4_d6776) (x2c_join _ 6784 6792 8000 (x2c_range_all (fun t => (!(pOK tl tl (t % 231) (t / 231)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 231 % 77) * 282) (x2Tab o (t / 231 / 77) (t % 231))) (x2Tab t3 (t / 231) (t % 231)))) 6784 8 chkC_4_d6784) (x2c_join _ 6792 6800 8000 (x2c_range_all (fun t => (!(pOK tl tl (t % 231) (t / 231)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 231 % 77) * 282) (x2Tab o (t / 231 / 77) (t % 231))) (x2Tab t3 (t / 231) (t % 231)))) 6792 8 chkC_4_d6792) (x2c_join _ 6800 6808 8000 (x2c_range_all (fun t => (!(pOK tl tl (t % 231) (t / 231)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 231 % 77) * 282) (x2Tab o (t / 231 / 77) (t % 231))) (x2Tab t3 (t / 231) (t % 231)))) 6800 8 chkC_4_d6800) (x2c_join _ 6808 6816 8000 (x2c_range_all (fun t => (!(pOK tl tl (t % 231) (t / 231)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 231 % 77) * 282) (x2Tab o (t / 231 / 77) (t % 231))) (x2Tab t3 (t / 231) (t % 231)))) 6808 8 chkC_4_d6808) (x2c_join _ 6816 6824 8000 (x2c_range_all (fun t => (!(pOK tl tl (t % 231) (t / 231)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 231 % 77) * 282) (x2Tab o (t / 231 / 77) (t % 231))) (x2Tab t3 (t / 231) (t % 231)))) 6816 8 chkC_4_d6816) (x2c_join _ 6824 6832 8000 (x2c_range_all (fun t => (!(pOK tl tl (t % 231) (t / 231)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 231 % 77) * 282) (x2Tab o (t / 231 / 77) (t % 231))) (x2Tab t3 (t / 231) (t % 231)))) 6824 8 chkC_4_d6824) (x2c_join _ 6832 6840 8000 (x2c_range_all (fun t => (!(pOK tl tl (t % 231) (t / 231)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 231 % 77) * 282) (x2Tab o (t / 231 / 77) (t % 231))) (x2Tab t3 (t / 231) (t % 231)))) 6832 8 chkC_4_d6832) (x2c_join _ 6840 6848 8000 (x2c_range_all (fun t => (!(pOK tl tl (t % 231) (t / 231)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 231 % 77) * 282) (x2Tab o (t / 231 / 77) (t % 231))) (x2Tab t3 (t / 231) (t % 231)))) 6840 8 chkC_4_d6840) (x2c_join _ 6848 6856 8000 (x2c_range_all (fun t => (!(pOK tl tl (t % 231) (t / 231)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 231 % 77) * 282) (x2Tab o (t / 231 / 77) (t % 231))) (x2Tab t3 (t / 231) (t % 231)))) 6848 8 chkC_4_d6848) (x2c_join _ 6856 6864 8000 (x2c_range_all (fun t => (!(pOK tl tl (t % 231) (t / 231)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 231 % 77) * 282) (x2Tab o (t / 231 / 77) (t % 231))) (x2Tab t3 (t / 231) (t % 231)))) 6856 8 chkC_4_d6856) (x2c_join _ 6864 6872 8000 (x2c_range_all (fun t => (!(pOK tl tl (t % 231) (t / 231)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 231 % 77) * 282) (x2Tab o (t / 231 / 77) (t % 231))) (x2Tab t3 (t / 231) (t % 231)))) 6864 8 chkC_4_d6864) (x2c_join _ 6872 6880 8000 (x2c_range_all (fun t => (!(pOK tl tl (t % 231) (t / 231)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 231 % 77) * 282) (x2Tab o (t / 231 / 77) (t % 231))) (x2Tab t3 (t / 231) (t % 231)))) 6872 8 chkC_4_d6872) (x2c_join _ 6880 6888 8000 (x2c_range_all (fun t => (!(pOK tl tl (t % 231) (t / 231)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 231 % 77) * 282) (x2Tab o (t / 231 / 77) (t % 231))) (x2Tab t3 (t / 231) (t % 231)))) 6880 8 chkC_4_d6880) (x2c_join _ 6888 6896 8000 (x2c_range_all (fun t => (!(pOK tl tl (t % 231) (t / 231)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 231 % 77) * 282) (x2Tab o (t / 231 / 77) (t % 231))) (x2Tab t3 (t / 231) (t % 231)))) 6888 8 chkC_4_d6888) (x2c_join _ 6896 6904 8000 (x2c_range_all (fun t => (!(pOK tl tl (t % 231) (t / 231)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 231 % 77) * 282) (x2Tab o (t / 231 / 77) (t % 231))) (x2Tab t3 (t / 231) (t % 231)))) 6896 8 chkC_4_d6896) (x2c_join _ 6904 6912 8000 (x2c_range_all (fun t => (!(pOK tl tl (t % 231) (t / 231)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 231 % 77) * 282) (x2Tab o (t / 231 / 77) (t % 231))) (x2Tab t3 (t / 231) (t % 231)))) 6904 8 chkC_4_d6904) (x2c_join _ 6912 6920 8000 (x2c_range_all (fun t => (!(pOK tl tl (t % 231) (t / 231)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 231 % 77) * 282) (x2Tab o (t / 231 / 77) (t % 231))) (x2Tab t3 (t / 231) (t % 231)))) 6912 8 chkC_4_d6912) (x2c_join _ 6920 6928 8000 (x2c_range_all (fun t => (!(pOK tl tl (t % 231) (t / 231)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 231 % 77) * 282) (x2Tab o (t / 231 / 77) (t % 231))) (x2Tab t3 (t / 231) (t % 231)))) 6920 8 chkC_4_d6920) (x2c_join _ 6928 6936 8000 (x2c_range_all (fun t => (!(pOK tl tl (t % 231) (t / 231)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 231 % 77) * 282) (x2Tab o (t / 231 / 77) (t % 231))) (x2Tab t3 (t / 231) (t % 231)))) 6928 8 chkC_4_d6928) (x2c_join _ 6936 6944 8000 (x2c_range_all (fun t => (!(pOK tl tl (t % 231) (t / 231)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 231 % 77) * 282) (x2Tab o (t / 231 / 77) (t % 231))) (x2Tab t3 (t / 231) (t % 231)))) 6936 8 chkC_4_d6936) (x2c_join _ 6944 6952 8000 (x2c_range_all (fun t => (!(pOK tl tl (t % 231) (t / 231)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 231 % 77) * 282) (x2Tab o (t / 231 / 77) (t % 231))) (x2Tab t3 (t / 231) (t % 231)))) 6944 8 chkC_4_d6944) (x2c_join _ 6952 6960 8000 (x2c_range_all (fun t => (!(pOK tl tl (t % 231) (t / 231)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 231 % 77) * 282) (x2Tab o (t / 231 / 77) (t % 231))) (x2Tab t3 (t / 231) (t % 231)))) 6952 8 chkC_4_d6952) (x2c_join _ 6960 6968 8000 (x2c_range_all (fun t => (!(pOK tl tl (t % 231) (t / 231)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 231 % 77) * 282) (x2Tab o (t / 231 / 77) (t % 231))) (x2Tab t3 (t / 231) (t % 231)))) 6960 8 chkC_4_d6960) (x2c_join _ 6968 6976 8000 (x2c_range_all (fun t => (!(pOK tl tl (t % 231) (t / 231)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 231 % 77) * 282) (x2Tab o (t / 231 / 77) (t % 231))) (x2Tab t3 (t / 231) (t % 231)))) 6968 8 chkC_4_d6968) (x2c_join _ 6976 6984 8000 (x2c_range_all (fun t => (!(pOK tl tl (t % 231) (t / 231)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 231 % 77) * 282) (x2Tab o (t / 231 / 77) (t % 231))) (x2Tab t3 (t / 231) (t % 231)))) 6976 8 chkC_4_d6976) (x2c_join _ 6984 6992 8000 (x2c_range_all (fun t => (!(pOK tl tl (t % 231) (t / 231)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 231 % 77) * 282) (x2Tab o (t / 231 / 77) (t % 231))) (x2Tab t3 (t / 231) (t % 231)))) 6984 8 chkC_4_d6984) (x2c_join _ 6992 7000 8000 (x2c_range_all (fun t => (!(pOK tl tl (t % 231) (t / 231)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 231 % 77) * 282) (x2Tab o (t / 231 / 77) (t % 231))) (x2Tab t3 (t / 231) (t % 231)))) 6992 8 chkC_4_d6992) (x2c_join _ 7000 7008 8000 (x2c_range_all (fun t => (!(pOK tl tl (t % 231) (t / 231)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 231 % 77) * 282) (x2Tab o (t / 231 / 77) (t % 231))) (x2Tab t3 (t / 231) (t % 231)))) 7000 8 chkC_4_d7000) (x2c_join _ 7008 7016 8000 (x2c_range_all (fun t => (!(pOK tl tl (t % 231) (t / 231)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 231 % 77) * 282) (x2Tab o (t / 231 / 77) (t % 231))) (x2Tab t3 (t / 231) (t % 231)))) 7008 8 chkC_4_d7008) (x2c_join _ 7016 7024 8000 (x2c_range_all (fun t => (!(pOK tl tl (t % 231) (t / 231)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 231 % 77) * 282) (x2Tab o (t / 231 / 77) (t % 231))) (x2Tab t3 (t / 231) (t % 231)))) 7016 8 chkC_4_d7016) (x2c_join _ 7024 7032 8000 (x2c_range_all (fun t => (!(pOK tl tl (t % 231) (t / 231)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 231 % 77) * 282) (x2Tab o (t / 231 / 77) (t % 231))) (x2Tab t3 (t / 231) (t % 231)))) 7024 8 chkC_4_d7024) (x2c_join _ 7032 7040 8000 (x2c_range_all (fun t => (!(pOK tl tl (t % 231) (t / 231)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 231 % 77) * 282) (x2Tab o (t / 231 / 77) (t % 231))) (x2Tab t3 (t / 231) (t % 231)))) 7032 8 chkC_4_d7032) (x2c_join _ 7040 7048 8000 (x2c_range_all (fun t => (!(pOK tl tl (t % 231) (t / 231)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 231 % 77) * 282) (x2Tab o (t / 231 / 77) (t % 231))) (x2Tab t3 (t / 231) (t % 231)))) 7040 8 chkC_4_d7040) (x2c_join _ 7048 7056 8000 (x2c_range_all (fun t => (!(pOK tl tl (t % 231) (t / 231)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 231 % 77) * 282) (x2Tab o (t / 231 / 77) (t % 231))) (x2Tab t3 (t / 231) (t % 231)))) 7048 8 chkC_4_d7048) (x2c_join _ 7056 7064 8000 (x2c_range_all (fun t => (!(pOK tl tl (t % 231) (t / 231)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 231 % 77) * 282) (x2Tab o (t / 231 / 77) (t % 231))) (x2Tab t3 (t / 231) (t % 231)))) 7056 8 chkC_4_d7056) (x2c_join _ 7064 7072 8000 (x2c_range_all (fun t => (!(pOK tl tl (t % 231) (t / 231)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 231 % 77) * 282) (x2Tab o (t / 231 / 77) (t % 231))) (x2Tab t3 (t / 231) (t % 231)))) 7064 8 chkC_4_d7064) (x2c_join _ 7072 7080 8000 (x2c_range_all (fun t => (!(pOK tl tl (t % 231) (t / 231)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 231 % 77) * 282) (x2Tab o (t / 231 / 77) (t % 231))) (x2Tab t3 (t / 231) (t % 231)))) 7072 8 chkC_4_d7072) (x2c_join _ 7080 7088 8000 (x2c_range_all (fun t => (!(pOK tl tl (t % 231) (t / 231)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 231 % 77) * 282) (x2Tab o (t / 231 / 77) (t % 231))) (x2Tab t3 (t / 231) (t % 231)))) 7080 8 chkC_4_d7080) (x2c_join _ 7088 7096 8000 (x2c_range_all (fun t => (!(pOK tl tl (t % 231) (t / 231)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 231 % 77) * 282) (x2Tab o (t / 231 / 77) (t % 231))) (x2Tab t3 (t / 231) (t % 231)))) 7088 8 chkC_4_d7088) (x2c_join _ 7096 7104 8000 (x2c_range_all (fun t => (!(pOK tl tl (t % 231) (t / 231)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 231 % 77) * 282) (x2Tab o (t / 231 / 77) (t % 231))) (x2Tab t3 (t / 231) (t % 231)))) 7096 8 chkC_4_d7096) (x2c_join _ 7104 7112 8000 (x2c_range_all (fun t => (!(pOK tl tl (t % 231) (t / 231)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 231 % 77) * 282) (x2Tab o (t / 231 / 77) (t % 231))) (x2Tab t3 (t / 231) (t % 231)))) 7104 8 chkC_4_d7104) (x2c_join _ 7112 7120 8000 (x2c_range_all (fun t => (!(pOK tl tl (t % 231) (t / 231)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 231 % 77) * 282) (x2Tab o (t / 231 / 77) (t % 231))) (x2Tab t3 (t / 231) (t % 231)))) 7112 8 chkC_4_d7112) (x2c_join _ 7120 7128 8000 (x2c_range_all (fun t => (!(pOK tl tl (t % 231) (t / 231)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 231 % 77) * 282) (x2Tab o (t / 231 / 77) (t % 231))) (x2Tab t3 (t / 231) (t % 231)))) 7120 8 chkC_4_d7120) (x2c_join _ 7128 7136 8000 (x2c_range_all (fun t => (!(pOK tl tl (t % 231) (t / 231)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 231 % 77) * 282) (x2Tab o (t / 231 / 77) (t % 231))) (x2Tab t3 (t / 231) (t % 231)))) 7128 8 chkC_4_d7128) (x2c_join _ 7136 7144 8000 (x2c_range_all (fun t => (!(pOK tl tl (t % 231) (t / 231)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 231 % 77) * 282) (x2Tab o (t / 231 / 77) (t % 231))) (x2Tab t3 (t / 231) (t % 231)))) 7136 8 chkC_4_d7136) (x2c_join _ 7144 7152 8000 (x2c_range_all (fun t => (!(pOK tl tl (t % 231) (t / 231)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 231 % 77) * 282) (x2Tab o (t / 231 / 77) (t % 231))) (x2Tab t3 (t / 231) (t % 231)))) 7144 8 chkC_4_d7144) (x2c_join _ 7152 7160 8000 (x2c_range_all (fun t => (!(pOK tl tl (t % 231) (t / 231)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 231 % 77) * 282) (x2Tab o (t / 231 / 77) (t % 231))) (x2Tab t3 (t / 231) (t % 231)))) 7152 8 chkC_4_d7152) (x2c_join _ 7160 7168 8000 (x2c_range_all (fun t => (!(pOK tl tl (t % 231) (t / 231)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 231 % 77) * 282) (x2Tab o (t / 231 / 77) (t % 231))) (x2Tab t3 (t / 231) (t % 231)))) 7160 8 chkC_4_d7160) (x2c_join _ 7168 7176 8000 (x2c_range_all (fun t => (!(pOK tl tl (t % 231) (t / 231)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 231 % 77) * 282) (x2Tab o (t / 231 / 77) (t % 231))) (x2Tab t3 (t / 231) (t % 231)))) 7168 8 chkC_4_d7168) (x2c_join _ 7176 7184 8000 (x2c_range_all (fun t => (!(pOK tl tl (t % 231) (t / 231)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 231 % 77) * 282) (x2Tab o (t / 231 / 77) (t % 231))) (x2Tab t3 (t / 231) (t % 231)))) 7176 8 chkC_4_d7176) (x2c_join _ 7184 7192 8000 (x2c_range_all (fun t => (!(pOK tl tl (t % 231) (t / 231)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 231 % 77) * 282) (x2Tab o (t / 231 / 77) (t % 231))) (x2Tab t3 (t / 231) (t % 231)))) 7184 8 chkC_4_d7184) (x2c_join _ 7192 7200 8000 (x2c_range_all (fun t => (!(pOK tl tl (t % 231) (t / 231)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 231 % 77) * 282) (x2Tab o (t / 231 / 77) (t % 231))) (x2Tab t3 (t / 231) (t % 231)))) 7192 8 chkC_4_d7192) (x2c_join _ 7200 7208 8000 (x2c_range_all (fun t => (!(pOK tl tl (t % 231) (t / 231)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 231 % 77) * 282) (x2Tab o (t / 231 / 77) (t % 231))) (x2Tab t3 (t / 231) (t % 231)))) 7200 8 chkC_4_d7200) (x2c_join _ 7208 7216 8000 (x2c_range_all (fun t => (!(pOK tl tl (t % 231) (t / 231)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 231 % 77) * 282) (x2Tab o (t / 231 / 77) (t % 231))) (x2Tab t3 (t / 231) (t % 231)))) 7208 8 chkC_4_d7208) (x2c_join _ 7216 7224 8000 (x2c_range_all (fun t => (!(pOK tl tl (t % 231) (t / 231)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 231 % 77) * 282) (x2Tab o (t / 231 / 77) (t % 231))) (x2Tab t3 (t / 231) (t % 231)))) 7216 8 chkC_4_d7216) (x2c_join _ 7224 7232 8000 (x2c_range_all (fun t => (!(pOK tl tl (t % 231) (t / 231)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 231 % 77) * 282) (x2Tab o (t / 231 / 77) (t % 231))) (x2Tab t3 (t / 231) (t % 231)))) 7224 8 chkC_4_d7224) (x2c_join _ 7232 7240 8000 (x2c_range_all (fun t => (!(pOK tl tl (t % 231) (t / 231)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 231 % 77) * 282) (x2Tab o (t / 231 / 77) (t % 231))) (x2Tab t3 (t / 231) (t % 231)))) 7232 8 chkC_4_d7232) (x2c_join _ 7240 7248 8000 (x2c_range_all (fun t => (!(pOK tl tl (t % 231) (t / 231)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 231 % 77) * 282) (x2Tab o (t / 231 / 77) (t % 231))) (x2Tab t3 (t / 231) (t % 231)))) 7240 8 chkC_4_d7240) (x2c_join _ 7248 7256 8000 (x2c_range_all (fun t => (!(pOK tl tl (t % 231) (t / 231)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 231 % 77) * 282) (x2Tab o (t / 231 / 77) (t % 231))) (x2Tab t3 (t / 231) (t % 231)))) 7248 8 chkC_4_d7248) (x2c_join _ 7256 7264 8000 (x2c_range_all (fun t => (!(pOK tl tl (t % 231) (t / 231)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 231 % 77) * 282) (x2Tab o (t / 231 / 77) (t % 231))) (x2Tab t3 (t / 231) (t % 231)))) 7256 8 chkC_4_d7256) (x2c_join _ 7264 7272 8000 (x2c_range_all (fun t => (!(pOK tl tl (t % 231) (t / 231)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 231 % 77) * 282) (x2Tab o (t / 231 / 77) (t % 231))) (x2Tab t3 (t / 231) (t % 231)))) 7264 8 chkC_4_d7264) (x2c_join _ 7272 7280 8000 (x2c_range_all (fun t => (!(pOK tl tl (t % 231) (t / 231)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 231 % 77) * 282) (x2Tab o (t / 231 / 77) (t % 231))) (x2Tab t3 (t / 231) (t % 231)))) 7272 8 chkC_4_d7272) (x2c_join _ 7280 7288 8000 (x2c_range_all (fun t => (!(pOK tl tl (t % 231) (t / 231)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 231 % 77) * 282) (x2Tab o (t / 231 / 77) (t % 231))) (x2Tab t3 (t / 231) (t % 231)))) 7280 8 chkC_4_d7280) (x2c_join _ 7288 7296 8000 (x2c_range_all (fun t => (!(pOK tl tl (t % 231) (t / 231)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 231 % 77) * 282) (x2Tab o (t / 231 / 77) (t % 231))) (x2Tab t3 (t / 231) (t % 231)))) 7288 8 chkC_4_d7288) (x2c_join _ 7296 7304 8000 (x2c_range_all (fun t => (!(pOK tl tl (t % 231) (t / 231)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 231 % 77) * 282) (x2Tab o (t / 231 / 77) (t % 231))) (x2Tab t3 (t / 231) (t % 231)))) 7296 8 chkC_4_d7296) (x2c_join _ 7304 7312 8000 (x2c_range_all (fun t => (!(pOK tl tl (t % 231) (t / 231)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 231 % 77) * 282) (x2Tab o (t / 231 / 77) (t % 231))) (x2Tab t3 (t / 231) (t % 231)))) 7304 8 chkC_4_d7304) (x2c_join _ 7312 7320 8000 (x2c_range_all (fun t => (!(pOK tl tl (t % 231) (t / 231)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 231 % 77) * 282) (x2Tab o (t / 231 / 77) (t % 231))) (x2Tab t3 (t / 231) (t % 231)))) 7312 8 chkC_4_d7312) (x2c_join _ 7320 7328 8000 (x2c_range_all (fun t => (!(pOK tl tl (t % 231) (t / 231)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 231 % 77) * 282) (x2Tab o (t / 231 / 77) (t % 231))) (x2Tab t3 (t / 231) (t % 231)))) 7320 8 chkC_4_d7320) (x2c_join _ 7328 7336 8000 (x2c_range_all (fun t => (!(pOK tl tl (t % 231) (t / 231)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 231 % 77) * 282) (x2Tab o (t / 231 / 77) (t % 231))) (x2Tab t3 (t / 231) (t % 231)))) 7328 8 chkC_4_d7328) (x2c_join _ 7336 7344 8000 (x2c_range_all (fun t => (!(pOK tl tl (t % 231) (t / 231)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 231 % 77) * 282) (x2Tab o (t / 231 / 77) (t % 231))) (x2Tab t3 (t / 231) (t % 231)))) 7336 8 chkC_4_d7336) (x2c_join _ 7344 7352 8000 (x2c_range_all (fun t => (!(pOK tl tl (t % 231) (t / 231)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 231 % 77) * 282) (x2Tab o (t / 231 / 77) (t % 231))) (x2Tab t3 (t / 231) (t % 231)))) 7344 8 chkC_4_d7344) (x2c_join _ 7352 7360 8000 (x2c_range_all (fun t => (!(pOK tl tl (t % 231) (t / 231)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 231 % 77) * 282) (x2Tab o (t / 231 / 77) (t % 231))) (x2Tab t3 (t / 231) (t % 231)))) 7352 8 chkC_4_d7352) (x2c_join _ 7360 7368 8000 (x2c_range_all (fun t => (!(pOK tl tl (t % 231) (t / 231)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 231 % 77) * 282) (x2Tab o (t / 231 / 77) (t % 231))) (x2Tab t3 (t / 231) (t % 231)))) 7360 8 chkC_4_d7360) (x2c_join _ 7368 7376 8000 (x2c_range_all (fun t => (!(pOK tl tl (t % 231) (t / 231)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 231 % 77) * 282) (x2Tab o (t / 231 / 77) (t % 231))) (x2Tab t3 (t / 231) (t % 231)))) 7368 8 chkC_4_d7368) (x2c_join _ 7376 7384 8000 (x2c_range_all (fun t => (!(pOK tl tl (t % 231) (t / 231)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 231 % 77) * 282) (x2Tab o (t / 231 / 77) (t % 231))) (x2Tab t3 (t / 231) (t % 231)))) 7376 8 chkC_4_d7376) (x2c_join _ 7384 7392 8000 (x2c_range_all (fun t => (!(pOK tl tl (t % 231) (t / 231)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 231 % 77) * 282) (x2Tab o (t / 231 / 77) (t % 231))) (x2Tab t3 (t / 231) (t % 231)))) 7384 8 chkC_4_d7384) (x2c_join _ 7392 7400 8000 (x2c_range_all (fun t => (!(pOK tl tl (t % 231) (t / 231)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 231 % 77) * 282) (x2Tab o (t / 231 / 77) (t % 231))) (x2Tab t3 (t / 231) (t % 231)))) 7392 8 chkC_4_d7392) (x2c_join _ 7400 7408 8000 (x2c_range_all (fun t => (!(pOK tl tl (t % 231) (t / 231)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 231 % 77) * 282) (x2Tab o (t / 231 / 77) (t % 231))) (x2Tab t3 (t / 231) (t % 231)))) 7400 8 chkC_4_d7400) (x2c_join _ 7408 7416 8000 (x2c_range_all (fun t => (!(pOK tl tl (t % 231) (t / 231)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 231 % 77) * 282) (x2Tab o (t / 231 / 77) (t % 231))) (x2Tab t3 (t / 231) (t % 231)))) 7408 8 chkC_4_d7408) (x2c_join _ 7416 7424 8000 (x2c_range_all (fun t => (!(pOK tl tl (t % 231) (t / 231)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 231 % 77) * 282) (x2Tab o (t / 231 / 77) (t % 231))) (x2Tab t3 (t / 231) (t % 231)))) 7416 8 chkC_4_d7416) (x2c_join _ 7424 7432 8000 (x2c_range_all (fun t => (!(pOK tl tl (t % 231) (t / 231)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 231 % 77) * 282) (x2Tab o (t / 231 / 77) (t % 231))) (x2Tab t3 (t / 231) (t % 231)))) 7424 8 chkC_4_d7424) (x2c_join _ 7432 7440 8000 (x2c_range_all (fun t => (!(pOK tl tl (t % 231) (t / 231)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 231 % 77) * 282) (x2Tab o (t / 231 / 77) (t % 231))) (x2Tab t3 (t / 231) (t % 231)))) 7432 8 chkC_4_d7432) (x2c_join _ 7440 7448 8000 (x2c_range_all (fun t => (!(pOK tl tl (t % 231) (t / 231)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 231 % 77) * 282) (x2Tab o (t / 231 / 77) (t % 231))) (x2Tab t3 (t / 231) (t % 231)))) 7440 8 chkC_4_d7440) (x2c_join _ 7448 7456 8000 (x2c_range_all (fun t => (!(pOK tl tl (t % 231) (t / 231)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 231 % 77) * 282) (x2Tab o (t / 231 / 77) (t % 231))) (x2Tab t3 (t / 231) (t % 231)))) 7448 8 chkC_4_d7448) (x2c_join _ 7456 7464 8000 (x2c_range_all (fun t => (!(pOK tl tl (t % 231) (t / 231)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 231 % 77) * 282) (x2Tab o (t / 231 / 77) (t % 231))) (x2Tab t3 (t / 231) (t % 231)))) 7456 8 chkC_4_d7456) (x2c_join _ 7464 7472 8000 (x2c_range_all (fun t => (!(pOK tl tl (t % 231) (t / 231)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 231 % 77) * 282) (x2Tab o (t / 231 / 77) (t % 231))) (x2Tab t3 (t / 231) (t % 231)))) 7464 8 chkC_4_d7464) (x2c_join _ 7472 7480 8000 (x2c_range_all (fun t => (!(pOK tl tl (t % 231) (t / 231)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 231 % 77) * 282) (x2Tab o (t / 231 / 77) (t % 231))) (x2Tab t3 (t / 231) (t % 231)))) 7472 8 chkC_4_d7472) (x2c_join _ 7480 7488 8000 (x2c_range_all (fun t => (!(pOK tl tl (t % 231) (t / 231)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 231 % 77) * 282) (x2Tab o (t / 231 / 77) (t % 231))) (x2Tab t3 (t / 231) (t % 231)))) 7480 8 chkC_4_d7480) (x2c_join _ 7488 7496 8000 (x2c_range_all (fun t => (!(pOK tl tl (t % 231) (t / 231)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 231 % 77) * 282) (x2Tab o (t / 231 / 77) (t % 231))) (x2Tab t3 (t / 231) (t % 231)))) 7488 8 chkC_4_d7488) (x2c_join _ 7496 7504 8000 (x2c_range_all (fun t => (!(pOK tl tl (t % 231) (t / 231)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 231 % 77) * 282) (x2Tab o (t / 231 / 77) (t % 231))) (x2Tab t3 (t / 231) (t % 231)))) 7496 8 chkC_4_d7496) (x2c_join _ 7504 7512 8000 (x2c_range_all (fun t => (!(pOK tl tl (t % 231) (t / 231)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 231 % 77) * 282) (x2Tab o (t / 231 / 77) (t % 231))) (x2Tab t3 (t / 231) (t % 231)))) 7504 8 chkC_4_d7504) (x2c_join _ 7512 7520 8000 (x2c_range_all (fun t => (!(pOK tl tl (t % 231) (t / 231)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 231 % 77) * 282) (x2Tab o (t / 231 / 77) (t % 231))) (x2Tab t3 (t / 231) (t % 231)))) 7512 8 chkC_4_d7512) (x2c_join _ 7520 7528 8000 (x2c_range_all (fun t => (!(pOK tl tl (t % 231) (t / 231)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 231 % 77) * 282) (x2Tab o (t / 231 / 77) (t % 231))) (x2Tab t3 (t / 231) (t % 231)))) 7520 8 chkC_4_d7520) (x2c_join _ 7528 7536 8000 (x2c_range_all (fun t => (!(pOK tl tl (t % 231) (t / 231)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 231 % 77) * 282) (x2Tab o (t / 231 / 77) (t % 231))) (x2Tab t3 (t / 231) (t % 231)))) 7528 8 chkC_4_d7528) (x2c_join _ 7536 7544 8000 (x2c_range_all (fun t => (!(pOK tl tl (t % 231) (t / 231)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 231 % 77) * 282) (x2Tab o (t / 231 / 77) (t % 231))) (x2Tab t3 (t / 231) (t % 231)))) 7536 8 chkC_4_d7536) (x2c_join _ 7544 7552 8000 (x2c_range_all (fun t => (!(pOK tl tl (t % 231) (t / 231)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 231 % 77) * 282) (x2Tab o (t / 231 / 77) (t % 231))) (x2Tab t3 (t / 231) (t % 231)))) 7544 8 chkC_4_d7544) (x2c_join _ 7552 7560 8000 (x2c_range_all (fun t => (!(pOK tl tl (t % 231) (t / 231)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 231 % 77) * 282) (x2Tab o (t / 231 / 77) (t % 231))) (x2Tab t3 (t / 231) (t % 231)))) 7552 8 chkC_4_d7552) (x2c_join _ 7560 7568 8000 (x2c_range_all (fun t => (!(pOK tl tl (t % 231) (t / 231)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 231 % 77) * 282) (x2Tab o (t / 231 / 77) (t % 231))) (x2Tab t3 (t / 231) (t % 231)))) 7560 8 chkC_4_d7560) (x2c_join _ 7568 7576 8000 (x2c_range_all (fun t => (!(pOK tl tl (t % 231) (t / 231)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 231 % 77) * 282) (x2Tab o (t / 231 / 77) (t % 231))) (x2Tab t3 (t / 231) (t % 231)))) 7568 8 chkC_4_d7568) (x2c_join _ 7576 7584 8000 (x2c_range_all (fun t => (!(pOK tl tl (t % 231) (t / 231)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 231 % 77) * 282) (x2Tab o (t / 231 / 77) (t % 231))) (x2Tab t3 (t / 231) (t % 231)))) 7576 8 chkC_4_d7576) (x2c_join _ 7584 7592 8000 (x2c_range_all (fun t => (!(pOK tl tl (t % 231) (t / 231)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 231 % 77) * 282) (x2Tab o (t / 231 / 77) (t % 231))) (x2Tab t3 (t / 231) (t % 231)))) 7584 8 chkC_4_d7584) (x2c_join _ 7592 7600 8000 (x2c_range_all (fun t => (!(pOK tl tl (t % 231) (t / 231)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 231 % 77) * 282) (x2Tab o (t / 231 / 77) (t % 231))) (x2Tab t3 (t / 231) (t % 231)))) 7592 8 chkC_4_d7592) (x2c_join _ 7600 7608 8000 (x2c_range_all (fun t => (!(pOK tl tl (t % 231) (t / 231)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 231 % 77) * 282) (x2Tab o (t / 231 / 77) (t % 231))) (x2Tab t3 (t / 231) (t % 231)))) 7600 8 chkC_4_d7600) (x2c_join _ 7608 7616 8000 (x2c_range_all (fun t => (!(pOK tl tl (t % 231) (t / 231)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 231 % 77) * 282) (x2Tab o (t / 231 / 77) (t % 231))) (x2Tab t3 (t / 231) (t % 231)))) 7608 8 chkC_4_d7608) (x2c_join _ 7616 7624 8000 (x2c_range_all (fun t => (!(pOK tl tl (t % 231) (t / 231)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 231 % 77) * 282) (x2Tab o (t / 231 / 77) (t % 231))) (x2Tab t3 (t / 231) (t % 231)))) 7616 8 chkC_4_d7616) (x2c_join _ 7624 7632 8000 (x2c_range_all (fun t => (!(pOK tl tl (t % 231) (t / 231)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 231 % 77) * 282) (x2Tab o (t / 231 / 77) (t % 231))) (x2Tab t3 (t / 231) (t % 231)))) 7624 8 chkC_4_d7624) (x2c_join _ 7632 7640 8000 (x2c_range_all (fun t => (!(pOK tl tl (t % 231) (t / 231)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 231 % 77) * 282) (x2Tab o (t / 231 / 77) (t % 231))) (x2Tab t3 (t / 231) (t % 231)))) 7632 8 chkC_4_d7632) (x2c_join _ 7640 7648 8000 (x2c_range_all (fun t => (!(pOK tl tl (t % 231) (t / 231)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 231 % 77) * 282) (x2Tab o (t / 231 / 77) (t % 231))) (x2Tab t3 (t / 231) (t % 231)))) 7640 8 chkC_4_d7640) (x2c_join _ 7648 7656 8000 (x2c_range_all (fun t => (!(pOK tl tl (t % 231) (t / 231)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 231 % 77) * 282) (x2Tab o (t / 231 / 77) (t % 231))) (x2Tab t3 (t / 231) (t % 231)))) 7648 8 chkC_4_d7648) (x2c_join _ 7656 7664 8000 (x2c_range_all (fun t => (!(pOK tl tl (t % 231) (t / 231)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 231 % 77) * 282) (x2Tab o (t / 231 / 77) (t % 231))) (x2Tab t3 (t / 231) (t % 231)))) 7656 8 chkC_4_d7656) (x2c_join _ 7664 7672 8000 (x2c_range_all (fun t => (!(pOK tl tl (t % 231) (t / 231)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 231 % 77) * 282) (x2Tab o (t / 231 / 77) (t % 231))) (x2Tab t3 (t / 231) (t % 231)))) 7664 8 chkC_4_d7664) (x2c_join _ 7672 7680 8000 (x2c_range_all (fun t => (!(pOK tl tl (t % 231) (t / 231)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 231 % 77) * 282) (x2Tab o (t / 231 / 77) (t % 231))) (x2Tab t3 (t / 231) (t % 231)))) 7672 8 chkC_4_d7672) (x2c_join _ 7680 7688 8000 (x2c_range_all (fun t => (!(pOK tl tl (t % 231) (t / 231)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 231 % 77) * 282) (x2Tab o (t / 231 / 77) (t % 231))) (x2Tab t3 (t / 231) (t % 231)))) 7680 8 chkC_4_d7680) (x2c_join _ 7688 7696 8000 (x2c_range_all (fun t => (!(pOK tl tl (t % 231) (t / 231)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 231 % 77) * 282) (x2Tab o (t / 231 / 77) (t % 231))) (x2Tab t3 (t / 231) (t % 231)))) 7688 8 chkC_4_d7688) (x2c_join _ 7696 7704 8000 (x2c_range_all (fun t => (!(pOK tl tl (t % 231) (t / 231)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 231 % 77) * 282) (x2Tab o (t / 231 / 77) (t % 231))) (x2Tab t3 (t / 231) (t % 231)))) 7696 8 chkC_4_d7696) (x2c_join _ 7704 7712 8000 (x2c_range_all (fun t => (!(pOK tl tl (t % 231) (t / 231)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 231 % 77) * 282) (x2Tab o (t / 231 / 77) (t % 231))) (x2Tab t3 (t / 231) (t % 231)))) 7704 8 chkC_4_d7704) (x2c_join _ 7712 7720 8000 (x2c_range_all (fun t => (!(pOK tl tl (t % 231) (t / 231)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 231 % 77) * 282) (x2Tab o (t / 231 / 77) (t % 231))) (x2Tab t3 (t / 231) (t % 231)))) 7712 8 chkC_4_d7712) (x2c_join _ 7720 7728 8000 (x2c_range_all (fun t => (!(pOK tl tl (t % 231) (t / 231)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 231 % 77) * 282) (x2Tab o (t / 231 / 77) (t % 231))) (x2Tab t3 (t / 231) (t % 231)))) 7720 8 chkC_4_d7720) (x2c_join _ 7728 7736 8000 (x2c_range_all (fun t => (!(pOK tl tl (t % 231) (t / 231)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 231 % 77) * 282) (x2Tab o (t / 231 / 77) (t % 231))) (x2Tab t3 (t / 231) (t % 231)))) 7728 8 chkC_4_d7728) (x2c_join _ 7736 7744 8000 (x2c_range_all (fun t => (!(pOK tl tl (t % 231) (t / 231)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 231 % 77) * 282) (x2Tab o (t / 231 / 77) (t % 231))) (x2Tab t3 (t / 231) (t % 231)))) 7736 8 chkC_4_d7736) (x2c_join _ 7744 7752 8000 (x2c_range_all (fun t => (!(pOK tl tl (t % 231) (t / 231)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 231 % 77) * 282) (x2Tab o (t / 231 / 77) (t % 231))) (x2Tab t3 (t / 231) (t % 231)))) 7744 8 chkC_4_d7744) (x2c_join _ 7752 7760 8000 (x2c_range_all (fun t => (!(pOK tl tl (t % 231) (t / 231)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 231 % 77) * 282) (x2Tab o (t / 231 / 77) (t % 231))) (x2Tab t3 (t / 231) (t % 231)))) 7752 8 chkC_4_d7752) (x2c_join _ 7760 7768 8000 (x2c_range_all (fun t => (!(pOK tl tl (t % 231) (t / 231)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 231 % 77) * 282) (x2Tab o (t / 231 / 77) (t % 231))) (x2Tab t3 (t / 231) (t % 231)))) 7760 8 chkC_4_d7760) (x2c_join _ 7768 7776 8000 (x2c_range_all (fun t => (!(pOK tl tl (t % 231) (t / 231)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 231 % 77) * 282) (x2Tab o (t / 231 / 77) (t % 231))) (x2Tab t3 (t / 231) (t % 231)))) 7768 8 chkC_4_d7768) (x2c_join _ 7776 7784 8000 (x2c_range_all (fun t => (!(pOK tl tl (t % 231) (t / 231)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 231 % 77) * 282) (x2Tab o (t / 231 / 77) (t % 231))) (x2Tab t3 (t / 231) (t % 231)))) 7776 8 chkC_4_d7776) (x2c_join _ 7784 7792 8000 (x2c_range_all (fun t => (!(pOK tl tl (t % 231) (t / 231)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 231 % 77) * 282) (x2Tab o (t / 231 / 77) (t % 231))) (x2Tab t3 (t / 231) (t % 231)))) 7784 8 chkC_4_d7784) (x2c_join _ 7792 7800 8000 (x2c_range_all (fun t => (!(pOK tl tl (t % 231) (t / 231)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 231 % 77) * 282) (x2Tab o (t / 231 / 77) (t % 231))) (x2Tab t3 (t / 231) (t % 231)))) 7792 8 chkC_4_d7792) (x2c_join _ 7800 7808 8000 (x2c_range_all (fun t => (!(pOK tl tl (t % 231) (t / 231)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 231 % 77) * 282) (x2Tab o (t / 231 / 77) (t % 231))) (x2Tab t3 (t / 231) (t % 231)))) 7800 8 chkC_4_d7800) (x2c_join _ 7808 7816 8000 (x2c_range_all (fun t => (!(pOK tl tl (t % 231) (t / 231)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 231 % 77) * 282) (x2Tab o (t / 231 / 77) (t % 231))) (x2Tab t3 (t / 231) (t % 231)))) 7808 8 chkC_4_d7808) (x2c_join _ 7816 7824 8000 (x2c_range_all (fun t => (!(pOK tl tl (t % 231) (t / 231)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 231 % 77) * 282) (x2Tab o (t / 231 / 77) (t % 231))) (x2Tab t3 (t / 231) (t % 231)))) 7816 8 chkC_4_d7816) (x2c_join _ 7824 7832 8000 (x2c_range_all (fun t => (!(pOK tl tl (t % 231) (t / 231)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 231 % 77) * 282) (x2Tab o (t / 231 / 77) (t % 231))) (x2Tab t3 (t / 231) (t % 231)))) 7824 8 chkC_4_d7824) (x2c_join _ 7832 7840 8000 (x2c_range_all (fun t => (!(pOK tl tl (t % 231) (t / 231)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 231 % 77) * 282) (x2Tab o (t / 231 / 77) (t % 231))) (x2Tab t3 (t / 231) (t % 231)))) 7832 8 chkC_4_d7832) (x2c_join _ 7840 7848 8000 (x2c_range_all (fun t => (!(pOK tl tl (t % 231) (t / 231)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 231 % 77) * 282) (x2Tab o (t / 231 / 77) (t % 231))) (x2Tab t3 (t / 231) (t % 231)))) 7840 8 chkC_4_d7840) (x2c_join _ 7848 7856 8000 (x2c_range_all (fun t => (!(pOK tl tl (t % 231) (t / 231)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 231 % 77) * 282) (x2Tab o (t / 231 / 77) (t % 231))) (x2Tab t3 (t / 231) (t % 231)))) 7848 8 chkC_4_d7848) (x2c_join _ 7856 7864 8000 (x2c_range_all (fun t => (!(pOK tl tl (t % 231) (t / 231)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 231 % 77) * 282) (x2Tab o (t / 231 / 77) (t % 231))) (x2Tab t3 (t / 231) (t % 231)))) 7856 8 chkC_4_d7856) (x2c_join _ 7864 7872 8000 (x2c_range_all (fun t => (!(pOK tl tl (t % 231) (t / 231)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 231 % 77) * 282) (x2Tab o (t / 231 / 77) (t % 231))) (x2Tab t3 (t / 231) (t % 231)))) 7864 8 chkC_4_d7864) (x2c_join _ 7872 7880 8000 (x2c_range_all (fun t => (!(pOK tl tl (t % 231) (t / 231)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 231 % 77) * 282) (x2Tab o (t / 231 / 77) (t % 231))) (x2Tab t3 (t / 231) (t % 231)))) 7872 8 chkC_4_d7872) (x2c_join _ 7880 7888 8000 (x2c_range_all (fun t => (!(pOK tl tl (t % 231) (t / 231)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 231 % 77) * 282) (x2Tab o (t / 231 / 77) (t % 231))) (x2Tab t3 (t / 231) (t % 231)))) 7880 8 chkC_4_d7880) (x2c_join _ 7888 7896 8000 (x2c_range_all (fun t => (!(pOK tl tl (t % 231) (t / 231)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 231 % 77) * 282) (x2Tab o (t / 231 / 77) (t % 231))) (x2Tab t3 (t / 231) (t % 231)))) 7888 8 chkC_4_d7888) (x2c_join _ 7896 7904 8000 (x2c_range_all (fun t => (!(pOK tl tl (t % 231) (t / 231)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 231 % 77) * 282) (x2Tab o (t / 231 / 77) (t % 231))) (x2Tab t3 (t / 231) (t % 231)))) 7896 8 chkC_4_d7896) (x2c_join _ 7904 7912 8000 (x2c_range_all (fun t => (!(pOK tl tl (t % 231) (t / 231)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 231 % 77) * 282) (x2Tab o (t / 231 / 77) (t % 231))) (x2Tab t3 (t / 231) (t % 231)))) 7904 8 chkC_4_d7904) (x2c_join _ 7912 7920 8000 (x2c_range_all (fun t => (!(pOK tl tl (t % 231) (t / 231)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 231 % 77) * 282) (x2Tab o (t / 231 / 77) (t % 231))) (x2Tab t3 (t / 231) (t % 231)))) 7912 8 chkC_4_d7912) (x2c_join _ 7920 7928 8000 (x2c_range_all (fun t => (!(pOK tl tl (t % 231) (t / 231)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 231 % 77) * 282) (x2Tab o (t / 231 / 77) (t % 231))) (x2Tab t3 (t / 231) (t % 231)))) 7920 8 chkC_4_d7920) (x2c_join _ 7928 7936 8000 (x2c_range_all (fun t => (!(pOK tl tl (t % 231) (t / 231)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 231 % 77) * 282) (x2Tab o (t / 231 / 77) (t % 231))) (x2Tab t3 (t / 231) (t % 231)))) 7928 8 chkC_4_d7928) (x2c_join _ 7936 7944 8000 (x2c_range_all (fun t => (!(pOK tl tl (t % 231) (t / 231)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 231 % 77) * 282) (x2Tab o (t / 231 / 77) (t % 231))) (x2Tab t3 (t / 231) (t % 231)))) 7936 8 chkC_4_d7936) (x2c_join _ 7944 7952 8000 (x2c_range_all (fun t => (!(pOK tl tl (t % 231) (t / 231)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 231 % 77) * 282) (x2Tab o (t / 231 / 77) (t % 231))) (x2Tab t3 (t / 231) (t % 231)))) 7944 8 chkC_4_d7944) (x2c_join _ 7952 7960 8000 (x2c_range_all (fun t => (!(pOK tl tl (t % 231) (t / 231)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 231 % 77) * 282) (x2Tab o (t / 231 / 77) (t % 231))) (x2Tab t3 (t / 231) (t % 231)))) 7952 8 chkC_4_d7952) (x2c_join _ 7960 7968 8000 (x2c_range_all (fun t => (!(pOK tl tl (t % 231) (t / 231)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 231 % 77) * 282) (x2Tab o (t / 231 / 77) (t % 231))) (x2Tab t3 (t / 231) (t % 231)))) 7960 8 chkC_4_d7960) (x2c_join _ 7968 7976 8000 (x2c_range_all (fun t => (!(pOK tl tl (t % 231) (t / 231)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 231 % 77) * 282) (x2Tab o (t / 231 / 77) (t % 231))) (x2Tab t3 (t / 231) (t % 231)))) 7968 8 chkC_4_d7968) (x2c_join _ 7976 7984 8000 (x2c_range_all (fun t => (!(pOK tl tl (t % 231) (t / 231)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 231 % 77) * 282) (x2Tab o (t / 231 / 77) (t % 231))) (x2Tab t3 (t / 231) (t % 231)))) 7976 8 chkC_4_d7976) (x2c_join _ 7984 7992 8000 (x2c_range_all (fun t => (!(pOK tl tl (t % 231) (t / 231)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 231 % 77) * 282) (x2Tab o (t / 231 / 77) (t % 231))) (x2Tab t3 (t / 231) (t % 231)))) 7984 8 chkC_4_d7984) (x2c_range_all (fun t => (!(pOK tl tl (t % 231) (t / 231)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 231 % 77) * 282) (x2Tab o (t / 231 / 77) (t % 231))) (x2Tab t3 (t / 231) (t % 231)))) 7992 8 chkC_4_d7992))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))


end ThreeCopyQutritWerner.X2.CoreA1g
