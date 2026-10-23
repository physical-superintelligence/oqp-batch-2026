module

public import ThreeCopyQutritWerner.CertificateX2CoreS1gT3
public import ThreeCopyQutritWerner.CertificateX2Trans
public import ThreeCopyQutritWerner.CertificateX2CoreBatchGen
public import ThreeCopyQutritWerner.CertificateX2CoreBatchFlat

@[expose] public section


/-! Batched core S1g: axis-0 stage, selected pairs, flat indices 9600..11199. -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option exponentiation.threshold 1000000

namespace ThreeCopyQutritWerner.X2.CoreS1g
open ThreeCopyQutritWerner ThreeCopyQutritWerner.X2

theorem chkC_6_d9600 : (List.range' 9600 8).all (fun t => (!(pOK tl tl (t % 282) (t / 282)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 282 % 94) * 282) (x2Tab o (t / 282 / 94) (t % 282))) (x2Tab t3 (t / 282) (t % 282)))) = true := by
  decide +kernel

theorem chkC_6_d9608 : (List.range' 9608 8).all (fun t => (!(pOK tl tl (t % 282) (t / 282)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 282 % 94) * 282) (x2Tab o (t / 282 / 94) (t % 282))) (x2Tab t3 (t / 282) (t % 282)))) = true := by
  decide +kernel

theorem chkC_6_d9616 : (List.range' 9616 8).all (fun t => (!(pOK tl tl (t % 282) (t / 282)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 282 % 94) * 282) (x2Tab o (t / 282 / 94) (t % 282))) (x2Tab t3 (t / 282) (t % 282)))) = true := by
  decide +kernel

theorem chkC_6_d9624 : (List.range' 9624 8).all (fun t => (!(pOK tl tl (t % 282) (t / 282)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 282 % 94) * 282) (x2Tab o (t / 282 / 94) (t % 282))) (x2Tab t3 (t / 282) (t % 282)))) = true := by
  decide +kernel

theorem chkC_6_d9632 : (List.range' 9632 8).all (fun t => (!(pOK tl tl (t % 282) (t / 282)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 282 % 94) * 282) (x2Tab o (t / 282 / 94) (t % 282))) (x2Tab t3 (t / 282) (t % 282)))) = true := by
  decide +kernel

theorem chkC_6_d9640 : (List.range' 9640 8).all (fun t => (!(pOK tl tl (t % 282) (t / 282)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 282 % 94) * 282) (x2Tab o (t / 282 / 94) (t % 282))) (x2Tab t3 (t / 282) (t % 282)))) = true := by
  decide +kernel

theorem chkC_6_d9648 : (List.range' 9648 8).all (fun t => (!(pOK tl tl (t % 282) (t / 282)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 282 % 94) * 282) (x2Tab o (t / 282 / 94) (t % 282))) (x2Tab t3 (t / 282) (t % 282)))) = true := by
  decide +kernel

theorem chkC_6_d9656 : (List.range' 9656 8).all (fun t => (!(pOK tl tl (t % 282) (t / 282)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 282 % 94) * 282) (x2Tab o (t / 282 / 94) (t % 282))) (x2Tab t3 (t / 282) (t % 282)))) = true := by
  decide +kernel

theorem chkC_6_d9664 : (List.range' 9664 8).all (fun t => (!(pOK tl tl (t % 282) (t / 282)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 282 % 94) * 282) (x2Tab o (t / 282 / 94) (t % 282))) (x2Tab t3 (t / 282) (t % 282)))) = true := by
  decide +kernel

theorem chkC_6_d9672 : (List.range' 9672 8).all (fun t => (!(pOK tl tl (t % 282) (t / 282)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 282 % 94) * 282) (x2Tab o (t / 282 / 94) (t % 282))) (x2Tab t3 (t / 282) (t % 282)))) = true := by
  decide +kernel

theorem chkC_6_d9680 : (List.range' 9680 8).all (fun t => (!(pOK tl tl (t % 282) (t / 282)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 282 % 94) * 282) (x2Tab o (t / 282 / 94) (t % 282))) (x2Tab t3 (t / 282) (t % 282)))) = true := by
  decide +kernel

theorem chkC_6_d9688 : (List.range' 9688 8).all (fun t => (!(pOK tl tl (t % 282) (t / 282)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 282 % 94) * 282) (x2Tab o (t / 282 / 94) (t % 282))) (x2Tab t3 (t / 282) (t % 282)))) = true := by
  decide +kernel

theorem chkC_6_d9696 : (List.range' 9696 8).all (fun t => (!(pOK tl tl (t % 282) (t / 282)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 282 % 94) * 282) (x2Tab o (t / 282 / 94) (t % 282))) (x2Tab t3 (t / 282) (t % 282)))) = true := by
  decide +kernel

theorem chkC_6_d9704 : (List.range' 9704 8).all (fun t => (!(pOK tl tl (t % 282) (t / 282)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 282 % 94) * 282) (x2Tab o (t / 282 / 94) (t % 282))) (x2Tab t3 (t / 282) (t % 282)))) = true := by
  decide +kernel

theorem chkC_6_d9712 : (List.range' 9712 8).all (fun t => (!(pOK tl tl (t % 282) (t / 282)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 282 % 94) * 282) (x2Tab o (t / 282 / 94) (t % 282))) (x2Tab t3 (t / 282) (t % 282)))) = true := by
  decide +kernel

theorem chkC_6_d9720 : (List.range' 9720 8).all (fun t => (!(pOK tl tl (t % 282) (t / 282)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 282 % 94) * 282) (x2Tab o (t / 282 / 94) (t % 282))) (x2Tab t3 (t / 282) (t % 282)))) = true := by
  decide +kernel

theorem chkC_6_d9728 : (List.range' 9728 8).all (fun t => (!(pOK tl tl (t % 282) (t / 282)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 282 % 94) * 282) (x2Tab o (t / 282 / 94) (t % 282))) (x2Tab t3 (t / 282) (t % 282)))) = true := by
  decide +kernel

theorem chkC_6_d9736 : (List.range' 9736 8).all (fun t => (!(pOK tl tl (t % 282) (t / 282)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 282 % 94) * 282) (x2Tab o (t / 282 / 94) (t % 282))) (x2Tab t3 (t / 282) (t % 282)))) = true := by
  decide +kernel

theorem chkC_6_d9744 : (List.range' 9744 8).all (fun t => (!(pOK tl tl (t % 282) (t / 282)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 282 % 94) * 282) (x2Tab o (t / 282 / 94) (t % 282))) (x2Tab t3 (t / 282) (t % 282)))) = true := by
  decide +kernel

theorem chkC_6_d9752 : (List.range' 9752 8).all (fun t => (!(pOK tl tl (t % 282) (t / 282)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 282 % 94) * 282) (x2Tab o (t / 282 / 94) (t % 282))) (x2Tab t3 (t / 282) (t % 282)))) = true := by
  decide +kernel

theorem chkC_6_d9760 : (List.range' 9760 8).all (fun t => (!(pOK tl tl (t % 282) (t / 282)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 282 % 94) * 282) (x2Tab o (t / 282 / 94) (t % 282))) (x2Tab t3 (t / 282) (t % 282)))) = true := by
  decide +kernel

theorem chkC_6_d9768 : (List.range' 9768 8).all (fun t => (!(pOK tl tl (t % 282) (t / 282)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 282 % 94) * 282) (x2Tab o (t / 282 / 94) (t % 282))) (x2Tab t3 (t / 282) (t % 282)))) = true := by
  decide +kernel

theorem chkC_6_d9776 : (List.range' 9776 8).all (fun t => (!(pOK tl tl (t % 282) (t / 282)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 282 % 94) * 282) (x2Tab o (t / 282 / 94) (t % 282))) (x2Tab t3 (t / 282) (t % 282)))) = true := by
  decide +kernel

theorem chkC_6_d9784 : (List.range' 9784 8).all (fun t => (!(pOK tl tl (t % 282) (t / 282)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 282 % 94) * 282) (x2Tab o (t / 282 / 94) (t % 282))) (x2Tab t3 (t / 282) (t % 282)))) = true := by
  decide +kernel

theorem chkC_6_d9792 : (List.range' 9792 8).all (fun t => (!(pOK tl tl (t % 282) (t / 282)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 282 % 94) * 282) (x2Tab o (t / 282 / 94) (t % 282))) (x2Tab t3 (t / 282) (t % 282)))) = true := by
  decide +kernel

theorem chkC_6_d9800 : (List.range' 9800 8).all (fun t => (!(pOK tl tl (t % 282) (t / 282)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 282 % 94) * 282) (x2Tab o (t / 282 / 94) (t % 282))) (x2Tab t3 (t / 282) (t % 282)))) = true := by
  decide +kernel

theorem chkC_6_d9808 : (List.range' 9808 8).all (fun t => (!(pOK tl tl (t % 282) (t / 282)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 282 % 94) * 282) (x2Tab o (t / 282 / 94) (t % 282))) (x2Tab t3 (t / 282) (t % 282)))) = true := by
  decide +kernel

theorem chkC_6_d9816 : (List.range' 9816 8).all (fun t => (!(pOK tl tl (t % 282) (t / 282)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 282 % 94) * 282) (x2Tab o (t / 282 / 94) (t % 282))) (x2Tab t3 (t / 282) (t % 282)))) = true := by
  decide +kernel

theorem chkC_6_d9824 : (List.range' 9824 8).all (fun t => (!(pOK tl tl (t % 282) (t / 282)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 282 % 94) * 282) (x2Tab o (t / 282 / 94) (t % 282))) (x2Tab t3 (t / 282) (t % 282)))) = true := by
  decide +kernel

theorem chkC_6_d9832 : (List.range' 9832 8).all (fun t => (!(pOK tl tl (t % 282) (t / 282)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 282 % 94) * 282) (x2Tab o (t / 282 / 94) (t % 282))) (x2Tab t3 (t / 282) (t % 282)))) = true := by
  decide +kernel

theorem chkC_6_d9840 : (List.range' 9840 8).all (fun t => (!(pOK tl tl (t % 282) (t / 282)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 282 % 94) * 282) (x2Tab o (t / 282 / 94) (t % 282))) (x2Tab t3 (t / 282) (t % 282)))) = true := by
  decide +kernel

theorem chkC_6_d9848 : (List.range' 9848 8).all (fun t => (!(pOK tl tl (t % 282) (t / 282)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 282 % 94) * 282) (x2Tab o (t / 282 / 94) (t % 282))) (x2Tab t3 (t / 282) (t % 282)))) = true := by
  decide +kernel

theorem chkC_6_d9856 : (List.range' 9856 8).all (fun t => (!(pOK tl tl (t % 282) (t / 282)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 282 % 94) * 282) (x2Tab o (t / 282 / 94) (t % 282))) (x2Tab t3 (t / 282) (t % 282)))) = true := by
  decide +kernel

theorem chkC_6_d9864 : (List.range' 9864 8).all (fun t => (!(pOK tl tl (t % 282) (t / 282)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 282 % 94) * 282) (x2Tab o (t / 282 / 94) (t % 282))) (x2Tab t3 (t / 282) (t % 282)))) = true := by
  decide +kernel

theorem chkC_6_d9872 : (List.range' 9872 8).all (fun t => (!(pOK tl tl (t % 282) (t / 282)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 282 % 94) * 282) (x2Tab o (t / 282 / 94) (t % 282))) (x2Tab t3 (t / 282) (t % 282)))) = true := by
  decide +kernel

theorem chkC_6_d9880 : (List.range' 9880 8).all (fun t => (!(pOK tl tl (t % 282) (t / 282)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 282 % 94) * 282) (x2Tab o (t / 282 / 94) (t % 282))) (x2Tab t3 (t / 282) (t % 282)))) = true := by
  decide +kernel

theorem chkC_6_d9888 : (List.range' 9888 8).all (fun t => (!(pOK tl tl (t % 282) (t / 282)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 282 % 94) * 282) (x2Tab o (t / 282 / 94) (t % 282))) (x2Tab t3 (t / 282) (t % 282)))) = true := by
  decide +kernel

theorem chkC_6_d9896 : (List.range' 9896 8).all (fun t => (!(pOK tl tl (t % 282) (t / 282)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 282 % 94) * 282) (x2Tab o (t / 282 / 94) (t % 282))) (x2Tab t3 (t / 282) (t % 282)))) = true := by
  decide +kernel

theorem chkC_6_d9904 : (List.range' 9904 8).all (fun t => (!(pOK tl tl (t % 282) (t / 282)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 282 % 94) * 282) (x2Tab o (t / 282 / 94) (t % 282))) (x2Tab t3 (t / 282) (t % 282)))) = true := by
  decide +kernel

theorem chkC_6_d9912 : (List.range' 9912 8).all (fun t => (!(pOK tl tl (t % 282) (t / 282)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 282 % 94) * 282) (x2Tab o (t / 282 / 94) (t % 282))) (x2Tab t3 (t / 282) (t % 282)))) = true := by
  decide +kernel

theorem chkC_6_d9920 : (List.range' 9920 8).all (fun t => (!(pOK tl tl (t % 282) (t / 282)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 282 % 94) * 282) (x2Tab o (t / 282 / 94) (t % 282))) (x2Tab t3 (t / 282) (t % 282)))) = true := by
  decide +kernel

theorem chkC_6_d9928 : (List.range' 9928 8).all (fun t => (!(pOK tl tl (t % 282) (t / 282)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 282 % 94) * 282) (x2Tab o (t / 282 / 94) (t % 282))) (x2Tab t3 (t / 282) (t % 282)))) = true := by
  decide +kernel

theorem chkC_6_d9936 : (List.range' 9936 8).all (fun t => (!(pOK tl tl (t % 282) (t / 282)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 282 % 94) * 282) (x2Tab o (t / 282 / 94) (t % 282))) (x2Tab t3 (t / 282) (t % 282)))) = true := by
  decide +kernel

theorem chkC_6_d9944 : (List.range' 9944 8).all (fun t => (!(pOK tl tl (t % 282) (t / 282)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 282 % 94) * 282) (x2Tab o (t / 282 / 94) (t % 282))) (x2Tab t3 (t / 282) (t % 282)))) = true := by
  decide +kernel

theorem chkC_6_d9952 : (List.range' 9952 8).all (fun t => (!(pOK tl tl (t % 282) (t / 282)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 282 % 94) * 282) (x2Tab o (t / 282 / 94) (t % 282))) (x2Tab t3 (t / 282) (t % 282)))) = true := by
  decide +kernel

theorem chkC_6_d9960 : (List.range' 9960 8).all (fun t => (!(pOK tl tl (t % 282) (t / 282)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 282 % 94) * 282) (x2Tab o (t / 282 / 94) (t % 282))) (x2Tab t3 (t / 282) (t % 282)))) = true := by
  decide +kernel

theorem chkC_6_d9968 : (List.range' 9968 8).all (fun t => (!(pOK tl tl (t % 282) (t / 282)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 282 % 94) * 282) (x2Tab o (t / 282 / 94) (t % 282))) (x2Tab t3 (t / 282) (t % 282)))) = true := by
  decide +kernel

theorem chkC_6_d9976 : (List.range' 9976 8).all (fun t => (!(pOK tl tl (t % 282) (t / 282)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 282 % 94) * 282) (x2Tab o (t / 282 / 94) (t % 282))) (x2Tab t3 (t / 282) (t % 282)))) = true := by
  decide +kernel

theorem chkC_6_d9984 : (List.range' 9984 8).all (fun t => (!(pOK tl tl (t % 282) (t / 282)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 282 % 94) * 282) (x2Tab o (t / 282 / 94) (t % 282))) (x2Tab t3 (t / 282) (t % 282)))) = true := by
  decide +kernel

theorem chkC_6_d9992 : (List.range' 9992 8).all (fun t => (!(pOK tl tl (t % 282) (t / 282)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 282 % 94) * 282) (x2Tab o (t / 282 / 94) (t % 282))) (x2Tab t3 (t / 282) (t % 282)))) = true := by
  decide +kernel

theorem chkC_6_d10000 : (List.range' 10000 8).all (fun t => (!(pOK tl tl (t % 282) (t / 282)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 282 % 94) * 282) (x2Tab o (t / 282 / 94) (t % 282))) (x2Tab t3 (t / 282) (t % 282)))) = true := by
  decide +kernel

theorem chkC_6_d10008 : (List.range' 10008 8).all (fun t => (!(pOK tl tl (t % 282) (t / 282)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 282 % 94) * 282) (x2Tab o (t / 282 / 94) (t % 282))) (x2Tab t3 (t / 282) (t % 282)))) = true := by
  decide +kernel

theorem chkC_6_d10016 : (List.range' 10016 8).all (fun t => (!(pOK tl tl (t % 282) (t / 282)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 282 % 94) * 282) (x2Tab o (t / 282 / 94) (t % 282))) (x2Tab t3 (t / 282) (t % 282)))) = true := by
  decide +kernel

theorem chkC_6_d10024 : (List.range' 10024 8).all (fun t => (!(pOK tl tl (t % 282) (t / 282)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 282 % 94) * 282) (x2Tab o (t / 282 / 94) (t % 282))) (x2Tab t3 (t / 282) (t % 282)))) = true := by
  decide +kernel

theorem chkC_6_d10032 : (List.range' 10032 8).all (fun t => (!(pOK tl tl (t % 282) (t / 282)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 282 % 94) * 282) (x2Tab o (t / 282 / 94) (t % 282))) (x2Tab t3 (t / 282) (t % 282)))) = true := by
  decide +kernel

theorem chkC_6_d10040 : (List.range' 10040 8).all (fun t => (!(pOK tl tl (t % 282) (t / 282)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 282 % 94) * 282) (x2Tab o (t / 282 / 94) (t % 282))) (x2Tab t3 (t / 282) (t % 282)))) = true := by
  decide +kernel

theorem chkC_6_d10048 : (List.range' 10048 8).all (fun t => (!(pOK tl tl (t % 282) (t / 282)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 282 % 94) * 282) (x2Tab o (t / 282 / 94) (t % 282))) (x2Tab t3 (t / 282) (t % 282)))) = true := by
  decide +kernel

theorem chkC_6_d10056 : (List.range' 10056 8).all (fun t => (!(pOK tl tl (t % 282) (t / 282)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 282 % 94) * 282) (x2Tab o (t / 282 / 94) (t % 282))) (x2Tab t3 (t / 282) (t % 282)))) = true := by
  decide +kernel

theorem chkC_6_d10064 : (List.range' 10064 8).all (fun t => (!(pOK tl tl (t % 282) (t / 282)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 282 % 94) * 282) (x2Tab o (t / 282 / 94) (t % 282))) (x2Tab t3 (t / 282) (t % 282)))) = true := by
  decide +kernel

theorem chkC_6_d10072 : (List.range' 10072 8).all (fun t => (!(pOK tl tl (t % 282) (t / 282)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 282 % 94) * 282) (x2Tab o (t / 282 / 94) (t % 282))) (x2Tab t3 (t / 282) (t % 282)))) = true := by
  decide +kernel

theorem chkC_6_d10080 : (List.range' 10080 8).all (fun t => (!(pOK tl tl (t % 282) (t / 282)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 282 % 94) * 282) (x2Tab o (t / 282 / 94) (t % 282))) (x2Tab t3 (t / 282) (t % 282)))) = true := by
  decide +kernel

theorem chkC_6_d10088 : (List.range' 10088 8).all (fun t => (!(pOK tl tl (t % 282) (t / 282)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 282 % 94) * 282) (x2Tab o (t / 282 / 94) (t % 282))) (x2Tab t3 (t / 282) (t % 282)))) = true := by
  decide +kernel

theorem chkC_6_d10096 : (List.range' 10096 8).all (fun t => (!(pOK tl tl (t % 282) (t / 282)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 282 % 94) * 282) (x2Tab o (t / 282 / 94) (t % 282))) (x2Tab t3 (t / 282) (t % 282)))) = true := by
  decide +kernel

theorem chkC_6_d10104 : (List.range' 10104 8).all (fun t => (!(pOK tl tl (t % 282) (t / 282)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 282 % 94) * 282) (x2Tab o (t / 282 / 94) (t % 282))) (x2Tab t3 (t / 282) (t % 282)))) = true := by
  decide +kernel

theorem chkC_6_d10112 : (List.range' 10112 8).all (fun t => (!(pOK tl tl (t % 282) (t / 282)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 282 % 94) * 282) (x2Tab o (t / 282 / 94) (t % 282))) (x2Tab t3 (t / 282) (t % 282)))) = true := by
  decide +kernel

theorem chkC_6_d10120 : (List.range' 10120 8).all (fun t => (!(pOK tl tl (t % 282) (t / 282)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 282 % 94) * 282) (x2Tab o (t / 282 / 94) (t % 282))) (x2Tab t3 (t / 282) (t % 282)))) = true := by
  decide +kernel

theorem chkC_6_d10128 : (List.range' 10128 8).all (fun t => (!(pOK tl tl (t % 282) (t / 282)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 282 % 94) * 282) (x2Tab o (t / 282 / 94) (t % 282))) (x2Tab t3 (t / 282) (t % 282)))) = true := by
  decide +kernel

theorem chkC_6_d10136 : (List.range' 10136 8).all (fun t => (!(pOK tl tl (t % 282) (t / 282)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 282 % 94) * 282) (x2Tab o (t / 282 / 94) (t % 282))) (x2Tab t3 (t / 282) (t % 282)))) = true := by
  decide +kernel

theorem chkC_6_d10144 : (List.range' 10144 8).all (fun t => (!(pOK tl tl (t % 282) (t / 282)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 282 % 94) * 282) (x2Tab o (t / 282 / 94) (t % 282))) (x2Tab t3 (t / 282) (t % 282)))) = true := by
  decide +kernel

theorem chkC_6_d10152 : (List.range' 10152 8).all (fun t => (!(pOK tl tl (t % 282) (t / 282)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 282 % 94) * 282) (x2Tab o (t / 282 / 94) (t % 282))) (x2Tab t3 (t / 282) (t % 282)))) = true := by
  decide +kernel

theorem chkC_6_d10160 : (List.range' 10160 8).all (fun t => (!(pOK tl tl (t % 282) (t / 282)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 282 % 94) * 282) (x2Tab o (t / 282 / 94) (t % 282))) (x2Tab t3 (t / 282) (t % 282)))) = true := by
  decide +kernel

theorem chkC_6_d10168 : (List.range' 10168 8).all (fun t => (!(pOK tl tl (t % 282) (t / 282)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 282 % 94) * 282) (x2Tab o (t / 282 / 94) (t % 282))) (x2Tab t3 (t / 282) (t % 282)))) = true := by
  decide +kernel

theorem chkC_6_d10176 : (List.range' 10176 8).all (fun t => (!(pOK tl tl (t % 282) (t / 282)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 282 % 94) * 282) (x2Tab o (t / 282 / 94) (t % 282))) (x2Tab t3 (t / 282) (t % 282)))) = true := by
  decide +kernel

theorem chkC_6_d10184 : (List.range' 10184 8).all (fun t => (!(pOK tl tl (t % 282) (t / 282)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 282 % 94) * 282) (x2Tab o (t / 282 / 94) (t % 282))) (x2Tab t3 (t / 282) (t % 282)))) = true := by
  decide +kernel

theorem chkC_6_d10192 : (List.range' 10192 8).all (fun t => (!(pOK tl tl (t % 282) (t / 282)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 282 % 94) * 282) (x2Tab o (t / 282 / 94) (t % 282))) (x2Tab t3 (t / 282) (t % 282)))) = true := by
  decide +kernel

theorem chkC_6_d10200 : (List.range' 10200 8).all (fun t => (!(pOK tl tl (t % 282) (t / 282)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 282 % 94) * 282) (x2Tab o (t / 282 / 94) (t % 282))) (x2Tab t3 (t / 282) (t % 282)))) = true := by
  decide +kernel

theorem chkC_6_d10208 : (List.range' 10208 8).all (fun t => (!(pOK tl tl (t % 282) (t / 282)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 282 % 94) * 282) (x2Tab o (t / 282 / 94) (t % 282))) (x2Tab t3 (t / 282) (t % 282)))) = true := by
  decide +kernel

theorem chkC_6_d10216 : (List.range' 10216 8).all (fun t => (!(pOK tl tl (t % 282) (t / 282)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 282 % 94) * 282) (x2Tab o (t / 282 / 94) (t % 282))) (x2Tab t3 (t / 282) (t % 282)))) = true := by
  decide +kernel

theorem chkC_6_d10224 : (List.range' 10224 8).all (fun t => (!(pOK tl tl (t % 282) (t / 282)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 282 % 94) * 282) (x2Tab o (t / 282 / 94) (t % 282))) (x2Tab t3 (t / 282) (t % 282)))) = true := by
  decide +kernel

theorem chkC_6_d10232 : (List.range' 10232 8).all (fun t => (!(pOK tl tl (t % 282) (t / 282)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 282 % 94) * 282) (x2Tab o (t / 282 / 94) (t % 282))) (x2Tab t3 (t / 282) (t % 282)))) = true := by
  decide +kernel

theorem chkC_6_d10240 : (List.range' 10240 8).all (fun t => (!(pOK tl tl (t % 282) (t / 282)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 282 % 94) * 282) (x2Tab o (t / 282 / 94) (t % 282))) (x2Tab t3 (t / 282) (t % 282)))) = true := by
  decide +kernel

theorem chkC_6_d10248 : (List.range' 10248 8).all (fun t => (!(pOK tl tl (t % 282) (t / 282)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 282 % 94) * 282) (x2Tab o (t / 282 / 94) (t % 282))) (x2Tab t3 (t / 282) (t % 282)))) = true := by
  decide +kernel

theorem chkC_6_d10256 : (List.range' 10256 8).all (fun t => (!(pOK tl tl (t % 282) (t / 282)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 282 % 94) * 282) (x2Tab o (t / 282 / 94) (t % 282))) (x2Tab t3 (t / 282) (t % 282)))) = true := by
  decide +kernel

theorem chkC_6_d10264 : (List.range' 10264 8).all (fun t => (!(pOK tl tl (t % 282) (t / 282)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 282 % 94) * 282) (x2Tab o (t / 282 / 94) (t % 282))) (x2Tab t3 (t / 282) (t % 282)))) = true := by
  decide +kernel

theorem chkC_6_d10272 : (List.range' 10272 8).all (fun t => (!(pOK tl tl (t % 282) (t / 282)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 282 % 94) * 282) (x2Tab o (t / 282 / 94) (t % 282))) (x2Tab t3 (t / 282) (t % 282)))) = true := by
  decide +kernel

theorem chkC_6_d10280 : (List.range' 10280 8).all (fun t => (!(pOK tl tl (t % 282) (t / 282)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 282 % 94) * 282) (x2Tab o (t / 282 / 94) (t % 282))) (x2Tab t3 (t / 282) (t % 282)))) = true := by
  decide +kernel

theorem chkC_6_d10288 : (List.range' 10288 8).all (fun t => (!(pOK tl tl (t % 282) (t / 282)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 282 % 94) * 282) (x2Tab o (t / 282 / 94) (t % 282))) (x2Tab t3 (t / 282) (t % 282)))) = true := by
  decide +kernel

theorem chkC_6_d10296 : (List.range' 10296 8).all (fun t => (!(pOK tl tl (t % 282) (t / 282)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 282 % 94) * 282) (x2Tab o (t / 282 / 94) (t % 282))) (x2Tab t3 (t / 282) (t % 282)))) = true := by
  decide +kernel

theorem chkC_6_d10304 : (List.range' 10304 8).all (fun t => (!(pOK tl tl (t % 282) (t / 282)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 282 % 94) * 282) (x2Tab o (t / 282 / 94) (t % 282))) (x2Tab t3 (t / 282) (t % 282)))) = true := by
  decide +kernel

theorem chkC_6_d10312 : (List.range' 10312 8).all (fun t => (!(pOK tl tl (t % 282) (t / 282)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 282 % 94) * 282) (x2Tab o (t / 282 / 94) (t % 282))) (x2Tab t3 (t / 282) (t % 282)))) = true := by
  decide +kernel

theorem chkC_6_d10320 : (List.range' 10320 8).all (fun t => (!(pOK tl tl (t % 282) (t / 282)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 282 % 94) * 282) (x2Tab o (t / 282 / 94) (t % 282))) (x2Tab t3 (t / 282) (t % 282)))) = true := by
  decide +kernel

theorem chkC_6_d10328 : (List.range' 10328 8).all (fun t => (!(pOK tl tl (t % 282) (t / 282)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 282 % 94) * 282) (x2Tab o (t / 282 / 94) (t % 282))) (x2Tab t3 (t / 282) (t % 282)))) = true := by
  decide +kernel

theorem chkC_6_d10336 : (List.range' 10336 8).all (fun t => (!(pOK tl tl (t % 282) (t / 282)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 282 % 94) * 282) (x2Tab o (t / 282 / 94) (t % 282))) (x2Tab t3 (t / 282) (t % 282)))) = true := by
  decide +kernel

theorem chkC_6_d10344 : (List.range' 10344 8).all (fun t => (!(pOK tl tl (t % 282) (t / 282)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 282 % 94) * 282) (x2Tab o (t / 282 / 94) (t % 282))) (x2Tab t3 (t / 282) (t % 282)))) = true := by
  decide +kernel

theorem chkC_6_d10352 : (List.range' 10352 8).all (fun t => (!(pOK tl tl (t % 282) (t / 282)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 282 % 94) * 282) (x2Tab o (t / 282 / 94) (t % 282))) (x2Tab t3 (t / 282) (t % 282)))) = true := by
  decide +kernel

theorem chkC_6_d10360 : (List.range' 10360 8).all (fun t => (!(pOK tl tl (t % 282) (t / 282)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 282 % 94) * 282) (x2Tab o (t / 282 / 94) (t % 282))) (x2Tab t3 (t / 282) (t % 282)))) = true := by
  decide +kernel

theorem chkC_6_d10368 : (List.range' 10368 8).all (fun t => (!(pOK tl tl (t % 282) (t / 282)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 282 % 94) * 282) (x2Tab o (t / 282 / 94) (t % 282))) (x2Tab t3 (t / 282) (t % 282)))) = true := by
  decide +kernel

theorem chkC_6_d10376 : (List.range' 10376 8).all (fun t => (!(pOK tl tl (t % 282) (t / 282)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 282 % 94) * 282) (x2Tab o (t / 282 / 94) (t % 282))) (x2Tab t3 (t / 282) (t % 282)))) = true := by
  decide +kernel

theorem chkC_6_d10384 : (List.range' 10384 8).all (fun t => (!(pOK tl tl (t % 282) (t / 282)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 282 % 94) * 282) (x2Tab o (t / 282 / 94) (t % 282))) (x2Tab t3 (t / 282) (t % 282)))) = true := by
  decide +kernel

theorem chkC_6_d10392 : (List.range' 10392 8).all (fun t => (!(pOK tl tl (t % 282) (t / 282)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 282 % 94) * 282) (x2Tab o (t / 282 / 94) (t % 282))) (x2Tab t3 (t / 282) (t % 282)))) = true := by
  decide +kernel

theorem chkC_6_d10400 : (List.range' 10400 8).all (fun t => (!(pOK tl tl (t % 282) (t / 282)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 282 % 94) * 282) (x2Tab o (t / 282 / 94) (t % 282))) (x2Tab t3 (t / 282) (t % 282)))) = true := by
  decide +kernel

theorem chkC_6_d10408 : (List.range' 10408 8).all (fun t => (!(pOK tl tl (t % 282) (t / 282)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 282 % 94) * 282) (x2Tab o (t / 282 / 94) (t % 282))) (x2Tab t3 (t / 282) (t % 282)))) = true := by
  decide +kernel

theorem chkC_6_d10416 : (List.range' 10416 8).all (fun t => (!(pOK tl tl (t % 282) (t / 282)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 282 % 94) * 282) (x2Tab o (t / 282 / 94) (t % 282))) (x2Tab t3 (t / 282) (t % 282)))) = true := by
  decide +kernel

theorem chkC_6_d10424 : (List.range' 10424 8).all (fun t => (!(pOK tl tl (t % 282) (t / 282)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 282 % 94) * 282) (x2Tab o (t / 282 / 94) (t % 282))) (x2Tab t3 (t / 282) (t % 282)))) = true := by
  decide +kernel

theorem chkC_6_d10432 : (List.range' 10432 8).all (fun t => (!(pOK tl tl (t % 282) (t / 282)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 282 % 94) * 282) (x2Tab o (t / 282 / 94) (t % 282))) (x2Tab t3 (t / 282) (t % 282)))) = true := by
  decide +kernel

theorem chkC_6_d10440 : (List.range' 10440 8).all (fun t => (!(pOK tl tl (t % 282) (t / 282)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 282 % 94) * 282) (x2Tab o (t / 282 / 94) (t % 282))) (x2Tab t3 (t / 282) (t % 282)))) = true := by
  decide +kernel

theorem chkC_6_d10448 : (List.range' 10448 8).all (fun t => (!(pOK tl tl (t % 282) (t / 282)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 282 % 94) * 282) (x2Tab o (t / 282 / 94) (t % 282))) (x2Tab t3 (t / 282) (t % 282)))) = true := by
  decide +kernel

theorem chkC_6_d10456 : (List.range' 10456 8).all (fun t => (!(pOK tl tl (t % 282) (t / 282)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 282 % 94) * 282) (x2Tab o (t / 282 / 94) (t % 282))) (x2Tab t3 (t / 282) (t % 282)))) = true := by
  decide +kernel

theorem chkC_6_d10464 : (List.range' 10464 8).all (fun t => (!(pOK tl tl (t % 282) (t / 282)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 282 % 94) * 282) (x2Tab o (t / 282 / 94) (t % 282))) (x2Tab t3 (t / 282) (t % 282)))) = true := by
  decide +kernel

theorem chkC_6_d10472 : (List.range' 10472 8).all (fun t => (!(pOK tl tl (t % 282) (t / 282)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 282 % 94) * 282) (x2Tab o (t / 282 / 94) (t % 282))) (x2Tab t3 (t / 282) (t % 282)))) = true := by
  decide +kernel

theorem chkC_6_d10480 : (List.range' 10480 8).all (fun t => (!(pOK tl tl (t % 282) (t / 282)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 282 % 94) * 282) (x2Tab o (t / 282 / 94) (t % 282))) (x2Tab t3 (t / 282) (t % 282)))) = true := by
  decide +kernel

theorem chkC_6_d10488 : (List.range' 10488 8).all (fun t => (!(pOK tl tl (t % 282) (t / 282)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 282 % 94) * 282) (x2Tab o (t / 282 / 94) (t % 282))) (x2Tab t3 (t / 282) (t % 282)))) = true := by
  decide +kernel

theorem chkC_6_d10496 : (List.range' 10496 8).all (fun t => (!(pOK tl tl (t % 282) (t / 282)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 282 % 94) * 282) (x2Tab o (t / 282 / 94) (t % 282))) (x2Tab t3 (t / 282) (t % 282)))) = true := by
  decide +kernel

theorem chkC_6_d10504 : (List.range' 10504 8).all (fun t => (!(pOK tl tl (t % 282) (t / 282)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 282 % 94) * 282) (x2Tab o (t / 282 / 94) (t % 282))) (x2Tab t3 (t / 282) (t % 282)))) = true := by
  decide +kernel

theorem chkC_6_d10512 : (List.range' 10512 8).all (fun t => (!(pOK tl tl (t % 282) (t / 282)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 282 % 94) * 282) (x2Tab o (t / 282 / 94) (t % 282))) (x2Tab t3 (t / 282) (t % 282)))) = true := by
  decide +kernel

theorem chkC_6_d10520 : (List.range' 10520 8).all (fun t => (!(pOK tl tl (t % 282) (t / 282)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 282 % 94) * 282) (x2Tab o (t / 282 / 94) (t % 282))) (x2Tab t3 (t / 282) (t % 282)))) = true := by
  decide +kernel

theorem chkC_6_d10528 : (List.range' 10528 8).all (fun t => (!(pOK tl tl (t % 282) (t / 282)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 282 % 94) * 282) (x2Tab o (t / 282 / 94) (t % 282))) (x2Tab t3 (t / 282) (t % 282)))) = true := by
  decide +kernel

theorem chkC_6_d10536 : (List.range' 10536 8).all (fun t => (!(pOK tl tl (t % 282) (t / 282)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 282 % 94) * 282) (x2Tab o (t / 282 / 94) (t % 282))) (x2Tab t3 (t / 282) (t % 282)))) = true := by
  decide +kernel

theorem chkC_6_d10544 : (List.range' 10544 8).all (fun t => (!(pOK tl tl (t % 282) (t / 282)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 282 % 94) * 282) (x2Tab o (t / 282 / 94) (t % 282))) (x2Tab t3 (t / 282) (t % 282)))) = true := by
  decide +kernel

theorem chkC_6_d10552 : (List.range' 10552 8).all (fun t => (!(pOK tl tl (t % 282) (t / 282)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 282 % 94) * 282) (x2Tab o (t / 282 / 94) (t % 282))) (x2Tab t3 (t / 282) (t % 282)))) = true := by
  decide +kernel

theorem chkC_6_d10560 : (List.range' 10560 8).all (fun t => (!(pOK tl tl (t % 282) (t / 282)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 282 % 94) * 282) (x2Tab o (t / 282 / 94) (t % 282))) (x2Tab t3 (t / 282) (t % 282)))) = true := by
  decide +kernel

theorem chkC_6_d10568 : (List.range' 10568 8).all (fun t => (!(pOK tl tl (t % 282) (t / 282)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 282 % 94) * 282) (x2Tab o (t / 282 / 94) (t % 282))) (x2Tab t3 (t / 282) (t % 282)))) = true := by
  decide +kernel

theorem chkC_6_d10576 : (List.range' 10576 8).all (fun t => (!(pOK tl tl (t % 282) (t / 282)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 282 % 94) * 282) (x2Tab o (t / 282 / 94) (t % 282))) (x2Tab t3 (t / 282) (t % 282)))) = true := by
  decide +kernel

theorem chkC_6_d10584 : (List.range' 10584 8).all (fun t => (!(pOK tl tl (t % 282) (t / 282)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 282 % 94) * 282) (x2Tab o (t / 282 / 94) (t % 282))) (x2Tab t3 (t / 282) (t % 282)))) = true := by
  decide +kernel

theorem chkC_6_d10592 : (List.range' 10592 8).all (fun t => (!(pOK tl tl (t % 282) (t / 282)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 282 % 94) * 282) (x2Tab o (t / 282 / 94) (t % 282))) (x2Tab t3 (t / 282) (t % 282)))) = true := by
  decide +kernel

theorem chkC_6_d10600 : (List.range' 10600 8).all (fun t => (!(pOK tl tl (t % 282) (t / 282)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 282 % 94) * 282) (x2Tab o (t / 282 / 94) (t % 282))) (x2Tab t3 (t / 282) (t % 282)))) = true := by
  decide +kernel

theorem chkC_6_d10608 : (List.range' 10608 8).all (fun t => (!(pOK tl tl (t % 282) (t / 282)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 282 % 94) * 282) (x2Tab o (t / 282 / 94) (t % 282))) (x2Tab t3 (t / 282) (t % 282)))) = true := by
  decide +kernel

theorem chkC_6_d10616 : (List.range' 10616 8).all (fun t => (!(pOK tl tl (t % 282) (t / 282)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 282 % 94) * 282) (x2Tab o (t / 282 / 94) (t % 282))) (x2Tab t3 (t / 282) (t % 282)))) = true := by
  decide +kernel

theorem chkC_6_d10624 : (List.range' 10624 8).all (fun t => (!(pOK tl tl (t % 282) (t / 282)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 282 % 94) * 282) (x2Tab o (t / 282 / 94) (t % 282))) (x2Tab t3 (t / 282) (t % 282)))) = true := by
  decide +kernel

theorem chkC_6_d10632 : (List.range' 10632 8).all (fun t => (!(pOK tl tl (t % 282) (t / 282)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 282 % 94) * 282) (x2Tab o (t / 282 / 94) (t % 282))) (x2Tab t3 (t / 282) (t % 282)))) = true := by
  decide +kernel

theorem chkC_6_d10640 : (List.range' 10640 8).all (fun t => (!(pOK tl tl (t % 282) (t / 282)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 282 % 94) * 282) (x2Tab o (t / 282 / 94) (t % 282))) (x2Tab t3 (t / 282) (t % 282)))) = true := by
  decide +kernel

theorem chkC_6_d10648 : (List.range' 10648 8).all (fun t => (!(pOK tl tl (t % 282) (t / 282)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 282 % 94) * 282) (x2Tab o (t / 282 / 94) (t % 282))) (x2Tab t3 (t / 282) (t % 282)))) = true := by
  decide +kernel

theorem chkC_6_d10656 : (List.range' 10656 8).all (fun t => (!(pOK tl tl (t % 282) (t / 282)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 282 % 94) * 282) (x2Tab o (t / 282 / 94) (t % 282))) (x2Tab t3 (t / 282) (t % 282)))) = true := by
  decide +kernel

theorem chkC_6_d10664 : (List.range' 10664 8).all (fun t => (!(pOK tl tl (t % 282) (t / 282)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 282 % 94) * 282) (x2Tab o (t / 282 / 94) (t % 282))) (x2Tab t3 (t / 282) (t % 282)))) = true := by
  decide +kernel

theorem chkC_6_d10672 : (List.range' 10672 8).all (fun t => (!(pOK tl tl (t % 282) (t / 282)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 282 % 94) * 282) (x2Tab o (t / 282 / 94) (t % 282))) (x2Tab t3 (t / 282) (t % 282)))) = true := by
  decide +kernel

theorem chkC_6_d10680 : (List.range' 10680 8).all (fun t => (!(pOK tl tl (t % 282) (t / 282)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 282 % 94) * 282) (x2Tab o (t / 282 / 94) (t % 282))) (x2Tab t3 (t / 282) (t % 282)))) = true := by
  decide +kernel

theorem chkC_6_d10688 : (List.range' 10688 8).all (fun t => (!(pOK tl tl (t % 282) (t / 282)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 282 % 94) * 282) (x2Tab o (t / 282 / 94) (t % 282))) (x2Tab t3 (t / 282) (t % 282)))) = true := by
  decide +kernel

theorem chkC_6_d10696 : (List.range' 10696 8).all (fun t => (!(pOK tl tl (t % 282) (t / 282)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 282 % 94) * 282) (x2Tab o (t / 282 / 94) (t % 282))) (x2Tab t3 (t / 282) (t % 282)))) = true := by
  decide +kernel

theorem chkC_6_d10704 : (List.range' 10704 8).all (fun t => (!(pOK tl tl (t % 282) (t / 282)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 282 % 94) * 282) (x2Tab o (t / 282 / 94) (t % 282))) (x2Tab t3 (t / 282) (t % 282)))) = true := by
  decide +kernel

theorem chkC_6_d10712 : (List.range' 10712 8).all (fun t => (!(pOK tl tl (t % 282) (t / 282)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 282 % 94) * 282) (x2Tab o (t / 282 / 94) (t % 282))) (x2Tab t3 (t / 282) (t % 282)))) = true := by
  decide +kernel

theorem chkC_6_d10720 : (List.range' 10720 8).all (fun t => (!(pOK tl tl (t % 282) (t / 282)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 282 % 94) * 282) (x2Tab o (t / 282 / 94) (t % 282))) (x2Tab t3 (t / 282) (t % 282)))) = true := by
  decide +kernel

theorem chkC_6_d10728 : (List.range' 10728 8).all (fun t => (!(pOK tl tl (t % 282) (t / 282)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 282 % 94) * 282) (x2Tab o (t / 282 / 94) (t % 282))) (x2Tab t3 (t / 282) (t % 282)))) = true := by
  decide +kernel

theorem chkC_6_d10736 : (List.range' 10736 8).all (fun t => (!(pOK tl tl (t % 282) (t / 282)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 282 % 94) * 282) (x2Tab o (t / 282 / 94) (t % 282))) (x2Tab t3 (t / 282) (t % 282)))) = true := by
  decide +kernel

theorem chkC_6_d10744 : (List.range' 10744 8).all (fun t => (!(pOK tl tl (t % 282) (t / 282)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 282 % 94) * 282) (x2Tab o (t / 282 / 94) (t % 282))) (x2Tab t3 (t / 282) (t % 282)))) = true := by
  decide +kernel

theorem chkC_6_d10752 : (List.range' 10752 8).all (fun t => (!(pOK tl tl (t % 282) (t / 282)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 282 % 94) * 282) (x2Tab o (t / 282 / 94) (t % 282))) (x2Tab t3 (t / 282) (t % 282)))) = true := by
  decide +kernel

theorem chkC_6_d10760 : (List.range' 10760 8).all (fun t => (!(pOK tl tl (t % 282) (t / 282)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 282 % 94) * 282) (x2Tab o (t / 282 / 94) (t % 282))) (x2Tab t3 (t / 282) (t % 282)))) = true := by
  decide +kernel

theorem chkC_6_d10768 : (List.range' 10768 8).all (fun t => (!(pOK tl tl (t % 282) (t / 282)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 282 % 94) * 282) (x2Tab o (t / 282 / 94) (t % 282))) (x2Tab t3 (t / 282) (t % 282)))) = true := by
  decide +kernel

theorem chkC_6_d10776 : (List.range' 10776 8).all (fun t => (!(pOK tl tl (t % 282) (t / 282)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 282 % 94) * 282) (x2Tab o (t / 282 / 94) (t % 282))) (x2Tab t3 (t / 282) (t % 282)))) = true := by
  decide +kernel

theorem chkC_6_d10784 : (List.range' 10784 8).all (fun t => (!(pOK tl tl (t % 282) (t / 282)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 282 % 94) * 282) (x2Tab o (t / 282 / 94) (t % 282))) (x2Tab t3 (t / 282) (t % 282)))) = true := by
  decide +kernel

theorem chkC_6_d10792 : (List.range' 10792 8).all (fun t => (!(pOK tl tl (t % 282) (t / 282)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 282 % 94) * 282) (x2Tab o (t / 282 / 94) (t % 282))) (x2Tab t3 (t / 282) (t % 282)))) = true := by
  decide +kernel

theorem chkC_6_d10800 : (List.range' 10800 8).all (fun t => (!(pOK tl tl (t % 282) (t / 282)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 282 % 94) * 282) (x2Tab o (t / 282 / 94) (t % 282))) (x2Tab t3 (t / 282) (t % 282)))) = true := by
  decide +kernel

theorem chkC_6_d10808 : (List.range' 10808 8).all (fun t => (!(pOK tl tl (t % 282) (t / 282)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 282 % 94) * 282) (x2Tab o (t / 282 / 94) (t % 282))) (x2Tab t3 (t / 282) (t % 282)))) = true := by
  decide +kernel

theorem chkC_6_d10816 : (List.range' 10816 8).all (fun t => (!(pOK tl tl (t % 282) (t / 282)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 282 % 94) * 282) (x2Tab o (t / 282 / 94) (t % 282))) (x2Tab t3 (t / 282) (t % 282)))) = true := by
  decide +kernel

theorem chkC_6_d10824 : (List.range' 10824 8).all (fun t => (!(pOK tl tl (t % 282) (t / 282)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 282 % 94) * 282) (x2Tab o (t / 282 / 94) (t % 282))) (x2Tab t3 (t / 282) (t % 282)))) = true := by
  decide +kernel

theorem chkC_6_d10832 : (List.range' 10832 8).all (fun t => (!(pOK tl tl (t % 282) (t / 282)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 282 % 94) * 282) (x2Tab o (t / 282 / 94) (t % 282))) (x2Tab t3 (t / 282) (t % 282)))) = true := by
  decide +kernel

theorem chkC_6_d10840 : (List.range' 10840 8).all (fun t => (!(pOK tl tl (t % 282) (t / 282)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 282 % 94) * 282) (x2Tab o (t / 282 / 94) (t % 282))) (x2Tab t3 (t / 282) (t % 282)))) = true := by
  decide +kernel

theorem chkC_6_d10848 : (List.range' 10848 8).all (fun t => (!(pOK tl tl (t % 282) (t / 282)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 282 % 94) * 282) (x2Tab o (t / 282 / 94) (t % 282))) (x2Tab t3 (t / 282) (t % 282)))) = true := by
  decide +kernel

theorem chkC_6_d10856 : (List.range' 10856 8).all (fun t => (!(pOK tl tl (t % 282) (t / 282)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 282 % 94) * 282) (x2Tab o (t / 282 / 94) (t % 282))) (x2Tab t3 (t / 282) (t % 282)))) = true := by
  decide +kernel

theorem chkC_6_d10864 : (List.range' 10864 8).all (fun t => (!(pOK tl tl (t % 282) (t / 282)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 282 % 94) * 282) (x2Tab o (t / 282 / 94) (t % 282))) (x2Tab t3 (t / 282) (t % 282)))) = true := by
  decide +kernel

theorem chkC_6_d10872 : (List.range' 10872 8).all (fun t => (!(pOK tl tl (t % 282) (t / 282)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 282 % 94) * 282) (x2Tab o (t / 282 / 94) (t % 282))) (x2Tab t3 (t / 282) (t % 282)))) = true := by
  decide +kernel

theorem chkC_6_d10880 : (List.range' 10880 8).all (fun t => (!(pOK tl tl (t % 282) (t / 282)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 282 % 94) * 282) (x2Tab o (t / 282 / 94) (t % 282))) (x2Tab t3 (t / 282) (t % 282)))) = true := by
  decide +kernel

theorem chkC_6_d10888 : (List.range' 10888 8).all (fun t => (!(pOK tl tl (t % 282) (t / 282)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 282 % 94) * 282) (x2Tab o (t / 282 / 94) (t % 282))) (x2Tab t3 (t / 282) (t % 282)))) = true := by
  decide +kernel

theorem chkC_6_d10896 : (List.range' 10896 8).all (fun t => (!(pOK tl tl (t % 282) (t / 282)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 282 % 94) * 282) (x2Tab o (t / 282 / 94) (t % 282))) (x2Tab t3 (t / 282) (t % 282)))) = true := by
  decide +kernel

theorem chkC_6_d10904 : (List.range' 10904 8).all (fun t => (!(pOK tl tl (t % 282) (t / 282)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 282 % 94) * 282) (x2Tab o (t / 282 / 94) (t % 282))) (x2Tab t3 (t / 282) (t % 282)))) = true := by
  decide +kernel

theorem chkC_6_d10912 : (List.range' 10912 8).all (fun t => (!(pOK tl tl (t % 282) (t / 282)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 282 % 94) * 282) (x2Tab o (t / 282 / 94) (t % 282))) (x2Tab t3 (t / 282) (t % 282)))) = true := by
  decide +kernel

theorem chkC_6_d10920 : (List.range' 10920 8).all (fun t => (!(pOK tl tl (t % 282) (t / 282)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 282 % 94) * 282) (x2Tab o (t / 282 / 94) (t % 282))) (x2Tab t3 (t / 282) (t % 282)))) = true := by
  decide +kernel

theorem chkC_6_d10928 : (List.range' 10928 8).all (fun t => (!(pOK tl tl (t % 282) (t / 282)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 282 % 94) * 282) (x2Tab o (t / 282 / 94) (t % 282))) (x2Tab t3 (t / 282) (t % 282)))) = true := by
  decide +kernel

theorem chkC_6_d10936 : (List.range' 10936 8).all (fun t => (!(pOK tl tl (t % 282) (t / 282)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 282 % 94) * 282) (x2Tab o (t / 282 / 94) (t % 282))) (x2Tab t3 (t / 282) (t % 282)))) = true := by
  decide +kernel

theorem chkC_6_d10944 : (List.range' 10944 8).all (fun t => (!(pOK tl tl (t % 282) (t / 282)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 282 % 94) * 282) (x2Tab o (t / 282 / 94) (t % 282))) (x2Tab t3 (t / 282) (t % 282)))) = true := by
  decide +kernel

theorem chkC_6_d10952 : (List.range' 10952 8).all (fun t => (!(pOK tl tl (t % 282) (t / 282)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 282 % 94) * 282) (x2Tab o (t / 282 / 94) (t % 282))) (x2Tab t3 (t / 282) (t % 282)))) = true := by
  decide +kernel

theorem chkC_6_d10960 : (List.range' 10960 8).all (fun t => (!(pOK tl tl (t % 282) (t / 282)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 282 % 94) * 282) (x2Tab o (t / 282 / 94) (t % 282))) (x2Tab t3 (t / 282) (t % 282)))) = true := by
  decide +kernel

theorem chkC_6_d10968 : (List.range' 10968 8).all (fun t => (!(pOK tl tl (t % 282) (t / 282)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 282 % 94) * 282) (x2Tab o (t / 282 / 94) (t % 282))) (x2Tab t3 (t / 282) (t % 282)))) = true := by
  decide +kernel

theorem chkC_6_d10976 : (List.range' 10976 8).all (fun t => (!(pOK tl tl (t % 282) (t / 282)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 282 % 94) * 282) (x2Tab o (t / 282 / 94) (t % 282))) (x2Tab t3 (t / 282) (t % 282)))) = true := by
  decide +kernel

theorem chkC_6_d10984 : (List.range' 10984 8).all (fun t => (!(pOK tl tl (t % 282) (t / 282)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 282 % 94) * 282) (x2Tab o (t / 282 / 94) (t % 282))) (x2Tab t3 (t / 282) (t % 282)))) = true := by
  decide +kernel

theorem chkC_6_d10992 : (List.range' 10992 8).all (fun t => (!(pOK tl tl (t % 282) (t / 282)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 282 % 94) * 282) (x2Tab o (t / 282 / 94) (t % 282))) (x2Tab t3 (t / 282) (t % 282)))) = true := by
  decide +kernel

theorem chkC_6_d11000 : (List.range' 11000 8).all (fun t => (!(pOK tl tl (t % 282) (t / 282)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 282 % 94) * 282) (x2Tab o (t / 282 / 94) (t % 282))) (x2Tab t3 (t / 282) (t % 282)))) = true := by
  decide +kernel

theorem chkC_6_d11008 : (List.range' 11008 8).all (fun t => (!(pOK tl tl (t % 282) (t / 282)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 282 % 94) * 282) (x2Tab o (t / 282 / 94) (t % 282))) (x2Tab t3 (t / 282) (t % 282)))) = true := by
  decide +kernel

theorem chkC_6_d11016 : (List.range' 11016 8).all (fun t => (!(pOK tl tl (t % 282) (t / 282)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 282 % 94) * 282) (x2Tab o (t / 282 / 94) (t % 282))) (x2Tab t3 (t / 282) (t % 282)))) = true := by
  decide +kernel

theorem chkC_6_d11024 : (List.range' 11024 8).all (fun t => (!(pOK tl tl (t % 282) (t / 282)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 282 % 94) * 282) (x2Tab o (t / 282 / 94) (t % 282))) (x2Tab t3 (t / 282) (t % 282)))) = true := by
  decide +kernel

theorem chkC_6_d11032 : (List.range' 11032 8).all (fun t => (!(pOK tl tl (t % 282) (t / 282)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 282 % 94) * 282) (x2Tab o (t / 282 / 94) (t % 282))) (x2Tab t3 (t / 282) (t % 282)))) = true := by
  decide +kernel

theorem chkC_6_d11040 : (List.range' 11040 8).all (fun t => (!(pOK tl tl (t % 282) (t / 282)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 282 % 94) * 282) (x2Tab o (t / 282 / 94) (t % 282))) (x2Tab t3 (t / 282) (t % 282)))) = true := by
  decide +kernel

theorem chkC_6_d11048 : (List.range' 11048 8).all (fun t => (!(pOK tl tl (t % 282) (t / 282)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 282 % 94) * 282) (x2Tab o (t / 282 / 94) (t % 282))) (x2Tab t3 (t / 282) (t % 282)))) = true := by
  decide +kernel

theorem chkC_6_d11056 : (List.range' 11056 8).all (fun t => (!(pOK tl tl (t % 282) (t / 282)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 282 % 94) * 282) (x2Tab o (t / 282 / 94) (t % 282))) (x2Tab t3 (t / 282) (t % 282)))) = true := by
  decide +kernel

theorem chkC_6_d11064 : (List.range' 11064 8).all (fun t => (!(pOK tl tl (t % 282) (t / 282)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 282 % 94) * 282) (x2Tab o (t / 282 / 94) (t % 282))) (x2Tab t3 (t / 282) (t % 282)))) = true := by
  decide +kernel

theorem chkC_6_d11072 : (List.range' 11072 8).all (fun t => (!(pOK tl tl (t % 282) (t / 282)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 282 % 94) * 282) (x2Tab o (t / 282 / 94) (t % 282))) (x2Tab t3 (t / 282) (t % 282)))) = true := by
  decide +kernel

theorem chkC_6_d11080 : (List.range' 11080 8).all (fun t => (!(pOK tl tl (t % 282) (t / 282)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 282 % 94) * 282) (x2Tab o (t / 282 / 94) (t % 282))) (x2Tab t3 (t / 282) (t % 282)))) = true := by
  decide +kernel

theorem chkC_6_d11088 : (List.range' 11088 8).all (fun t => (!(pOK tl tl (t % 282) (t / 282)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 282 % 94) * 282) (x2Tab o (t / 282 / 94) (t % 282))) (x2Tab t3 (t / 282) (t % 282)))) = true := by
  decide +kernel

theorem chkC_6_d11096 : (List.range' 11096 8).all (fun t => (!(pOK tl tl (t % 282) (t / 282)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 282 % 94) * 282) (x2Tab o (t / 282 / 94) (t % 282))) (x2Tab t3 (t / 282) (t % 282)))) = true := by
  decide +kernel

theorem chkC_6_d11104 : (List.range' 11104 8).all (fun t => (!(pOK tl tl (t % 282) (t / 282)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 282 % 94) * 282) (x2Tab o (t / 282 / 94) (t % 282))) (x2Tab t3 (t / 282) (t % 282)))) = true := by
  decide +kernel

theorem chkC_6_d11112 : (List.range' 11112 8).all (fun t => (!(pOK tl tl (t % 282) (t / 282)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 282 % 94) * 282) (x2Tab o (t / 282 / 94) (t % 282))) (x2Tab t3 (t / 282) (t % 282)))) = true := by
  decide +kernel

theorem chkC_6_d11120 : (List.range' 11120 8).all (fun t => (!(pOK tl tl (t % 282) (t / 282)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 282 % 94) * 282) (x2Tab o (t / 282 / 94) (t % 282))) (x2Tab t3 (t / 282) (t % 282)))) = true := by
  decide +kernel

theorem chkC_6_d11128 : (List.range' 11128 8).all (fun t => (!(pOK tl tl (t % 282) (t / 282)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 282 % 94) * 282) (x2Tab o (t / 282 / 94) (t % 282))) (x2Tab t3 (t / 282) (t % 282)))) = true := by
  decide +kernel

theorem chkC_6_d11136 : (List.range' 11136 8).all (fun t => (!(pOK tl tl (t % 282) (t / 282)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 282 % 94) * 282) (x2Tab o (t / 282 / 94) (t % 282))) (x2Tab t3 (t / 282) (t % 282)))) = true := by
  decide +kernel

theorem chkC_6_d11144 : (List.range' 11144 8).all (fun t => (!(pOK tl tl (t % 282) (t / 282)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 282 % 94) * 282) (x2Tab o (t / 282 / 94) (t % 282))) (x2Tab t3 (t / 282) (t % 282)))) = true := by
  decide +kernel

theorem chkC_6_d11152 : (List.range' 11152 8).all (fun t => (!(pOK tl tl (t % 282) (t / 282)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 282 % 94) * 282) (x2Tab o (t / 282 / 94) (t % 282))) (x2Tab t3 (t / 282) (t % 282)))) = true := by
  decide +kernel

theorem chkC_6_d11160 : (List.range' 11160 8).all (fun t => (!(pOK tl tl (t % 282) (t / 282)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 282 % 94) * 282) (x2Tab o (t / 282 / 94) (t % 282))) (x2Tab t3 (t / 282) (t % 282)))) = true := by
  decide +kernel

theorem chkC_6_d11168 : (List.range' 11168 8).all (fun t => (!(pOK tl tl (t % 282) (t / 282)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 282 % 94) * 282) (x2Tab o (t / 282 / 94) (t % 282))) (x2Tab t3 (t / 282) (t % 282)))) = true := by
  decide +kernel

theorem chkC_6_d11176 : (List.range' 11176 8).all (fun t => (!(pOK tl tl (t % 282) (t / 282)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 282 % 94) * 282) (x2Tab o (t / 282 / 94) (t % 282))) (x2Tab t3 (t / 282) (t % 282)))) = true := by
  decide +kernel

theorem chkC_6_d11184 : (List.range' 11184 8).all (fun t => (!(pOK tl tl (t % 282) (t / 282)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 282 % 94) * 282) (x2Tab o (t / 282 / 94) (t % 282))) (x2Tab t3 (t / 282) (t % 282)))) = true := by
  decide +kernel

theorem chkC_6_d11192 : (List.range' 11192 8).all (fun t => (!(pOK tl tl (t % 282) (t / 282)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 282 % 94) * 282) (x2Tab o (t / 282 / 94) (t % 282))) (x2Tab t3 (t / 282) (t % 282)))) = true := by
  decide +kernel

theorem chkC_6 : ∀ t, 9600 ≤ t → t < 11200 → ((!(pOK tl tl (t % 282) (t / 282)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 282 % 94) * 282) (x2Tab o (t / 282 / 94) (t % 282))) (x2Tab t3 (t / 282) (t % 282)))) = true := by
  exact (x2c_join _ 9600 9608 11200 (x2c_range_all (fun t => (!(pOK tl tl (t % 282) (t / 282)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 282 % 94) * 282) (x2Tab o (t / 282 / 94) (t % 282))) (x2Tab t3 (t / 282) (t % 282)))) 9600 8 chkC_6_d9600) (x2c_join _ 9608 9616 11200 (x2c_range_all (fun t => (!(pOK tl tl (t % 282) (t / 282)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 282 % 94) * 282) (x2Tab o (t / 282 / 94) (t % 282))) (x2Tab t3 (t / 282) (t % 282)))) 9608 8 chkC_6_d9608) (x2c_join _ 9616 9624 11200 (x2c_range_all (fun t => (!(pOK tl tl (t % 282) (t / 282)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 282 % 94) * 282) (x2Tab o (t / 282 / 94) (t % 282))) (x2Tab t3 (t / 282) (t % 282)))) 9616 8 chkC_6_d9616) (x2c_join _ 9624 9632 11200 (x2c_range_all (fun t => (!(pOK tl tl (t % 282) (t / 282)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 282 % 94) * 282) (x2Tab o (t / 282 / 94) (t % 282))) (x2Tab t3 (t / 282) (t % 282)))) 9624 8 chkC_6_d9624) (x2c_join _ 9632 9640 11200 (x2c_range_all (fun t => (!(pOK tl tl (t % 282) (t / 282)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 282 % 94) * 282) (x2Tab o (t / 282 / 94) (t % 282))) (x2Tab t3 (t / 282) (t % 282)))) 9632 8 chkC_6_d9632) (x2c_join _ 9640 9648 11200 (x2c_range_all (fun t => (!(pOK tl tl (t % 282) (t / 282)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 282 % 94) * 282) (x2Tab o (t / 282 / 94) (t % 282))) (x2Tab t3 (t / 282) (t % 282)))) 9640 8 chkC_6_d9640) (x2c_join _ 9648 9656 11200 (x2c_range_all (fun t => (!(pOK tl tl (t % 282) (t / 282)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 282 % 94) * 282) (x2Tab o (t / 282 / 94) (t % 282))) (x2Tab t3 (t / 282) (t % 282)))) 9648 8 chkC_6_d9648) (x2c_join _ 9656 9664 11200 (x2c_range_all (fun t => (!(pOK tl tl (t % 282) (t / 282)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 282 % 94) * 282) (x2Tab o (t / 282 / 94) (t % 282))) (x2Tab t3 (t / 282) (t % 282)))) 9656 8 chkC_6_d9656) (x2c_join _ 9664 9672 11200 (x2c_range_all (fun t => (!(pOK tl tl (t % 282) (t / 282)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 282 % 94) * 282) (x2Tab o (t / 282 / 94) (t % 282))) (x2Tab t3 (t / 282) (t % 282)))) 9664 8 chkC_6_d9664) (x2c_join _ 9672 9680 11200 (x2c_range_all (fun t => (!(pOK tl tl (t % 282) (t / 282)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 282 % 94) * 282) (x2Tab o (t / 282 / 94) (t % 282))) (x2Tab t3 (t / 282) (t % 282)))) 9672 8 chkC_6_d9672) (x2c_join _ 9680 9688 11200 (x2c_range_all (fun t => (!(pOK tl tl (t % 282) (t / 282)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 282 % 94) * 282) (x2Tab o (t / 282 / 94) (t % 282))) (x2Tab t3 (t / 282) (t % 282)))) 9680 8 chkC_6_d9680) (x2c_join _ 9688 9696 11200 (x2c_range_all (fun t => (!(pOK tl tl (t % 282) (t / 282)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 282 % 94) * 282) (x2Tab o (t / 282 / 94) (t % 282))) (x2Tab t3 (t / 282) (t % 282)))) 9688 8 chkC_6_d9688) (x2c_join _ 9696 9704 11200 (x2c_range_all (fun t => (!(pOK tl tl (t % 282) (t / 282)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 282 % 94) * 282) (x2Tab o (t / 282 / 94) (t % 282))) (x2Tab t3 (t / 282) (t % 282)))) 9696 8 chkC_6_d9696) (x2c_join _ 9704 9712 11200 (x2c_range_all (fun t => (!(pOK tl tl (t % 282) (t / 282)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 282 % 94) * 282) (x2Tab o (t / 282 / 94) (t % 282))) (x2Tab t3 (t / 282) (t % 282)))) 9704 8 chkC_6_d9704) (x2c_join _ 9712 9720 11200 (x2c_range_all (fun t => (!(pOK tl tl (t % 282) (t / 282)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 282 % 94) * 282) (x2Tab o (t / 282 / 94) (t % 282))) (x2Tab t3 (t / 282) (t % 282)))) 9712 8 chkC_6_d9712) (x2c_join _ 9720 9728 11200 (x2c_range_all (fun t => (!(pOK tl tl (t % 282) (t / 282)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 282 % 94) * 282) (x2Tab o (t / 282 / 94) (t % 282))) (x2Tab t3 (t / 282) (t % 282)))) 9720 8 chkC_6_d9720) (x2c_join _ 9728 9736 11200 (x2c_range_all (fun t => (!(pOK tl tl (t % 282) (t / 282)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 282 % 94) * 282) (x2Tab o (t / 282 / 94) (t % 282))) (x2Tab t3 (t / 282) (t % 282)))) 9728 8 chkC_6_d9728) (x2c_join _ 9736 9744 11200 (x2c_range_all (fun t => (!(pOK tl tl (t % 282) (t / 282)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 282 % 94) * 282) (x2Tab o (t / 282 / 94) (t % 282))) (x2Tab t3 (t / 282) (t % 282)))) 9736 8 chkC_6_d9736) (x2c_join _ 9744 9752 11200 (x2c_range_all (fun t => (!(pOK tl tl (t % 282) (t / 282)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 282 % 94) * 282) (x2Tab o (t / 282 / 94) (t % 282))) (x2Tab t3 (t / 282) (t % 282)))) 9744 8 chkC_6_d9744) (x2c_join _ 9752 9760 11200 (x2c_range_all (fun t => (!(pOK tl tl (t % 282) (t / 282)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 282 % 94) * 282) (x2Tab o (t / 282 / 94) (t % 282))) (x2Tab t3 (t / 282) (t % 282)))) 9752 8 chkC_6_d9752) (x2c_join _ 9760 9768 11200 (x2c_range_all (fun t => (!(pOK tl tl (t % 282) (t / 282)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 282 % 94) * 282) (x2Tab o (t / 282 / 94) (t % 282))) (x2Tab t3 (t / 282) (t % 282)))) 9760 8 chkC_6_d9760) (x2c_join _ 9768 9776 11200 (x2c_range_all (fun t => (!(pOK tl tl (t % 282) (t / 282)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 282 % 94) * 282) (x2Tab o (t / 282 / 94) (t % 282))) (x2Tab t3 (t / 282) (t % 282)))) 9768 8 chkC_6_d9768) (x2c_join _ 9776 9784 11200 (x2c_range_all (fun t => (!(pOK tl tl (t % 282) (t / 282)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 282 % 94) * 282) (x2Tab o (t / 282 / 94) (t % 282))) (x2Tab t3 (t / 282) (t % 282)))) 9776 8 chkC_6_d9776) (x2c_join _ 9784 9792 11200 (x2c_range_all (fun t => (!(pOK tl tl (t % 282) (t / 282)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 282 % 94) * 282) (x2Tab o (t / 282 / 94) (t % 282))) (x2Tab t3 (t / 282) (t % 282)))) 9784 8 chkC_6_d9784) (x2c_join _ 9792 9800 11200 (x2c_range_all (fun t => (!(pOK tl tl (t % 282) (t / 282)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 282 % 94) * 282) (x2Tab o (t / 282 / 94) (t % 282))) (x2Tab t3 (t / 282) (t % 282)))) 9792 8 chkC_6_d9792) (x2c_join _ 9800 9808 11200 (x2c_range_all (fun t => (!(pOK tl tl (t % 282) (t / 282)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 282 % 94) * 282) (x2Tab o (t / 282 / 94) (t % 282))) (x2Tab t3 (t / 282) (t % 282)))) 9800 8 chkC_6_d9800) (x2c_join _ 9808 9816 11200 (x2c_range_all (fun t => (!(pOK tl tl (t % 282) (t / 282)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 282 % 94) * 282) (x2Tab o (t / 282 / 94) (t % 282))) (x2Tab t3 (t / 282) (t % 282)))) 9808 8 chkC_6_d9808) (x2c_join _ 9816 9824 11200 (x2c_range_all (fun t => (!(pOK tl tl (t % 282) (t / 282)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 282 % 94) * 282) (x2Tab o (t / 282 / 94) (t % 282))) (x2Tab t3 (t / 282) (t % 282)))) 9816 8 chkC_6_d9816) (x2c_join _ 9824 9832 11200 (x2c_range_all (fun t => (!(pOK tl tl (t % 282) (t / 282)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 282 % 94) * 282) (x2Tab o (t / 282 / 94) (t % 282))) (x2Tab t3 (t / 282) (t % 282)))) 9824 8 chkC_6_d9824) (x2c_join _ 9832 9840 11200 (x2c_range_all (fun t => (!(pOK tl tl (t % 282) (t / 282)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 282 % 94) * 282) (x2Tab o (t / 282 / 94) (t % 282))) (x2Tab t3 (t / 282) (t % 282)))) 9832 8 chkC_6_d9832) (x2c_join _ 9840 9848 11200 (x2c_range_all (fun t => (!(pOK tl tl (t % 282) (t / 282)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 282 % 94) * 282) (x2Tab o (t / 282 / 94) (t % 282))) (x2Tab t3 (t / 282) (t % 282)))) 9840 8 chkC_6_d9840) (x2c_join _ 9848 9856 11200 (x2c_range_all (fun t => (!(pOK tl tl (t % 282) (t / 282)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 282 % 94) * 282) (x2Tab o (t / 282 / 94) (t % 282))) (x2Tab t3 (t / 282) (t % 282)))) 9848 8 chkC_6_d9848) (x2c_join _ 9856 9864 11200 (x2c_range_all (fun t => (!(pOK tl tl (t % 282) (t / 282)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 282 % 94) * 282) (x2Tab o (t / 282 / 94) (t % 282))) (x2Tab t3 (t / 282) (t % 282)))) 9856 8 chkC_6_d9856) (x2c_join _ 9864 9872 11200 (x2c_range_all (fun t => (!(pOK tl tl (t % 282) (t / 282)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 282 % 94) * 282) (x2Tab o (t / 282 / 94) (t % 282))) (x2Tab t3 (t / 282) (t % 282)))) 9864 8 chkC_6_d9864) (x2c_join _ 9872 9880 11200 (x2c_range_all (fun t => (!(pOK tl tl (t % 282) (t / 282)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 282 % 94) * 282) (x2Tab o (t / 282 / 94) (t % 282))) (x2Tab t3 (t / 282) (t % 282)))) 9872 8 chkC_6_d9872) (x2c_join _ 9880 9888 11200 (x2c_range_all (fun t => (!(pOK tl tl (t % 282) (t / 282)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 282 % 94) * 282) (x2Tab o (t / 282 / 94) (t % 282))) (x2Tab t3 (t / 282) (t % 282)))) 9880 8 chkC_6_d9880) (x2c_join _ 9888 9896 11200 (x2c_range_all (fun t => (!(pOK tl tl (t % 282) (t / 282)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 282 % 94) * 282) (x2Tab o (t / 282 / 94) (t % 282))) (x2Tab t3 (t / 282) (t % 282)))) 9888 8 chkC_6_d9888) (x2c_join _ 9896 9904 11200 (x2c_range_all (fun t => (!(pOK tl tl (t % 282) (t / 282)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 282 % 94) * 282) (x2Tab o (t / 282 / 94) (t % 282))) (x2Tab t3 (t / 282) (t % 282)))) 9896 8 chkC_6_d9896) (x2c_join _ 9904 9912 11200 (x2c_range_all (fun t => (!(pOK tl tl (t % 282) (t / 282)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 282 % 94) * 282) (x2Tab o (t / 282 / 94) (t % 282))) (x2Tab t3 (t / 282) (t % 282)))) 9904 8 chkC_6_d9904) (x2c_join _ 9912 9920 11200 (x2c_range_all (fun t => (!(pOK tl tl (t % 282) (t / 282)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 282 % 94) * 282) (x2Tab o (t / 282 / 94) (t % 282))) (x2Tab t3 (t / 282) (t % 282)))) 9912 8 chkC_6_d9912) (x2c_join _ 9920 9928 11200 (x2c_range_all (fun t => (!(pOK tl tl (t % 282) (t / 282)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 282 % 94) * 282) (x2Tab o (t / 282 / 94) (t % 282))) (x2Tab t3 (t / 282) (t % 282)))) 9920 8 chkC_6_d9920) (x2c_join _ 9928 9936 11200 (x2c_range_all (fun t => (!(pOK tl tl (t % 282) (t / 282)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 282 % 94) * 282) (x2Tab o (t / 282 / 94) (t % 282))) (x2Tab t3 (t / 282) (t % 282)))) 9928 8 chkC_6_d9928) (x2c_join _ 9936 9944 11200 (x2c_range_all (fun t => (!(pOK tl tl (t % 282) (t / 282)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 282 % 94) * 282) (x2Tab o (t / 282 / 94) (t % 282))) (x2Tab t3 (t / 282) (t % 282)))) 9936 8 chkC_6_d9936) (x2c_join _ 9944 9952 11200 (x2c_range_all (fun t => (!(pOK tl tl (t % 282) (t / 282)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 282 % 94) * 282) (x2Tab o (t / 282 / 94) (t % 282))) (x2Tab t3 (t / 282) (t % 282)))) 9944 8 chkC_6_d9944) (x2c_join _ 9952 9960 11200 (x2c_range_all (fun t => (!(pOK tl tl (t % 282) (t / 282)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 282 % 94) * 282) (x2Tab o (t / 282 / 94) (t % 282))) (x2Tab t3 (t / 282) (t % 282)))) 9952 8 chkC_6_d9952) (x2c_join _ 9960 9968 11200 (x2c_range_all (fun t => (!(pOK tl tl (t % 282) (t / 282)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 282 % 94) * 282) (x2Tab o (t / 282 / 94) (t % 282))) (x2Tab t3 (t / 282) (t % 282)))) 9960 8 chkC_6_d9960) (x2c_join _ 9968 9976 11200 (x2c_range_all (fun t => (!(pOK tl tl (t % 282) (t / 282)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 282 % 94) * 282) (x2Tab o (t / 282 / 94) (t % 282))) (x2Tab t3 (t / 282) (t % 282)))) 9968 8 chkC_6_d9968) (x2c_join _ 9976 9984 11200 (x2c_range_all (fun t => (!(pOK tl tl (t % 282) (t / 282)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 282 % 94) * 282) (x2Tab o (t / 282 / 94) (t % 282))) (x2Tab t3 (t / 282) (t % 282)))) 9976 8 chkC_6_d9976) (x2c_join _ 9984 9992 11200 (x2c_range_all (fun t => (!(pOK tl tl (t % 282) (t / 282)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 282 % 94) * 282) (x2Tab o (t / 282 / 94) (t % 282))) (x2Tab t3 (t / 282) (t % 282)))) 9984 8 chkC_6_d9984) (x2c_join _ 9992 10000 11200 (x2c_range_all (fun t => (!(pOK tl tl (t % 282) (t / 282)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 282 % 94) * 282) (x2Tab o (t / 282 / 94) (t % 282))) (x2Tab t3 (t / 282) (t % 282)))) 9992 8 chkC_6_d9992) (x2c_join _ 10000 10008 11200 (x2c_range_all (fun t => (!(pOK tl tl (t % 282) (t / 282)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 282 % 94) * 282) (x2Tab o (t / 282 / 94) (t % 282))) (x2Tab t3 (t / 282) (t % 282)))) 10000 8 chkC_6_d10000) (x2c_join _ 10008 10016 11200 (x2c_range_all (fun t => (!(pOK tl tl (t % 282) (t / 282)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 282 % 94) * 282) (x2Tab o (t / 282 / 94) (t % 282))) (x2Tab t3 (t / 282) (t % 282)))) 10008 8 chkC_6_d10008) (x2c_join _ 10016 10024 11200 (x2c_range_all (fun t => (!(pOK tl tl (t % 282) (t / 282)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 282 % 94) * 282) (x2Tab o (t / 282 / 94) (t % 282))) (x2Tab t3 (t / 282) (t % 282)))) 10016 8 chkC_6_d10016) (x2c_join _ 10024 10032 11200 (x2c_range_all (fun t => (!(pOK tl tl (t % 282) (t / 282)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 282 % 94) * 282) (x2Tab o (t / 282 / 94) (t % 282))) (x2Tab t3 (t / 282) (t % 282)))) 10024 8 chkC_6_d10024) (x2c_join _ 10032 10040 11200 (x2c_range_all (fun t => (!(pOK tl tl (t % 282) (t / 282)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 282 % 94) * 282) (x2Tab o (t / 282 / 94) (t % 282))) (x2Tab t3 (t / 282) (t % 282)))) 10032 8 chkC_6_d10032) (x2c_join _ 10040 10048 11200 (x2c_range_all (fun t => (!(pOK tl tl (t % 282) (t / 282)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 282 % 94) * 282) (x2Tab o (t / 282 / 94) (t % 282))) (x2Tab t3 (t / 282) (t % 282)))) 10040 8 chkC_6_d10040) (x2c_join _ 10048 10056 11200 (x2c_range_all (fun t => (!(pOK tl tl (t % 282) (t / 282)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 282 % 94) * 282) (x2Tab o (t / 282 / 94) (t % 282))) (x2Tab t3 (t / 282) (t % 282)))) 10048 8 chkC_6_d10048) (x2c_join _ 10056 10064 11200 (x2c_range_all (fun t => (!(pOK tl tl (t % 282) (t / 282)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 282 % 94) * 282) (x2Tab o (t / 282 / 94) (t % 282))) (x2Tab t3 (t / 282) (t % 282)))) 10056 8 chkC_6_d10056) (x2c_join _ 10064 10072 11200 (x2c_range_all (fun t => (!(pOK tl tl (t % 282) (t / 282)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 282 % 94) * 282) (x2Tab o (t / 282 / 94) (t % 282))) (x2Tab t3 (t / 282) (t % 282)))) 10064 8 chkC_6_d10064) (x2c_join _ 10072 10080 11200 (x2c_range_all (fun t => (!(pOK tl tl (t % 282) (t / 282)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 282 % 94) * 282) (x2Tab o (t / 282 / 94) (t % 282))) (x2Tab t3 (t / 282) (t % 282)))) 10072 8 chkC_6_d10072) (x2c_join _ 10080 10088 11200 (x2c_range_all (fun t => (!(pOK tl tl (t % 282) (t / 282)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 282 % 94) * 282) (x2Tab o (t / 282 / 94) (t % 282))) (x2Tab t3 (t / 282) (t % 282)))) 10080 8 chkC_6_d10080) (x2c_join _ 10088 10096 11200 (x2c_range_all (fun t => (!(pOK tl tl (t % 282) (t / 282)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 282 % 94) * 282) (x2Tab o (t / 282 / 94) (t % 282))) (x2Tab t3 (t / 282) (t % 282)))) 10088 8 chkC_6_d10088) (x2c_join _ 10096 10104 11200 (x2c_range_all (fun t => (!(pOK tl tl (t % 282) (t / 282)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 282 % 94) * 282) (x2Tab o (t / 282 / 94) (t % 282))) (x2Tab t3 (t / 282) (t % 282)))) 10096 8 chkC_6_d10096) (x2c_join _ 10104 10112 11200 (x2c_range_all (fun t => (!(pOK tl tl (t % 282) (t / 282)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 282 % 94) * 282) (x2Tab o (t / 282 / 94) (t % 282))) (x2Tab t3 (t / 282) (t % 282)))) 10104 8 chkC_6_d10104) (x2c_join _ 10112 10120 11200 (x2c_range_all (fun t => (!(pOK tl tl (t % 282) (t / 282)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 282 % 94) * 282) (x2Tab o (t / 282 / 94) (t % 282))) (x2Tab t3 (t / 282) (t % 282)))) 10112 8 chkC_6_d10112) (x2c_join _ 10120 10128 11200 (x2c_range_all (fun t => (!(pOK tl tl (t % 282) (t / 282)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 282 % 94) * 282) (x2Tab o (t / 282 / 94) (t % 282))) (x2Tab t3 (t / 282) (t % 282)))) 10120 8 chkC_6_d10120) (x2c_join _ 10128 10136 11200 (x2c_range_all (fun t => (!(pOK tl tl (t % 282) (t / 282)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 282 % 94) * 282) (x2Tab o (t / 282 / 94) (t % 282))) (x2Tab t3 (t / 282) (t % 282)))) 10128 8 chkC_6_d10128) (x2c_join _ 10136 10144 11200 (x2c_range_all (fun t => (!(pOK tl tl (t % 282) (t / 282)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 282 % 94) * 282) (x2Tab o (t / 282 / 94) (t % 282))) (x2Tab t3 (t / 282) (t % 282)))) 10136 8 chkC_6_d10136) (x2c_join _ 10144 10152 11200 (x2c_range_all (fun t => (!(pOK tl tl (t % 282) (t / 282)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 282 % 94) * 282) (x2Tab o (t / 282 / 94) (t % 282))) (x2Tab t3 (t / 282) (t % 282)))) 10144 8 chkC_6_d10144) (x2c_join _ 10152 10160 11200 (x2c_range_all (fun t => (!(pOK tl tl (t % 282) (t / 282)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 282 % 94) * 282) (x2Tab o (t / 282 / 94) (t % 282))) (x2Tab t3 (t / 282) (t % 282)))) 10152 8 chkC_6_d10152) (x2c_join _ 10160 10168 11200 (x2c_range_all (fun t => (!(pOK tl tl (t % 282) (t / 282)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 282 % 94) * 282) (x2Tab o (t / 282 / 94) (t % 282))) (x2Tab t3 (t / 282) (t % 282)))) 10160 8 chkC_6_d10160) (x2c_join _ 10168 10176 11200 (x2c_range_all (fun t => (!(pOK tl tl (t % 282) (t / 282)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 282 % 94) * 282) (x2Tab o (t / 282 / 94) (t % 282))) (x2Tab t3 (t / 282) (t % 282)))) 10168 8 chkC_6_d10168) (x2c_join _ 10176 10184 11200 (x2c_range_all (fun t => (!(pOK tl tl (t % 282) (t / 282)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 282 % 94) * 282) (x2Tab o (t / 282 / 94) (t % 282))) (x2Tab t3 (t / 282) (t % 282)))) 10176 8 chkC_6_d10176) (x2c_join _ 10184 10192 11200 (x2c_range_all (fun t => (!(pOK tl tl (t % 282) (t / 282)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 282 % 94) * 282) (x2Tab o (t / 282 / 94) (t % 282))) (x2Tab t3 (t / 282) (t % 282)))) 10184 8 chkC_6_d10184) (x2c_join _ 10192 10200 11200 (x2c_range_all (fun t => (!(pOK tl tl (t % 282) (t / 282)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 282 % 94) * 282) (x2Tab o (t / 282 / 94) (t % 282))) (x2Tab t3 (t / 282) (t % 282)))) 10192 8 chkC_6_d10192) (x2c_join _ 10200 10208 11200 (x2c_range_all (fun t => (!(pOK tl tl (t % 282) (t / 282)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 282 % 94) * 282) (x2Tab o (t / 282 / 94) (t % 282))) (x2Tab t3 (t / 282) (t % 282)))) 10200 8 chkC_6_d10200) (x2c_join _ 10208 10216 11200 (x2c_range_all (fun t => (!(pOK tl tl (t % 282) (t / 282)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 282 % 94) * 282) (x2Tab o (t / 282 / 94) (t % 282))) (x2Tab t3 (t / 282) (t % 282)))) 10208 8 chkC_6_d10208) (x2c_join _ 10216 10224 11200 (x2c_range_all (fun t => (!(pOK tl tl (t % 282) (t / 282)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 282 % 94) * 282) (x2Tab o (t / 282 / 94) (t % 282))) (x2Tab t3 (t / 282) (t % 282)))) 10216 8 chkC_6_d10216) (x2c_join _ 10224 10232 11200 (x2c_range_all (fun t => (!(pOK tl tl (t % 282) (t / 282)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 282 % 94) * 282) (x2Tab o (t / 282 / 94) (t % 282))) (x2Tab t3 (t / 282) (t % 282)))) 10224 8 chkC_6_d10224) (x2c_join _ 10232 10240 11200 (x2c_range_all (fun t => (!(pOK tl tl (t % 282) (t / 282)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 282 % 94) * 282) (x2Tab o (t / 282 / 94) (t % 282))) (x2Tab t3 (t / 282) (t % 282)))) 10232 8 chkC_6_d10232) (x2c_join _ 10240 10248 11200 (x2c_range_all (fun t => (!(pOK tl tl (t % 282) (t / 282)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 282 % 94) * 282) (x2Tab o (t / 282 / 94) (t % 282))) (x2Tab t3 (t / 282) (t % 282)))) 10240 8 chkC_6_d10240) (x2c_join _ 10248 10256 11200 (x2c_range_all (fun t => (!(pOK tl tl (t % 282) (t / 282)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 282 % 94) * 282) (x2Tab o (t / 282 / 94) (t % 282))) (x2Tab t3 (t / 282) (t % 282)))) 10248 8 chkC_6_d10248) (x2c_join _ 10256 10264 11200 (x2c_range_all (fun t => (!(pOK tl tl (t % 282) (t / 282)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 282 % 94) * 282) (x2Tab o (t / 282 / 94) (t % 282))) (x2Tab t3 (t / 282) (t % 282)))) 10256 8 chkC_6_d10256) (x2c_join _ 10264 10272 11200 (x2c_range_all (fun t => (!(pOK tl tl (t % 282) (t / 282)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 282 % 94) * 282) (x2Tab o (t / 282 / 94) (t % 282))) (x2Tab t3 (t / 282) (t % 282)))) 10264 8 chkC_6_d10264) (x2c_join _ 10272 10280 11200 (x2c_range_all (fun t => (!(pOK tl tl (t % 282) (t / 282)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 282 % 94) * 282) (x2Tab o (t / 282 / 94) (t % 282))) (x2Tab t3 (t / 282) (t % 282)))) 10272 8 chkC_6_d10272) (x2c_join _ 10280 10288 11200 (x2c_range_all (fun t => (!(pOK tl tl (t % 282) (t / 282)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 282 % 94) * 282) (x2Tab o (t / 282 / 94) (t % 282))) (x2Tab t3 (t / 282) (t % 282)))) 10280 8 chkC_6_d10280) (x2c_join _ 10288 10296 11200 (x2c_range_all (fun t => (!(pOK tl tl (t % 282) (t / 282)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 282 % 94) * 282) (x2Tab o (t / 282 / 94) (t % 282))) (x2Tab t3 (t / 282) (t % 282)))) 10288 8 chkC_6_d10288) (x2c_join _ 10296 10304 11200 (x2c_range_all (fun t => (!(pOK tl tl (t % 282) (t / 282)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 282 % 94) * 282) (x2Tab o (t / 282 / 94) (t % 282))) (x2Tab t3 (t / 282) (t % 282)))) 10296 8 chkC_6_d10296) (x2c_join _ 10304 10312 11200 (x2c_range_all (fun t => (!(pOK tl tl (t % 282) (t / 282)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 282 % 94) * 282) (x2Tab o (t / 282 / 94) (t % 282))) (x2Tab t3 (t / 282) (t % 282)))) 10304 8 chkC_6_d10304) (x2c_join _ 10312 10320 11200 (x2c_range_all (fun t => (!(pOK tl tl (t % 282) (t / 282)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 282 % 94) * 282) (x2Tab o (t / 282 / 94) (t % 282))) (x2Tab t3 (t / 282) (t % 282)))) 10312 8 chkC_6_d10312) (x2c_join _ 10320 10328 11200 (x2c_range_all (fun t => (!(pOK tl tl (t % 282) (t / 282)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 282 % 94) * 282) (x2Tab o (t / 282 / 94) (t % 282))) (x2Tab t3 (t / 282) (t % 282)))) 10320 8 chkC_6_d10320) (x2c_join _ 10328 10336 11200 (x2c_range_all (fun t => (!(pOK tl tl (t % 282) (t / 282)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 282 % 94) * 282) (x2Tab o (t / 282 / 94) (t % 282))) (x2Tab t3 (t / 282) (t % 282)))) 10328 8 chkC_6_d10328) (x2c_join _ 10336 10344 11200 (x2c_range_all (fun t => (!(pOK tl tl (t % 282) (t / 282)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 282 % 94) * 282) (x2Tab o (t / 282 / 94) (t % 282))) (x2Tab t3 (t / 282) (t % 282)))) 10336 8 chkC_6_d10336) (x2c_join _ 10344 10352 11200 (x2c_range_all (fun t => (!(pOK tl tl (t % 282) (t / 282)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 282 % 94) * 282) (x2Tab o (t / 282 / 94) (t % 282))) (x2Tab t3 (t / 282) (t % 282)))) 10344 8 chkC_6_d10344) (x2c_join _ 10352 10360 11200 (x2c_range_all (fun t => (!(pOK tl tl (t % 282) (t / 282)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 282 % 94) * 282) (x2Tab o (t / 282 / 94) (t % 282))) (x2Tab t3 (t / 282) (t % 282)))) 10352 8 chkC_6_d10352) (x2c_join _ 10360 10368 11200 (x2c_range_all (fun t => (!(pOK tl tl (t % 282) (t / 282)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 282 % 94) * 282) (x2Tab o (t / 282 / 94) (t % 282))) (x2Tab t3 (t / 282) (t % 282)))) 10360 8 chkC_6_d10360) (x2c_join _ 10368 10376 11200 (x2c_range_all (fun t => (!(pOK tl tl (t % 282) (t / 282)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 282 % 94) * 282) (x2Tab o (t / 282 / 94) (t % 282))) (x2Tab t3 (t / 282) (t % 282)))) 10368 8 chkC_6_d10368) (x2c_join _ 10376 10384 11200 (x2c_range_all (fun t => (!(pOK tl tl (t % 282) (t / 282)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 282 % 94) * 282) (x2Tab o (t / 282 / 94) (t % 282))) (x2Tab t3 (t / 282) (t % 282)))) 10376 8 chkC_6_d10376) (x2c_join _ 10384 10392 11200 (x2c_range_all (fun t => (!(pOK tl tl (t % 282) (t / 282)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 282 % 94) * 282) (x2Tab o (t / 282 / 94) (t % 282))) (x2Tab t3 (t / 282) (t % 282)))) 10384 8 chkC_6_d10384) (x2c_join _ 10392 10400 11200 (x2c_range_all (fun t => (!(pOK tl tl (t % 282) (t / 282)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 282 % 94) * 282) (x2Tab o (t / 282 / 94) (t % 282))) (x2Tab t3 (t / 282) (t % 282)))) 10392 8 chkC_6_d10392) (x2c_join _ 10400 10408 11200 (x2c_range_all (fun t => (!(pOK tl tl (t % 282) (t / 282)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 282 % 94) * 282) (x2Tab o (t / 282 / 94) (t % 282))) (x2Tab t3 (t / 282) (t % 282)))) 10400 8 chkC_6_d10400) (x2c_join _ 10408 10416 11200 (x2c_range_all (fun t => (!(pOK tl tl (t % 282) (t / 282)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 282 % 94) * 282) (x2Tab o (t / 282 / 94) (t % 282))) (x2Tab t3 (t / 282) (t % 282)))) 10408 8 chkC_6_d10408) (x2c_join _ 10416 10424 11200 (x2c_range_all (fun t => (!(pOK tl tl (t % 282) (t / 282)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 282 % 94) * 282) (x2Tab o (t / 282 / 94) (t % 282))) (x2Tab t3 (t / 282) (t % 282)))) 10416 8 chkC_6_d10416) (x2c_join _ 10424 10432 11200 (x2c_range_all (fun t => (!(pOK tl tl (t % 282) (t / 282)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 282 % 94) * 282) (x2Tab o (t / 282 / 94) (t % 282))) (x2Tab t3 (t / 282) (t % 282)))) 10424 8 chkC_6_d10424) (x2c_join _ 10432 10440 11200 (x2c_range_all (fun t => (!(pOK tl tl (t % 282) (t / 282)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 282 % 94) * 282) (x2Tab o (t / 282 / 94) (t % 282))) (x2Tab t3 (t / 282) (t % 282)))) 10432 8 chkC_6_d10432) (x2c_join _ 10440 10448 11200 (x2c_range_all (fun t => (!(pOK tl tl (t % 282) (t / 282)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 282 % 94) * 282) (x2Tab o (t / 282 / 94) (t % 282))) (x2Tab t3 (t / 282) (t % 282)))) 10440 8 chkC_6_d10440) (x2c_join _ 10448 10456 11200 (x2c_range_all (fun t => (!(pOK tl tl (t % 282) (t / 282)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 282 % 94) * 282) (x2Tab o (t / 282 / 94) (t % 282))) (x2Tab t3 (t / 282) (t % 282)))) 10448 8 chkC_6_d10448) (x2c_join _ 10456 10464 11200 (x2c_range_all (fun t => (!(pOK tl tl (t % 282) (t / 282)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 282 % 94) * 282) (x2Tab o (t / 282 / 94) (t % 282))) (x2Tab t3 (t / 282) (t % 282)))) 10456 8 chkC_6_d10456) (x2c_join _ 10464 10472 11200 (x2c_range_all (fun t => (!(pOK tl tl (t % 282) (t / 282)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 282 % 94) * 282) (x2Tab o (t / 282 / 94) (t % 282))) (x2Tab t3 (t / 282) (t % 282)))) 10464 8 chkC_6_d10464) (x2c_join _ 10472 10480 11200 (x2c_range_all (fun t => (!(pOK tl tl (t % 282) (t / 282)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 282 % 94) * 282) (x2Tab o (t / 282 / 94) (t % 282))) (x2Tab t3 (t / 282) (t % 282)))) 10472 8 chkC_6_d10472) (x2c_join _ 10480 10488 11200 (x2c_range_all (fun t => (!(pOK tl tl (t % 282) (t / 282)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 282 % 94) * 282) (x2Tab o (t / 282 / 94) (t % 282))) (x2Tab t3 (t / 282) (t % 282)))) 10480 8 chkC_6_d10480) (x2c_join _ 10488 10496 11200 (x2c_range_all (fun t => (!(pOK tl tl (t % 282) (t / 282)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 282 % 94) * 282) (x2Tab o (t / 282 / 94) (t % 282))) (x2Tab t3 (t / 282) (t % 282)))) 10488 8 chkC_6_d10488) (x2c_join _ 10496 10504 11200 (x2c_range_all (fun t => (!(pOK tl tl (t % 282) (t / 282)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 282 % 94) * 282) (x2Tab o (t / 282 / 94) (t % 282))) (x2Tab t3 (t / 282) (t % 282)))) 10496 8 chkC_6_d10496) (x2c_join _ 10504 10512 11200 (x2c_range_all (fun t => (!(pOK tl tl (t % 282) (t / 282)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 282 % 94) * 282) (x2Tab o (t / 282 / 94) (t % 282))) (x2Tab t3 (t / 282) (t % 282)))) 10504 8 chkC_6_d10504) (x2c_join _ 10512 10520 11200 (x2c_range_all (fun t => (!(pOK tl tl (t % 282) (t / 282)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 282 % 94) * 282) (x2Tab o (t / 282 / 94) (t % 282))) (x2Tab t3 (t / 282) (t % 282)))) 10512 8 chkC_6_d10512) (x2c_join _ 10520 10528 11200 (x2c_range_all (fun t => (!(pOK tl tl (t % 282) (t / 282)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 282 % 94) * 282) (x2Tab o (t / 282 / 94) (t % 282))) (x2Tab t3 (t / 282) (t % 282)))) 10520 8 chkC_6_d10520) (x2c_join _ 10528 10536 11200 (x2c_range_all (fun t => (!(pOK tl tl (t % 282) (t / 282)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 282 % 94) * 282) (x2Tab o (t / 282 / 94) (t % 282))) (x2Tab t3 (t / 282) (t % 282)))) 10528 8 chkC_6_d10528) (x2c_join _ 10536 10544 11200 (x2c_range_all (fun t => (!(pOK tl tl (t % 282) (t / 282)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 282 % 94) * 282) (x2Tab o (t / 282 / 94) (t % 282))) (x2Tab t3 (t / 282) (t % 282)))) 10536 8 chkC_6_d10536) (x2c_join _ 10544 10552 11200 (x2c_range_all (fun t => (!(pOK tl tl (t % 282) (t / 282)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 282 % 94) * 282) (x2Tab o (t / 282 / 94) (t % 282))) (x2Tab t3 (t / 282) (t % 282)))) 10544 8 chkC_6_d10544) (x2c_join _ 10552 10560 11200 (x2c_range_all (fun t => (!(pOK tl tl (t % 282) (t / 282)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 282 % 94) * 282) (x2Tab o (t / 282 / 94) (t % 282))) (x2Tab t3 (t / 282) (t % 282)))) 10552 8 chkC_6_d10552) (x2c_join _ 10560 10568 11200 (x2c_range_all (fun t => (!(pOK tl tl (t % 282) (t / 282)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 282 % 94) * 282) (x2Tab o (t / 282 / 94) (t % 282))) (x2Tab t3 (t / 282) (t % 282)))) 10560 8 chkC_6_d10560) (x2c_join _ 10568 10576 11200 (x2c_range_all (fun t => (!(pOK tl tl (t % 282) (t / 282)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 282 % 94) * 282) (x2Tab o (t / 282 / 94) (t % 282))) (x2Tab t3 (t / 282) (t % 282)))) 10568 8 chkC_6_d10568) (x2c_join _ 10576 10584 11200 (x2c_range_all (fun t => (!(pOK tl tl (t % 282) (t / 282)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 282 % 94) * 282) (x2Tab o (t / 282 / 94) (t % 282))) (x2Tab t3 (t / 282) (t % 282)))) 10576 8 chkC_6_d10576) (x2c_join _ 10584 10592 11200 (x2c_range_all (fun t => (!(pOK tl tl (t % 282) (t / 282)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 282 % 94) * 282) (x2Tab o (t / 282 / 94) (t % 282))) (x2Tab t3 (t / 282) (t % 282)))) 10584 8 chkC_6_d10584) (x2c_join _ 10592 10600 11200 (x2c_range_all (fun t => (!(pOK tl tl (t % 282) (t / 282)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 282 % 94) * 282) (x2Tab o (t / 282 / 94) (t % 282))) (x2Tab t3 (t / 282) (t % 282)))) 10592 8 chkC_6_d10592) (x2c_join _ 10600 10608 11200 (x2c_range_all (fun t => (!(pOK tl tl (t % 282) (t / 282)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 282 % 94) * 282) (x2Tab o (t / 282 / 94) (t % 282))) (x2Tab t3 (t / 282) (t % 282)))) 10600 8 chkC_6_d10600) (x2c_join _ 10608 10616 11200 (x2c_range_all (fun t => (!(pOK tl tl (t % 282) (t / 282)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 282 % 94) * 282) (x2Tab o (t / 282 / 94) (t % 282))) (x2Tab t3 (t / 282) (t % 282)))) 10608 8 chkC_6_d10608) (x2c_join _ 10616 10624 11200 (x2c_range_all (fun t => (!(pOK tl tl (t % 282) (t / 282)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 282 % 94) * 282) (x2Tab o (t / 282 / 94) (t % 282))) (x2Tab t3 (t / 282) (t % 282)))) 10616 8 chkC_6_d10616) (x2c_join _ 10624 10632 11200 (x2c_range_all (fun t => (!(pOK tl tl (t % 282) (t / 282)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 282 % 94) * 282) (x2Tab o (t / 282 / 94) (t % 282))) (x2Tab t3 (t / 282) (t % 282)))) 10624 8 chkC_6_d10624) (x2c_join _ 10632 10640 11200 (x2c_range_all (fun t => (!(pOK tl tl (t % 282) (t / 282)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 282 % 94) * 282) (x2Tab o (t / 282 / 94) (t % 282))) (x2Tab t3 (t / 282) (t % 282)))) 10632 8 chkC_6_d10632) (x2c_join _ 10640 10648 11200 (x2c_range_all (fun t => (!(pOK tl tl (t % 282) (t / 282)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 282 % 94) * 282) (x2Tab o (t / 282 / 94) (t % 282))) (x2Tab t3 (t / 282) (t % 282)))) 10640 8 chkC_6_d10640) (x2c_join _ 10648 10656 11200 (x2c_range_all (fun t => (!(pOK tl tl (t % 282) (t / 282)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 282 % 94) * 282) (x2Tab o (t / 282 / 94) (t % 282))) (x2Tab t3 (t / 282) (t % 282)))) 10648 8 chkC_6_d10648) (x2c_join _ 10656 10664 11200 (x2c_range_all (fun t => (!(pOK tl tl (t % 282) (t / 282)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 282 % 94) * 282) (x2Tab o (t / 282 / 94) (t % 282))) (x2Tab t3 (t / 282) (t % 282)))) 10656 8 chkC_6_d10656) (x2c_join _ 10664 10672 11200 (x2c_range_all (fun t => (!(pOK tl tl (t % 282) (t / 282)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 282 % 94) * 282) (x2Tab o (t / 282 / 94) (t % 282))) (x2Tab t3 (t / 282) (t % 282)))) 10664 8 chkC_6_d10664) (x2c_join _ 10672 10680 11200 (x2c_range_all (fun t => (!(pOK tl tl (t % 282) (t / 282)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 282 % 94) * 282) (x2Tab o (t / 282 / 94) (t % 282))) (x2Tab t3 (t / 282) (t % 282)))) 10672 8 chkC_6_d10672) (x2c_join _ 10680 10688 11200 (x2c_range_all (fun t => (!(pOK tl tl (t % 282) (t / 282)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 282 % 94) * 282) (x2Tab o (t / 282 / 94) (t % 282))) (x2Tab t3 (t / 282) (t % 282)))) 10680 8 chkC_6_d10680) (x2c_join _ 10688 10696 11200 (x2c_range_all (fun t => (!(pOK tl tl (t % 282) (t / 282)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 282 % 94) * 282) (x2Tab o (t / 282 / 94) (t % 282))) (x2Tab t3 (t / 282) (t % 282)))) 10688 8 chkC_6_d10688) (x2c_join _ 10696 10704 11200 (x2c_range_all (fun t => (!(pOK tl tl (t % 282) (t / 282)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 282 % 94) * 282) (x2Tab o (t / 282 / 94) (t % 282))) (x2Tab t3 (t / 282) (t % 282)))) 10696 8 chkC_6_d10696) (x2c_join _ 10704 10712 11200 (x2c_range_all (fun t => (!(pOK tl tl (t % 282) (t / 282)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 282 % 94) * 282) (x2Tab o (t / 282 / 94) (t % 282))) (x2Tab t3 (t / 282) (t % 282)))) 10704 8 chkC_6_d10704) (x2c_join _ 10712 10720 11200 (x2c_range_all (fun t => (!(pOK tl tl (t % 282) (t / 282)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 282 % 94) * 282) (x2Tab o (t / 282 / 94) (t % 282))) (x2Tab t3 (t / 282) (t % 282)))) 10712 8 chkC_6_d10712) (x2c_join _ 10720 10728 11200 (x2c_range_all (fun t => (!(pOK tl tl (t % 282) (t / 282)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 282 % 94) * 282) (x2Tab o (t / 282 / 94) (t % 282))) (x2Tab t3 (t / 282) (t % 282)))) 10720 8 chkC_6_d10720) (x2c_join _ 10728 10736 11200 (x2c_range_all (fun t => (!(pOK tl tl (t % 282) (t / 282)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 282 % 94) * 282) (x2Tab o (t / 282 / 94) (t % 282))) (x2Tab t3 (t / 282) (t % 282)))) 10728 8 chkC_6_d10728) (x2c_join _ 10736 10744 11200 (x2c_range_all (fun t => (!(pOK tl tl (t % 282) (t / 282)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 282 % 94) * 282) (x2Tab o (t / 282 / 94) (t % 282))) (x2Tab t3 (t / 282) (t % 282)))) 10736 8 chkC_6_d10736) (x2c_join _ 10744 10752 11200 (x2c_range_all (fun t => (!(pOK tl tl (t % 282) (t / 282)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 282 % 94) * 282) (x2Tab o (t / 282 / 94) (t % 282))) (x2Tab t3 (t / 282) (t % 282)))) 10744 8 chkC_6_d10744) (x2c_join _ 10752 10760 11200 (x2c_range_all (fun t => (!(pOK tl tl (t % 282) (t / 282)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 282 % 94) * 282) (x2Tab o (t / 282 / 94) (t % 282))) (x2Tab t3 (t / 282) (t % 282)))) 10752 8 chkC_6_d10752) (x2c_join _ 10760 10768 11200 (x2c_range_all (fun t => (!(pOK tl tl (t % 282) (t / 282)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 282 % 94) * 282) (x2Tab o (t / 282 / 94) (t % 282))) (x2Tab t3 (t / 282) (t % 282)))) 10760 8 chkC_6_d10760) (x2c_join _ 10768 10776 11200 (x2c_range_all (fun t => (!(pOK tl tl (t % 282) (t / 282)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 282 % 94) * 282) (x2Tab o (t / 282 / 94) (t % 282))) (x2Tab t3 (t / 282) (t % 282)))) 10768 8 chkC_6_d10768) (x2c_join _ 10776 10784 11200 (x2c_range_all (fun t => (!(pOK tl tl (t % 282) (t / 282)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 282 % 94) * 282) (x2Tab o (t / 282 / 94) (t % 282))) (x2Tab t3 (t / 282) (t % 282)))) 10776 8 chkC_6_d10776) (x2c_join _ 10784 10792 11200 (x2c_range_all (fun t => (!(pOK tl tl (t % 282) (t / 282)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 282 % 94) * 282) (x2Tab o (t / 282 / 94) (t % 282))) (x2Tab t3 (t / 282) (t % 282)))) 10784 8 chkC_6_d10784) (x2c_join _ 10792 10800 11200 (x2c_range_all (fun t => (!(pOK tl tl (t % 282) (t / 282)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 282 % 94) * 282) (x2Tab o (t / 282 / 94) (t % 282))) (x2Tab t3 (t / 282) (t % 282)))) 10792 8 chkC_6_d10792) (x2c_join _ 10800 10808 11200 (x2c_range_all (fun t => (!(pOK tl tl (t % 282) (t / 282)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 282 % 94) * 282) (x2Tab o (t / 282 / 94) (t % 282))) (x2Tab t3 (t / 282) (t % 282)))) 10800 8 chkC_6_d10800) (x2c_join _ 10808 10816 11200 (x2c_range_all (fun t => (!(pOK tl tl (t % 282) (t / 282)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 282 % 94) * 282) (x2Tab o (t / 282 / 94) (t % 282))) (x2Tab t3 (t / 282) (t % 282)))) 10808 8 chkC_6_d10808) (x2c_join _ 10816 10824 11200 (x2c_range_all (fun t => (!(pOK tl tl (t % 282) (t / 282)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 282 % 94) * 282) (x2Tab o (t / 282 / 94) (t % 282))) (x2Tab t3 (t / 282) (t % 282)))) 10816 8 chkC_6_d10816) (x2c_join _ 10824 10832 11200 (x2c_range_all (fun t => (!(pOK tl tl (t % 282) (t / 282)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 282 % 94) * 282) (x2Tab o (t / 282 / 94) (t % 282))) (x2Tab t3 (t / 282) (t % 282)))) 10824 8 chkC_6_d10824) (x2c_join _ 10832 10840 11200 (x2c_range_all (fun t => (!(pOK tl tl (t % 282) (t / 282)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 282 % 94) * 282) (x2Tab o (t / 282 / 94) (t % 282))) (x2Tab t3 (t / 282) (t % 282)))) 10832 8 chkC_6_d10832) (x2c_join _ 10840 10848 11200 (x2c_range_all (fun t => (!(pOK tl tl (t % 282) (t / 282)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 282 % 94) * 282) (x2Tab o (t / 282 / 94) (t % 282))) (x2Tab t3 (t / 282) (t % 282)))) 10840 8 chkC_6_d10840) (x2c_join _ 10848 10856 11200 (x2c_range_all (fun t => (!(pOK tl tl (t % 282) (t / 282)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 282 % 94) * 282) (x2Tab o (t / 282 / 94) (t % 282))) (x2Tab t3 (t / 282) (t % 282)))) 10848 8 chkC_6_d10848) (x2c_join _ 10856 10864 11200 (x2c_range_all (fun t => (!(pOK tl tl (t % 282) (t / 282)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 282 % 94) * 282) (x2Tab o (t / 282 / 94) (t % 282))) (x2Tab t3 (t / 282) (t % 282)))) 10856 8 chkC_6_d10856) (x2c_join _ 10864 10872 11200 (x2c_range_all (fun t => (!(pOK tl tl (t % 282) (t / 282)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 282 % 94) * 282) (x2Tab o (t / 282 / 94) (t % 282))) (x2Tab t3 (t / 282) (t % 282)))) 10864 8 chkC_6_d10864) (x2c_join _ 10872 10880 11200 (x2c_range_all (fun t => (!(pOK tl tl (t % 282) (t / 282)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 282 % 94) * 282) (x2Tab o (t / 282 / 94) (t % 282))) (x2Tab t3 (t / 282) (t % 282)))) 10872 8 chkC_6_d10872) (x2c_join _ 10880 10888 11200 (x2c_range_all (fun t => (!(pOK tl tl (t % 282) (t / 282)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 282 % 94) * 282) (x2Tab o (t / 282 / 94) (t % 282))) (x2Tab t3 (t / 282) (t % 282)))) 10880 8 chkC_6_d10880) (x2c_join _ 10888 10896 11200 (x2c_range_all (fun t => (!(pOK tl tl (t % 282) (t / 282)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 282 % 94) * 282) (x2Tab o (t / 282 / 94) (t % 282))) (x2Tab t3 (t / 282) (t % 282)))) 10888 8 chkC_6_d10888) (x2c_join _ 10896 10904 11200 (x2c_range_all (fun t => (!(pOK tl tl (t % 282) (t / 282)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 282 % 94) * 282) (x2Tab o (t / 282 / 94) (t % 282))) (x2Tab t3 (t / 282) (t % 282)))) 10896 8 chkC_6_d10896) (x2c_join _ 10904 10912 11200 (x2c_range_all (fun t => (!(pOK tl tl (t % 282) (t / 282)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 282 % 94) * 282) (x2Tab o (t / 282 / 94) (t % 282))) (x2Tab t3 (t / 282) (t % 282)))) 10904 8 chkC_6_d10904) (x2c_join _ 10912 10920 11200 (x2c_range_all (fun t => (!(pOK tl tl (t % 282) (t / 282)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 282 % 94) * 282) (x2Tab o (t / 282 / 94) (t % 282))) (x2Tab t3 (t / 282) (t % 282)))) 10912 8 chkC_6_d10912) (x2c_join _ 10920 10928 11200 (x2c_range_all (fun t => (!(pOK tl tl (t % 282) (t / 282)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 282 % 94) * 282) (x2Tab o (t / 282 / 94) (t % 282))) (x2Tab t3 (t / 282) (t % 282)))) 10920 8 chkC_6_d10920) (x2c_join _ 10928 10936 11200 (x2c_range_all (fun t => (!(pOK tl tl (t % 282) (t / 282)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 282 % 94) * 282) (x2Tab o (t / 282 / 94) (t % 282))) (x2Tab t3 (t / 282) (t % 282)))) 10928 8 chkC_6_d10928) (x2c_join _ 10936 10944 11200 (x2c_range_all (fun t => (!(pOK tl tl (t % 282) (t / 282)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 282 % 94) * 282) (x2Tab o (t / 282 / 94) (t % 282))) (x2Tab t3 (t / 282) (t % 282)))) 10936 8 chkC_6_d10936) (x2c_join _ 10944 10952 11200 (x2c_range_all (fun t => (!(pOK tl tl (t % 282) (t / 282)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 282 % 94) * 282) (x2Tab o (t / 282 / 94) (t % 282))) (x2Tab t3 (t / 282) (t % 282)))) 10944 8 chkC_6_d10944) (x2c_join _ 10952 10960 11200 (x2c_range_all (fun t => (!(pOK tl tl (t % 282) (t / 282)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 282 % 94) * 282) (x2Tab o (t / 282 / 94) (t % 282))) (x2Tab t3 (t / 282) (t % 282)))) 10952 8 chkC_6_d10952) (x2c_join _ 10960 10968 11200 (x2c_range_all (fun t => (!(pOK tl tl (t % 282) (t / 282)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 282 % 94) * 282) (x2Tab o (t / 282 / 94) (t % 282))) (x2Tab t3 (t / 282) (t % 282)))) 10960 8 chkC_6_d10960) (x2c_join _ 10968 10976 11200 (x2c_range_all (fun t => (!(pOK tl tl (t % 282) (t / 282)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 282 % 94) * 282) (x2Tab o (t / 282 / 94) (t % 282))) (x2Tab t3 (t / 282) (t % 282)))) 10968 8 chkC_6_d10968) (x2c_join _ 10976 10984 11200 (x2c_range_all (fun t => (!(pOK tl tl (t % 282) (t / 282)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 282 % 94) * 282) (x2Tab o (t / 282 / 94) (t % 282))) (x2Tab t3 (t / 282) (t % 282)))) 10976 8 chkC_6_d10976) (x2c_join _ 10984 10992 11200 (x2c_range_all (fun t => (!(pOK tl tl (t % 282) (t / 282)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 282 % 94) * 282) (x2Tab o (t / 282 / 94) (t % 282))) (x2Tab t3 (t / 282) (t % 282)))) 10984 8 chkC_6_d10984) (x2c_join _ 10992 11000 11200 (x2c_range_all (fun t => (!(pOK tl tl (t % 282) (t / 282)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 282 % 94) * 282) (x2Tab o (t / 282 / 94) (t % 282))) (x2Tab t3 (t / 282) (t % 282)))) 10992 8 chkC_6_d10992) (x2c_join _ 11000 11008 11200 (x2c_range_all (fun t => (!(pOK tl tl (t % 282) (t / 282)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 282 % 94) * 282) (x2Tab o (t / 282 / 94) (t % 282))) (x2Tab t3 (t / 282) (t % 282)))) 11000 8 chkC_6_d11000) (x2c_join _ 11008 11016 11200 (x2c_range_all (fun t => (!(pOK tl tl (t % 282) (t / 282)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 282 % 94) * 282) (x2Tab o (t / 282 / 94) (t % 282))) (x2Tab t3 (t / 282) (t % 282)))) 11008 8 chkC_6_d11008) (x2c_join _ 11016 11024 11200 (x2c_range_all (fun t => (!(pOK tl tl (t % 282) (t / 282)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 282 % 94) * 282) (x2Tab o (t / 282 / 94) (t % 282))) (x2Tab t3 (t / 282) (t % 282)))) 11016 8 chkC_6_d11016) (x2c_join _ 11024 11032 11200 (x2c_range_all (fun t => (!(pOK tl tl (t % 282) (t / 282)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 282 % 94) * 282) (x2Tab o (t / 282 / 94) (t % 282))) (x2Tab t3 (t / 282) (t % 282)))) 11024 8 chkC_6_d11024) (x2c_join _ 11032 11040 11200 (x2c_range_all (fun t => (!(pOK tl tl (t % 282) (t / 282)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 282 % 94) * 282) (x2Tab o (t / 282 / 94) (t % 282))) (x2Tab t3 (t / 282) (t % 282)))) 11032 8 chkC_6_d11032) (x2c_join _ 11040 11048 11200 (x2c_range_all (fun t => (!(pOK tl tl (t % 282) (t / 282)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 282 % 94) * 282) (x2Tab o (t / 282 / 94) (t % 282))) (x2Tab t3 (t / 282) (t % 282)))) 11040 8 chkC_6_d11040) (x2c_join _ 11048 11056 11200 (x2c_range_all (fun t => (!(pOK tl tl (t % 282) (t / 282)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 282 % 94) * 282) (x2Tab o (t / 282 / 94) (t % 282))) (x2Tab t3 (t / 282) (t % 282)))) 11048 8 chkC_6_d11048) (x2c_join _ 11056 11064 11200 (x2c_range_all (fun t => (!(pOK tl tl (t % 282) (t / 282)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 282 % 94) * 282) (x2Tab o (t / 282 / 94) (t % 282))) (x2Tab t3 (t / 282) (t % 282)))) 11056 8 chkC_6_d11056) (x2c_join _ 11064 11072 11200 (x2c_range_all (fun t => (!(pOK tl tl (t % 282) (t / 282)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 282 % 94) * 282) (x2Tab o (t / 282 / 94) (t % 282))) (x2Tab t3 (t / 282) (t % 282)))) 11064 8 chkC_6_d11064) (x2c_join _ 11072 11080 11200 (x2c_range_all (fun t => (!(pOK tl tl (t % 282) (t / 282)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 282 % 94) * 282) (x2Tab o (t / 282 / 94) (t % 282))) (x2Tab t3 (t / 282) (t % 282)))) 11072 8 chkC_6_d11072) (x2c_join _ 11080 11088 11200 (x2c_range_all (fun t => (!(pOK tl tl (t % 282) (t / 282)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 282 % 94) * 282) (x2Tab o (t / 282 / 94) (t % 282))) (x2Tab t3 (t / 282) (t % 282)))) 11080 8 chkC_6_d11080) (x2c_join _ 11088 11096 11200 (x2c_range_all (fun t => (!(pOK tl tl (t % 282) (t / 282)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 282 % 94) * 282) (x2Tab o (t / 282 / 94) (t % 282))) (x2Tab t3 (t / 282) (t % 282)))) 11088 8 chkC_6_d11088) (x2c_join _ 11096 11104 11200 (x2c_range_all (fun t => (!(pOK tl tl (t % 282) (t / 282)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 282 % 94) * 282) (x2Tab o (t / 282 / 94) (t % 282))) (x2Tab t3 (t / 282) (t % 282)))) 11096 8 chkC_6_d11096) (x2c_join _ 11104 11112 11200 (x2c_range_all (fun t => (!(pOK tl tl (t % 282) (t / 282)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 282 % 94) * 282) (x2Tab o (t / 282 / 94) (t % 282))) (x2Tab t3 (t / 282) (t % 282)))) 11104 8 chkC_6_d11104) (x2c_join _ 11112 11120 11200 (x2c_range_all (fun t => (!(pOK tl tl (t % 282) (t / 282)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 282 % 94) * 282) (x2Tab o (t / 282 / 94) (t % 282))) (x2Tab t3 (t / 282) (t % 282)))) 11112 8 chkC_6_d11112) (x2c_join _ 11120 11128 11200 (x2c_range_all (fun t => (!(pOK tl tl (t % 282) (t / 282)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 282 % 94) * 282) (x2Tab o (t / 282 / 94) (t % 282))) (x2Tab t3 (t / 282) (t % 282)))) 11120 8 chkC_6_d11120) (x2c_join _ 11128 11136 11200 (x2c_range_all (fun t => (!(pOK tl tl (t % 282) (t / 282)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 282 % 94) * 282) (x2Tab o (t / 282 / 94) (t % 282))) (x2Tab t3 (t / 282) (t % 282)))) 11128 8 chkC_6_d11128) (x2c_join _ 11136 11144 11200 (x2c_range_all (fun t => (!(pOK tl tl (t % 282) (t / 282)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 282 % 94) * 282) (x2Tab o (t / 282 / 94) (t % 282))) (x2Tab t3 (t / 282) (t % 282)))) 11136 8 chkC_6_d11136) (x2c_join _ 11144 11152 11200 (x2c_range_all (fun t => (!(pOK tl tl (t % 282) (t / 282)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 282 % 94) * 282) (x2Tab o (t / 282 / 94) (t % 282))) (x2Tab t3 (t / 282) (t % 282)))) 11144 8 chkC_6_d11144) (x2c_join _ 11152 11160 11200 (x2c_range_all (fun t => (!(pOK tl tl (t % 282) (t / 282)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 282 % 94) * 282) (x2Tab o (t / 282 / 94) (t % 282))) (x2Tab t3 (t / 282) (t % 282)))) 11152 8 chkC_6_d11152) (x2c_join _ 11160 11168 11200 (x2c_range_all (fun t => (!(pOK tl tl (t % 282) (t / 282)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 282 % 94) * 282) (x2Tab o (t / 282 / 94) (t % 282))) (x2Tab t3 (t / 282) (t % 282)))) 11160 8 chkC_6_d11160) (x2c_join _ 11168 11176 11200 (x2c_range_all (fun t => (!(pOK tl tl (t % 282) (t / 282)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 282 % 94) * 282) (x2Tab o (t / 282 / 94) (t % 282))) (x2Tab t3 (t / 282) (t % 282)))) 11168 8 chkC_6_d11168) (x2c_join _ 11176 11184 11200 (x2c_range_all (fun t => (!(pOK tl tl (t % 282) (t / 282)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 282 % 94) * 282) (x2Tab o (t / 282 / 94) (t % 282))) (x2Tab t3 (t / 282) (t % 282)))) 11176 8 chkC_6_d11176) (x2c_join _ 11184 11192 11200 (x2c_range_all (fun t => (!(pOK tl tl (t % 282) (t / 282)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 282 % 94) * 282) (x2Tab o (t / 282 / 94) (t % 282))) (x2Tab t3 (t / 282) (t % 282)))) 11184 8 chkC_6_d11184) (x2c_range_all (fun t => (!(pOK tl tl (t % 282) (t / 282)) || slotCheck 384 282 513 cs (runOf 384 282 ((t / 282 % 94) * 282) (x2Tab o (t / 282 / 94) (t % 282))) (x2Tab t3 (t / 282) (t % 282)))) 11192 8 chkC_6_d11192))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))


end ThreeCopyQutritWerner.X2.CoreS1g
