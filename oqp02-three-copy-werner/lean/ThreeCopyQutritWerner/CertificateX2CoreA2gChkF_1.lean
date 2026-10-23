module

public import ThreeCopyQutritWerner.CertificateX2CoreA2gF0
public import ThreeCopyQutritWerner.CertificateX2CoreBatchFlat

@[expose] public section


/-! Batched core A2g: slot bounds of the input, flat indices 576..692. -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option exponentiation.threshold 1000000

namespace ThreeCopyQutritWerner.X2.CoreA2g
open ThreeCopyQutritWerner ThreeCopyQutritWerner.X2

theorem chkF_1_d576 : (List.range' 576 6).all (fun t => slotBoundCheck 384 228 21714 (x2Tab f0 (t / 231) (t % 231))) = true := by
  decide +kernel

theorem chkF_1_d582 : (List.range' 582 6).all (fun t => slotBoundCheck 384 228 21714 (x2Tab f0 (t / 231) (t % 231))) = true := by
  decide +kernel

theorem chkF_1_d588 : (List.range' 588 6).all (fun t => slotBoundCheck 384 228 21714 (x2Tab f0 (t / 231) (t % 231))) = true := by
  decide +kernel

theorem chkF_1_d594 : (List.range' 594 6).all (fun t => slotBoundCheck 384 228 21714 (x2Tab f0 (t / 231) (t % 231))) = true := by
  decide +kernel

theorem chkF_1_d600 : (List.range' 600 6).all (fun t => slotBoundCheck 384 228 21714 (x2Tab f0 (t / 231) (t % 231))) = true := by
  decide +kernel

theorem chkF_1_d606 : (List.range' 606 6).all (fun t => slotBoundCheck 384 228 21714 (x2Tab f0 (t / 231) (t % 231))) = true := by
  decide +kernel

theorem chkF_1_d612 : (List.range' 612 6).all (fun t => slotBoundCheck 384 228 21714 (x2Tab f0 (t / 231) (t % 231))) = true := by
  decide +kernel

theorem chkF_1_d618 : (List.range' 618 6).all (fun t => slotBoundCheck 384 228 21714 (x2Tab f0 (t / 231) (t % 231))) = true := by
  decide +kernel

theorem chkF_1_d624 : (List.range' 624 6).all (fun t => slotBoundCheck 384 228 21714 (x2Tab f0 (t / 231) (t % 231))) = true := by
  decide +kernel

theorem chkF_1_d630 : (List.range' 630 6).all (fun t => slotBoundCheck 384 228 21714 (x2Tab f0 (t / 231) (t % 231))) = true := by
  decide +kernel

theorem chkF_1_d636 : (List.range' 636 6).all (fun t => slotBoundCheck 384 228 21714 (x2Tab f0 (t / 231) (t % 231))) = true := by
  decide +kernel

theorem chkF_1_d642 : (List.range' 642 6).all (fun t => slotBoundCheck 384 228 21714 (x2Tab f0 (t / 231) (t % 231))) = true := by
  decide +kernel

theorem chkF_1_d648 : (List.range' 648 6).all (fun t => slotBoundCheck 384 228 21714 (x2Tab f0 (t / 231) (t % 231))) = true := by
  decide +kernel

theorem chkF_1_d654 : (List.range' 654 6).all (fun t => slotBoundCheck 384 228 21714 (x2Tab f0 (t / 231) (t % 231))) = true := by
  decide +kernel

theorem chkF_1_d660 : (List.range' 660 6).all (fun t => slotBoundCheck 384 228 21714 (x2Tab f0 (t / 231) (t % 231))) = true := by
  decide +kernel

theorem chkF_1_d666 : (List.range' 666 6).all (fun t => slotBoundCheck 384 228 21714 (x2Tab f0 (t / 231) (t % 231))) = true := by
  decide +kernel

theorem chkF_1_d672 : (List.range' 672 6).all (fun t => slotBoundCheck 384 228 21714 (x2Tab f0 (t / 231) (t % 231))) = true := by
  decide +kernel

theorem chkF_1_d678 : (List.range' 678 6).all (fun t => slotBoundCheck 384 228 21714 (x2Tab f0 (t / 231) (t % 231))) = true := by
  decide +kernel

theorem chkF_1_d684 : (List.range' 684 6).all (fun t => slotBoundCheck 384 228 21714 (x2Tab f0 (t / 231) (t % 231))) = true := by
  decide +kernel

theorem chkF_1_d690 : (List.range' 690 3).all (fun t => slotBoundCheck 384 228 21714 (x2Tab f0 (t / 231) (t % 231))) = true := by
  decide +kernel

theorem chkF_1 : ∀ t, 576 ≤ t → t < 693 → (slotBoundCheck 384 228 21714 (x2Tab f0 (t / 231) (t % 231))) = true := by
  exact (x2c_join _ 576 582 693 (x2c_range_all (fun t => slotBoundCheck 384 228 21714 (x2Tab f0 (t / 231) (t % 231))) 576 6 chkF_1_d576) (x2c_join _ 582 588 693 (x2c_range_all (fun t => slotBoundCheck 384 228 21714 (x2Tab f0 (t / 231) (t % 231))) 582 6 chkF_1_d582) (x2c_join _ 588 594 693 (x2c_range_all (fun t => slotBoundCheck 384 228 21714 (x2Tab f0 (t / 231) (t % 231))) 588 6 chkF_1_d588) (x2c_join _ 594 600 693 (x2c_range_all (fun t => slotBoundCheck 384 228 21714 (x2Tab f0 (t / 231) (t % 231))) 594 6 chkF_1_d594) (x2c_join _ 600 606 693 (x2c_range_all (fun t => slotBoundCheck 384 228 21714 (x2Tab f0 (t / 231) (t % 231))) 600 6 chkF_1_d600) (x2c_join _ 606 612 693 (x2c_range_all (fun t => slotBoundCheck 384 228 21714 (x2Tab f0 (t / 231) (t % 231))) 606 6 chkF_1_d606) (x2c_join _ 612 618 693 (x2c_range_all (fun t => slotBoundCheck 384 228 21714 (x2Tab f0 (t / 231) (t % 231))) 612 6 chkF_1_d612) (x2c_join _ 618 624 693 (x2c_range_all (fun t => slotBoundCheck 384 228 21714 (x2Tab f0 (t / 231) (t % 231))) 618 6 chkF_1_d618) (x2c_join _ 624 630 693 (x2c_range_all (fun t => slotBoundCheck 384 228 21714 (x2Tab f0 (t / 231) (t % 231))) 624 6 chkF_1_d624) (x2c_join _ 630 636 693 (x2c_range_all (fun t => slotBoundCheck 384 228 21714 (x2Tab f0 (t / 231) (t % 231))) 630 6 chkF_1_d630) (x2c_join _ 636 642 693 (x2c_range_all (fun t => slotBoundCheck 384 228 21714 (x2Tab f0 (t / 231) (t % 231))) 636 6 chkF_1_d636) (x2c_join _ 642 648 693 (x2c_range_all (fun t => slotBoundCheck 384 228 21714 (x2Tab f0 (t / 231) (t % 231))) 642 6 chkF_1_d642) (x2c_join _ 648 654 693 (x2c_range_all (fun t => slotBoundCheck 384 228 21714 (x2Tab f0 (t / 231) (t % 231))) 648 6 chkF_1_d648) (x2c_join _ 654 660 693 (x2c_range_all (fun t => slotBoundCheck 384 228 21714 (x2Tab f0 (t / 231) (t % 231))) 654 6 chkF_1_d654) (x2c_join _ 660 666 693 (x2c_range_all (fun t => slotBoundCheck 384 228 21714 (x2Tab f0 (t / 231) (t % 231))) 660 6 chkF_1_d660) (x2c_join _ 666 672 693 (x2c_range_all (fun t => slotBoundCheck 384 228 21714 (x2Tab f0 (t / 231) (t % 231))) 666 6 chkF_1_d666) (x2c_join _ 672 678 693 (x2c_range_all (fun t => slotBoundCheck 384 228 21714 (x2Tab f0 (t / 231) (t % 231))) 672 6 chkF_1_d672) (x2c_join _ 678 684 693 (x2c_range_all (fun t => slotBoundCheck 384 228 21714 (x2Tab f0 (t / 231) (t % 231))) 678 6 chkF_1_d678) (x2c_join _ 684 690 693 (x2c_range_all (fun t => slotBoundCheck 384 228 21714 (x2Tab f0 (t / 231) (t % 231))) 684 6 chkF_1_d684) (x2c_range_all (fun t => slotBoundCheck 384 228 21714 (x2Tab f0 (t / 231) (t % 231))) 690 3 chkF_1_d690))))))))))))))))))))


end ThreeCopyQutritWerner.X2.CoreA2g
