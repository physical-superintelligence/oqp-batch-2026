module

public import ThreeCopyQutritWerner.CertificateX2CoreS1gO
public import ThreeCopyQutritWerner.CertificateX2Trans
public import ThreeCopyQutritWerner.CertificateX2CoreBatchGen
public import ThreeCopyQutritWerner.CertificateX2CoreBatchFlat

@[expose] public section


/-! Batched core S1g: axis-1 stage, one output per declaration, flat indices 768..845. -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option exponentiation.threshold 1000000

namespace ThreeCopyQutritWerner.X2.CoreS1g
open ThreeCopyQutritWerner ThreeCopyQutritWerner.X2

theorem chkB_8_d768 : (List.range' 768 1).all (fun t => natAxpySp 384 26508 31 (transS1Tab.getD (t % 282) []) (h.getD (t / 282) []) (x2Tab o (t / 282) (t % 282))) = true := by
  decide +kernel

theorem chkB_8_d769 : (List.range' 769 1).all (fun t => natAxpySp 384 26508 31 (transS1Tab.getD (t % 282) []) (h.getD (t / 282) []) (x2Tab o (t / 282) (t % 282))) = true := by
  decide +kernel

theorem chkB_8_d770 : (List.range' 770 1).all (fun t => natAxpySp 384 26508 31 (transS1Tab.getD (t % 282) []) (h.getD (t / 282) []) (x2Tab o (t / 282) (t % 282))) = true := by
  decide +kernel

theorem chkB_8_d771 : (List.range' 771 1).all (fun t => natAxpySp 384 26508 31 (transS1Tab.getD (t % 282) []) (h.getD (t / 282) []) (x2Tab o (t / 282) (t % 282))) = true := by
  decide +kernel

theorem chkB_8_d772 : (List.range' 772 1).all (fun t => natAxpySp 384 26508 31 (transS1Tab.getD (t % 282) []) (h.getD (t / 282) []) (x2Tab o (t / 282) (t % 282))) = true := by
  decide +kernel

theorem chkB_8_d773 : (List.range' 773 1).all (fun t => natAxpySp 384 26508 31 (transS1Tab.getD (t % 282) []) (h.getD (t / 282) []) (x2Tab o (t / 282) (t % 282))) = true := by
  decide +kernel

theorem chkB_8_d774 : (List.range' 774 1).all (fun t => natAxpySp 384 26508 31 (transS1Tab.getD (t % 282) []) (h.getD (t / 282) []) (x2Tab o (t / 282) (t % 282))) = true := by
  decide +kernel

theorem chkB_8_d775 : (List.range' 775 1).all (fun t => natAxpySp 384 26508 31 (transS1Tab.getD (t % 282) []) (h.getD (t / 282) []) (x2Tab o (t / 282) (t % 282))) = true := by
  decide +kernel

theorem chkB_8_d776 : (List.range' 776 1).all (fun t => natAxpySp 384 26508 31 (transS1Tab.getD (t % 282) []) (h.getD (t / 282) []) (x2Tab o (t / 282) (t % 282))) = true := by
  decide +kernel

theorem chkB_8_d777 : (List.range' 777 1).all (fun t => natAxpySp 384 26508 31 (transS1Tab.getD (t % 282) []) (h.getD (t / 282) []) (x2Tab o (t / 282) (t % 282))) = true := by
  decide +kernel

theorem chkB_8_d778 : (List.range' 778 1).all (fun t => natAxpySp 384 26508 31 (transS1Tab.getD (t % 282) []) (h.getD (t / 282) []) (x2Tab o (t / 282) (t % 282))) = true := by
  decide +kernel

theorem chkB_8_d779 : (List.range' 779 1).all (fun t => natAxpySp 384 26508 31 (transS1Tab.getD (t % 282) []) (h.getD (t / 282) []) (x2Tab o (t / 282) (t % 282))) = true := by
  decide +kernel

theorem chkB_8_d780 : (List.range' 780 1).all (fun t => natAxpySp 384 26508 31 (transS1Tab.getD (t % 282) []) (h.getD (t / 282) []) (x2Tab o (t / 282) (t % 282))) = true := by
  decide +kernel

theorem chkB_8_d781 : (List.range' 781 1).all (fun t => natAxpySp 384 26508 31 (transS1Tab.getD (t % 282) []) (h.getD (t / 282) []) (x2Tab o (t / 282) (t % 282))) = true := by
  decide +kernel

theorem chkB_8_d782 : (List.range' 782 1).all (fun t => natAxpySp 384 26508 31 (transS1Tab.getD (t % 282) []) (h.getD (t / 282) []) (x2Tab o (t / 282) (t % 282))) = true := by
  decide +kernel

theorem chkB_8_d783 : (List.range' 783 1).all (fun t => natAxpySp 384 26508 31 (transS1Tab.getD (t % 282) []) (h.getD (t / 282) []) (x2Tab o (t / 282) (t % 282))) = true := by
  decide +kernel

theorem chkB_8_d784 : (List.range' 784 1).all (fun t => natAxpySp 384 26508 31 (transS1Tab.getD (t % 282) []) (h.getD (t / 282) []) (x2Tab o (t / 282) (t % 282))) = true := by
  decide +kernel

theorem chkB_8_d785 : (List.range' 785 1).all (fun t => natAxpySp 384 26508 31 (transS1Tab.getD (t % 282) []) (h.getD (t / 282) []) (x2Tab o (t / 282) (t % 282))) = true := by
  decide +kernel

theorem chkB_8_d786 : (List.range' 786 1).all (fun t => natAxpySp 384 26508 31 (transS1Tab.getD (t % 282) []) (h.getD (t / 282) []) (x2Tab o (t / 282) (t % 282))) = true := by
  decide +kernel

theorem chkB_8_d787 : (List.range' 787 1).all (fun t => natAxpySp 384 26508 31 (transS1Tab.getD (t % 282) []) (h.getD (t / 282) []) (x2Tab o (t / 282) (t % 282))) = true := by
  decide +kernel

theorem chkB_8_d788 : (List.range' 788 1).all (fun t => natAxpySp 384 26508 31 (transS1Tab.getD (t % 282) []) (h.getD (t / 282) []) (x2Tab o (t / 282) (t % 282))) = true := by
  decide +kernel

theorem chkB_8_d789 : (List.range' 789 1).all (fun t => natAxpySp 384 26508 31 (transS1Tab.getD (t % 282) []) (h.getD (t / 282) []) (x2Tab o (t / 282) (t % 282))) = true := by
  decide +kernel

theorem chkB_8_d790 : (List.range' 790 1).all (fun t => natAxpySp 384 26508 31 (transS1Tab.getD (t % 282) []) (h.getD (t / 282) []) (x2Tab o (t / 282) (t % 282))) = true := by
  decide +kernel

theorem chkB_8_d791 : (List.range' 791 1).all (fun t => natAxpySp 384 26508 31 (transS1Tab.getD (t % 282) []) (h.getD (t / 282) []) (x2Tab o (t / 282) (t % 282))) = true := by
  decide +kernel

theorem chkB_8_d792 : (List.range' 792 1).all (fun t => natAxpySp 384 26508 31 (transS1Tab.getD (t % 282) []) (h.getD (t / 282) []) (x2Tab o (t / 282) (t % 282))) = true := by
  decide +kernel

theorem chkB_8_d793 : (List.range' 793 1).all (fun t => natAxpySp 384 26508 31 (transS1Tab.getD (t % 282) []) (h.getD (t / 282) []) (x2Tab o (t / 282) (t % 282))) = true := by
  decide +kernel

theorem chkB_8_d794 : (List.range' 794 1).all (fun t => natAxpySp 384 26508 31 (transS1Tab.getD (t % 282) []) (h.getD (t / 282) []) (x2Tab o (t / 282) (t % 282))) = true := by
  decide +kernel

theorem chkB_8_d795 : (List.range' 795 1).all (fun t => natAxpySp 384 26508 31 (transS1Tab.getD (t % 282) []) (h.getD (t / 282) []) (x2Tab o (t / 282) (t % 282))) = true := by
  decide +kernel

theorem chkB_8_d796 : (List.range' 796 1).all (fun t => natAxpySp 384 26508 31 (transS1Tab.getD (t % 282) []) (h.getD (t / 282) []) (x2Tab o (t / 282) (t % 282))) = true := by
  decide +kernel

theorem chkB_8_d797 : (List.range' 797 1).all (fun t => natAxpySp 384 26508 31 (transS1Tab.getD (t % 282) []) (h.getD (t / 282) []) (x2Tab o (t / 282) (t % 282))) = true := by
  decide +kernel

theorem chkB_8_d798 : (List.range' 798 1).all (fun t => natAxpySp 384 26508 31 (transS1Tab.getD (t % 282) []) (h.getD (t / 282) []) (x2Tab o (t / 282) (t % 282))) = true := by
  decide +kernel

theorem chkB_8_d799 : (List.range' 799 1).all (fun t => natAxpySp 384 26508 31 (transS1Tab.getD (t % 282) []) (h.getD (t / 282) []) (x2Tab o (t / 282) (t % 282))) = true := by
  decide +kernel

theorem chkB_8_d800 : (List.range' 800 1).all (fun t => natAxpySp 384 26508 31 (transS1Tab.getD (t % 282) []) (h.getD (t / 282) []) (x2Tab o (t / 282) (t % 282))) = true := by
  decide +kernel

theorem chkB_8_d801 : (List.range' 801 1).all (fun t => natAxpySp 384 26508 31 (transS1Tab.getD (t % 282) []) (h.getD (t / 282) []) (x2Tab o (t / 282) (t % 282))) = true := by
  decide +kernel

theorem chkB_8_d802 : (List.range' 802 1).all (fun t => natAxpySp 384 26508 31 (transS1Tab.getD (t % 282) []) (h.getD (t / 282) []) (x2Tab o (t / 282) (t % 282))) = true := by
  decide +kernel

theorem chkB_8_d803 : (List.range' 803 1).all (fun t => natAxpySp 384 26508 31 (transS1Tab.getD (t % 282) []) (h.getD (t / 282) []) (x2Tab o (t / 282) (t % 282))) = true := by
  decide +kernel

theorem chkB_8_d804 : (List.range' 804 1).all (fun t => natAxpySp 384 26508 31 (transS1Tab.getD (t % 282) []) (h.getD (t / 282) []) (x2Tab o (t / 282) (t % 282))) = true := by
  decide +kernel

theorem chkB_8_d805 : (List.range' 805 1).all (fun t => natAxpySp 384 26508 31 (transS1Tab.getD (t % 282) []) (h.getD (t / 282) []) (x2Tab o (t / 282) (t % 282))) = true := by
  decide +kernel

theorem chkB_8_d806 : (List.range' 806 1).all (fun t => natAxpySp 384 26508 31 (transS1Tab.getD (t % 282) []) (h.getD (t / 282) []) (x2Tab o (t / 282) (t % 282))) = true := by
  decide +kernel

theorem chkB_8_d807 : (List.range' 807 1).all (fun t => natAxpySp 384 26508 31 (transS1Tab.getD (t % 282) []) (h.getD (t / 282) []) (x2Tab o (t / 282) (t % 282))) = true := by
  decide +kernel

theorem chkB_8_d808 : (List.range' 808 1).all (fun t => natAxpySp 384 26508 31 (transS1Tab.getD (t % 282) []) (h.getD (t / 282) []) (x2Tab o (t / 282) (t % 282))) = true := by
  decide +kernel

theorem chkB_8_d809 : (List.range' 809 1).all (fun t => natAxpySp 384 26508 31 (transS1Tab.getD (t % 282) []) (h.getD (t / 282) []) (x2Tab o (t / 282) (t % 282))) = true := by
  decide +kernel

theorem chkB_8_d810 : (List.range' 810 1).all (fun t => natAxpySp 384 26508 31 (transS1Tab.getD (t % 282) []) (h.getD (t / 282) []) (x2Tab o (t / 282) (t % 282))) = true := by
  decide +kernel

theorem chkB_8_d811 : (List.range' 811 1).all (fun t => natAxpySp 384 26508 31 (transS1Tab.getD (t % 282) []) (h.getD (t / 282) []) (x2Tab o (t / 282) (t % 282))) = true := by
  decide +kernel

theorem chkB_8_d812 : (List.range' 812 1).all (fun t => natAxpySp 384 26508 31 (transS1Tab.getD (t % 282) []) (h.getD (t / 282) []) (x2Tab o (t / 282) (t % 282))) = true := by
  decide +kernel

theorem chkB_8_d813 : (List.range' 813 1).all (fun t => natAxpySp 384 26508 31 (transS1Tab.getD (t % 282) []) (h.getD (t / 282) []) (x2Tab o (t / 282) (t % 282))) = true := by
  decide +kernel

theorem chkB_8_d814 : (List.range' 814 1).all (fun t => natAxpySp 384 26508 31 (transS1Tab.getD (t % 282) []) (h.getD (t / 282) []) (x2Tab o (t / 282) (t % 282))) = true := by
  decide +kernel

theorem chkB_8_d815 : (List.range' 815 1).all (fun t => natAxpySp 384 26508 31 (transS1Tab.getD (t % 282) []) (h.getD (t / 282) []) (x2Tab o (t / 282) (t % 282))) = true := by
  decide +kernel

theorem chkB_8_d816 : (List.range' 816 1).all (fun t => natAxpySp 384 26508 31 (transS1Tab.getD (t % 282) []) (h.getD (t / 282) []) (x2Tab o (t / 282) (t % 282))) = true := by
  decide +kernel

theorem chkB_8_d817 : (List.range' 817 1).all (fun t => natAxpySp 384 26508 31 (transS1Tab.getD (t % 282) []) (h.getD (t / 282) []) (x2Tab o (t / 282) (t % 282))) = true := by
  decide +kernel

theorem chkB_8_d818 : (List.range' 818 1).all (fun t => natAxpySp 384 26508 31 (transS1Tab.getD (t % 282) []) (h.getD (t / 282) []) (x2Tab o (t / 282) (t % 282))) = true := by
  decide +kernel

theorem chkB_8_d819 : (List.range' 819 1).all (fun t => natAxpySp 384 26508 31 (transS1Tab.getD (t % 282) []) (h.getD (t / 282) []) (x2Tab o (t / 282) (t % 282))) = true := by
  decide +kernel

theorem chkB_8_d820 : (List.range' 820 1).all (fun t => natAxpySp 384 26508 31 (transS1Tab.getD (t % 282) []) (h.getD (t / 282) []) (x2Tab o (t / 282) (t % 282))) = true := by
  decide +kernel

theorem chkB_8_d821 : (List.range' 821 1).all (fun t => natAxpySp 384 26508 31 (transS1Tab.getD (t % 282) []) (h.getD (t / 282) []) (x2Tab o (t / 282) (t % 282))) = true := by
  decide +kernel

theorem chkB_8_d822 : (List.range' 822 1).all (fun t => natAxpySp 384 26508 31 (transS1Tab.getD (t % 282) []) (h.getD (t / 282) []) (x2Tab o (t / 282) (t % 282))) = true := by
  decide +kernel

theorem chkB_8_d823 : (List.range' 823 1).all (fun t => natAxpySp 384 26508 31 (transS1Tab.getD (t % 282) []) (h.getD (t / 282) []) (x2Tab o (t / 282) (t % 282))) = true := by
  decide +kernel

theorem chkB_8_d824 : (List.range' 824 1).all (fun t => natAxpySp 384 26508 31 (transS1Tab.getD (t % 282) []) (h.getD (t / 282) []) (x2Tab o (t / 282) (t % 282))) = true := by
  decide +kernel

theorem chkB_8_d825 : (List.range' 825 1).all (fun t => natAxpySp 384 26508 31 (transS1Tab.getD (t % 282) []) (h.getD (t / 282) []) (x2Tab o (t / 282) (t % 282))) = true := by
  decide +kernel

theorem chkB_8_d826 : (List.range' 826 1).all (fun t => natAxpySp 384 26508 31 (transS1Tab.getD (t % 282) []) (h.getD (t / 282) []) (x2Tab o (t / 282) (t % 282))) = true := by
  decide +kernel

theorem chkB_8_d827 : (List.range' 827 1).all (fun t => natAxpySp 384 26508 31 (transS1Tab.getD (t % 282) []) (h.getD (t / 282) []) (x2Tab o (t / 282) (t % 282))) = true := by
  decide +kernel

theorem chkB_8_d828 : (List.range' 828 1).all (fun t => natAxpySp 384 26508 31 (transS1Tab.getD (t % 282) []) (h.getD (t / 282) []) (x2Tab o (t / 282) (t % 282))) = true := by
  decide +kernel

theorem chkB_8_d829 : (List.range' 829 1).all (fun t => natAxpySp 384 26508 31 (transS1Tab.getD (t % 282) []) (h.getD (t / 282) []) (x2Tab o (t / 282) (t % 282))) = true := by
  decide +kernel

theorem chkB_8_d830 : (List.range' 830 1).all (fun t => natAxpySp 384 26508 31 (transS1Tab.getD (t % 282) []) (h.getD (t / 282) []) (x2Tab o (t / 282) (t % 282))) = true := by
  decide +kernel

theorem chkB_8_d831 : (List.range' 831 1).all (fun t => natAxpySp 384 26508 31 (transS1Tab.getD (t % 282) []) (h.getD (t / 282) []) (x2Tab o (t / 282) (t % 282))) = true := by
  decide +kernel

theorem chkB_8_d832 : (List.range' 832 1).all (fun t => natAxpySp 384 26508 31 (transS1Tab.getD (t % 282) []) (h.getD (t / 282) []) (x2Tab o (t / 282) (t % 282))) = true := by
  decide +kernel

theorem chkB_8_d833 : (List.range' 833 1).all (fun t => natAxpySp 384 26508 31 (transS1Tab.getD (t % 282) []) (h.getD (t / 282) []) (x2Tab o (t / 282) (t % 282))) = true := by
  decide +kernel

theorem chkB_8_d834 : (List.range' 834 1).all (fun t => natAxpySp 384 26508 31 (transS1Tab.getD (t % 282) []) (h.getD (t / 282) []) (x2Tab o (t / 282) (t % 282))) = true := by
  decide +kernel

theorem chkB_8_d835 : (List.range' 835 1).all (fun t => natAxpySp 384 26508 31 (transS1Tab.getD (t % 282) []) (h.getD (t / 282) []) (x2Tab o (t / 282) (t % 282))) = true := by
  decide +kernel

theorem chkB_8_d836 : (List.range' 836 1).all (fun t => natAxpySp 384 26508 31 (transS1Tab.getD (t % 282) []) (h.getD (t / 282) []) (x2Tab o (t / 282) (t % 282))) = true := by
  decide +kernel

theorem chkB_8_d837 : (List.range' 837 1).all (fun t => natAxpySp 384 26508 31 (transS1Tab.getD (t % 282) []) (h.getD (t / 282) []) (x2Tab o (t / 282) (t % 282))) = true := by
  decide +kernel

theorem chkB_8_d838 : (List.range' 838 1).all (fun t => natAxpySp 384 26508 31 (transS1Tab.getD (t % 282) []) (h.getD (t / 282) []) (x2Tab o (t / 282) (t % 282))) = true := by
  decide +kernel

theorem chkB_8_d839 : (List.range' 839 1).all (fun t => natAxpySp 384 26508 31 (transS1Tab.getD (t % 282) []) (h.getD (t / 282) []) (x2Tab o (t / 282) (t % 282))) = true := by
  decide +kernel

theorem chkB_8_d840 : (List.range' 840 1).all (fun t => natAxpySp 384 26508 31 (transS1Tab.getD (t % 282) []) (h.getD (t / 282) []) (x2Tab o (t / 282) (t % 282))) = true := by
  decide +kernel

theorem chkB_8_d841 : (List.range' 841 1).all (fun t => natAxpySp 384 26508 31 (transS1Tab.getD (t % 282) []) (h.getD (t / 282) []) (x2Tab o (t / 282) (t % 282))) = true := by
  decide +kernel

theorem chkB_8_d842 : (List.range' 842 1).all (fun t => natAxpySp 384 26508 31 (transS1Tab.getD (t % 282) []) (h.getD (t / 282) []) (x2Tab o (t / 282) (t % 282))) = true := by
  decide +kernel

theorem chkB_8_d843 : (List.range' 843 1).all (fun t => natAxpySp 384 26508 31 (transS1Tab.getD (t % 282) []) (h.getD (t / 282) []) (x2Tab o (t / 282) (t % 282))) = true := by
  decide +kernel

theorem chkB_8_d844 : (List.range' 844 1).all (fun t => natAxpySp 384 26508 31 (transS1Tab.getD (t % 282) []) (h.getD (t / 282) []) (x2Tab o (t / 282) (t % 282))) = true := by
  decide +kernel

theorem chkB_8_d845 : (List.range' 845 1).all (fun t => natAxpySp 384 26508 31 (transS1Tab.getD (t % 282) []) (h.getD (t / 282) []) (x2Tab o (t / 282) (t % 282))) = true := by
  decide +kernel

theorem chkB_8 : ∀ t, 768 ≤ t → t < 846 → (natAxpySp 384 26508 31 (transS1Tab.getD (t % 282) []) (h.getD (t / 282) []) (x2Tab o (t / 282) (t % 282))) = true := by
  exact (x2c_join _ 768 769 846 (x2c_range_all (fun t => natAxpySp 384 26508 31 (transS1Tab.getD (t % 282) []) (h.getD (t / 282) []) (x2Tab o (t / 282) (t % 282))) 768 1 chkB_8_d768) (x2c_join _ 769 770 846 (x2c_range_all (fun t => natAxpySp 384 26508 31 (transS1Tab.getD (t % 282) []) (h.getD (t / 282) []) (x2Tab o (t / 282) (t % 282))) 769 1 chkB_8_d769) (x2c_join _ 770 771 846 (x2c_range_all (fun t => natAxpySp 384 26508 31 (transS1Tab.getD (t % 282) []) (h.getD (t / 282) []) (x2Tab o (t / 282) (t % 282))) 770 1 chkB_8_d770) (x2c_join _ 771 772 846 (x2c_range_all (fun t => natAxpySp 384 26508 31 (transS1Tab.getD (t % 282) []) (h.getD (t / 282) []) (x2Tab o (t / 282) (t % 282))) 771 1 chkB_8_d771) (x2c_join _ 772 773 846 (x2c_range_all (fun t => natAxpySp 384 26508 31 (transS1Tab.getD (t % 282) []) (h.getD (t / 282) []) (x2Tab o (t / 282) (t % 282))) 772 1 chkB_8_d772) (x2c_join _ 773 774 846 (x2c_range_all (fun t => natAxpySp 384 26508 31 (transS1Tab.getD (t % 282) []) (h.getD (t / 282) []) (x2Tab o (t / 282) (t % 282))) 773 1 chkB_8_d773) (x2c_join _ 774 775 846 (x2c_range_all (fun t => natAxpySp 384 26508 31 (transS1Tab.getD (t % 282) []) (h.getD (t / 282) []) (x2Tab o (t / 282) (t % 282))) 774 1 chkB_8_d774) (x2c_join _ 775 776 846 (x2c_range_all (fun t => natAxpySp 384 26508 31 (transS1Tab.getD (t % 282) []) (h.getD (t / 282) []) (x2Tab o (t / 282) (t % 282))) 775 1 chkB_8_d775) (x2c_join _ 776 777 846 (x2c_range_all (fun t => natAxpySp 384 26508 31 (transS1Tab.getD (t % 282) []) (h.getD (t / 282) []) (x2Tab o (t / 282) (t % 282))) 776 1 chkB_8_d776) (x2c_join _ 777 778 846 (x2c_range_all (fun t => natAxpySp 384 26508 31 (transS1Tab.getD (t % 282) []) (h.getD (t / 282) []) (x2Tab o (t / 282) (t % 282))) 777 1 chkB_8_d777) (x2c_join _ 778 779 846 (x2c_range_all (fun t => natAxpySp 384 26508 31 (transS1Tab.getD (t % 282) []) (h.getD (t / 282) []) (x2Tab o (t / 282) (t % 282))) 778 1 chkB_8_d778) (x2c_join _ 779 780 846 (x2c_range_all (fun t => natAxpySp 384 26508 31 (transS1Tab.getD (t % 282) []) (h.getD (t / 282) []) (x2Tab o (t / 282) (t % 282))) 779 1 chkB_8_d779) (x2c_join _ 780 781 846 (x2c_range_all (fun t => natAxpySp 384 26508 31 (transS1Tab.getD (t % 282) []) (h.getD (t / 282) []) (x2Tab o (t / 282) (t % 282))) 780 1 chkB_8_d780) (x2c_join _ 781 782 846 (x2c_range_all (fun t => natAxpySp 384 26508 31 (transS1Tab.getD (t % 282) []) (h.getD (t / 282) []) (x2Tab o (t / 282) (t % 282))) 781 1 chkB_8_d781) (x2c_join _ 782 783 846 (x2c_range_all (fun t => natAxpySp 384 26508 31 (transS1Tab.getD (t % 282) []) (h.getD (t / 282) []) (x2Tab o (t / 282) (t % 282))) 782 1 chkB_8_d782) (x2c_join _ 783 784 846 (x2c_range_all (fun t => natAxpySp 384 26508 31 (transS1Tab.getD (t % 282) []) (h.getD (t / 282) []) (x2Tab o (t / 282) (t % 282))) 783 1 chkB_8_d783) (x2c_join _ 784 785 846 (x2c_range_all (fun t => natAxpySp 384 26508 31 (transS1Tab.getD (t % 282) []) (h.getD (t / 282) []) (x2Tab o (t / 282) (t % 282))) 784 1 chkB_8_d784) (x2c_join _ 785 786 846 (x2c_range_all (fun t => natAxpySp 384 26508 31 (transS1Tab.getD (t % 282) []) (h.getD (t / 282) []) (x2Tab o (t / 282) (t % 282))) 785 1 chkB_8_d785) (x2c_join _ 786 787 846 (x2c_range_all (fun t => natAxpySp 384 26508 31 (transS1Tab.getD (t % 282) []) (h.getD (t / 282) []) (x2Tab o (t / 282) (t % 282))) 786 1 chkB_8_d786) (x2c_join _ 787 788 846 (x2c_range_all (fun t => natAxpySp 384 26508 31 (transS1Tab.getD (t % 282) []) (h.getD (t / 282) []) (x2Tab o (t / 282) (t % 282))) 787 1 chkB_8_d787) (x2c_join _ 788 789 846 (x2c_range_all (fun t => natAxpySp 384 26508 31 (transS1Tab.getD (t % 282) []) (h.getD (t / 282) []) (x2Tab o (t / 282) (t % 282))) 788 1 chkB_8_d788) (x2c_join _ 789 790 846 (x2c_range_all (fun t => natAxpySp 384 26508 31 (transS1Tab.getD (t % 282) []) (h.getD (t / 282) []) (x2Tab o (t / 282) (t % 282))) 789 1 chkB_8_d789) (x2c_join _ 790 791 846 (x2c_range_all (fun t => natAxpySp 384 26508 31 (transS1Tab.getD (t % 282) []) (h.getD (t / 282) []) (x2Tab o (t / 282) (t % 282))) 790 1 chkB_8_d790) (x2c_join _ 791 792 846 (x2c_range_all (fun t => natAxpySp 384 26508 31 (transS1Tab.getD (t % 282) []) (h.getD (t / 282) []) (x2Tab o (t / 282) (t % 282))) 791 1 chkB_8_d791) (x2c_join _ 792 793 846 (x2c_range_all (fun t => natAxpySp 384 26508 31 (transS1Tab.getD (t % 282) []) (h.getD (t / 282) []) (x2Tab o (t / 282) (t % 282))) 792 1 chkB_8_d792) (x2c_join _ 793 794 846 (x2c_range_all (fun t => natAxpySp 384 26508 31 (transS1Tab.getD (t % 282) []) (h.getD (t / 282) []) (x2Tab o (t / 282) (t % 282))) 793 1 chkB_8_d793) (x2c_join _ 794 795 846 (x2c_range_all (fun t => natAxpySp 384 26508 31 (transS1Tab.getD (t % 282) []) (h.getD (t / 282) []) (x2Tab o (t / 282) (t % 282))) 794 1 chkB_8_d794) (x2c_join _ 795 796 846 (x2c_range_all (fun t => natAxpySp 384 26508 31 (transS1Tab.getD (t % 282) []) (h.getD (t / 282) []) (x2Tab o (t / 282) (t % 282))) 795 1 chkB_8_d795) (x2c_join _ 796 797 846 (x2c_range_all (fun t => natAxpySp 384 26508 31 (transS1Tab.getD (t % 282) []) (h.getD (t / 282) []) (x2Tab o (t / 282) (t % 282))) 796 1 chkB_8_d796) (x2c_join _ 797 798 846 (x2c_range_all (fun t => natAxpySp 384 26508 31 (transS1Tab.getD (t % 282) []) (h.getD (t / 282) []) (x2Tab o (t / 282) (t % 282))) 797 1 chkB_8_d797) (x2c_join _ 798 799 846 (x2c_range_all (fun t => natAxpySp 384 26508 31 (transS1Tab.getD (t % 282) []) (h.getD (t / 282) []) (x2Tab o (t / 282) (t % 282))) 798 1 chkB_8_d798) (x2c_join _ 799 800 846 (x2c_range_all (fun t => natAxpySp 384 26508 31 (transS1Tab.getD (t % 282) []) (h.getD (t / 282) []) (x2Tab o (t / 282) (t % 282))) 799 1 chkB_8_d799) (x2c_join _ 800 801 846 (x2c_range_all (fun t => natAxpySp 384 26508 31 (transS1Tab.getD (t % 282) []) (h.getD (t / 282) []) (x2Tab o (t / 282) (t % 282))) 800 1 chkB_8_d800) (x2c_join _ 801 802 846 (x2c_range_all (fun t => natAxpySp 384 26508 31 (transS1Tab.getD (t % 282) []) (h.getD (t / 282) []) (x2Tab o (t / 282) (t % 282))) 801 1 chkB_8_d801) (x2c_join _ 802 803 846 (x2c_range_all (fun t => natAxpySp 384 26508 31 (transS1Tab.getD (t % 282) []) (h.getD (t / 282) []) (x2Tab o (t / 282) (t % 282))) 802 1 chkB_8_d802) (x2c_join _ 803 804 846 (x2c_range_all (fun t => natAxpySp 384 26508 31 (transS1Tab.getD (t % 282) []) (h.getD (t / 282) []) (x2Tab o (t / 282) (t % 282))) 803 1 chkB_8_d803) (x2c_join _ 804 805 846 (x2c_range_all (fun t => natAxpySp 384 26508 31 (transS1Tab.getD (t % 282) []) (h.getD (t / 282) []) (x2Tab o (t / 282) (t % 282))) 804 1 chkB_8_d804) (x2c_join _ 805 806 846 (x2c_range_all (fun t => natAxpySp 384 26508 31 (transS1Tab.getD (t % 282) []) (h.getD (t / 282) []) (x2Tab o (t / 282) (t % 282))) 805 1 chkB_8_d805) (x2c_join _ 806 807 846 (x2c_range_all (fun t => natAxpySp 384 26508 31 (transS1Tab.getD (t % 282) []) (h.getD (t / 282) []) (x2Tab o (t / 282) (t % 282))) 806 1 chkB_8_d806) (x2c_join _ 807 808 846 (x2c_range_all (fun t => natAxpySp 384 26508 31 (transS1Tab.getD (t % 282) []) (h.getD (t / 282) []) (x2Tab o (t / 282) (t % 282))) 807 1 chkB_8_d807) (x2c_join _ 808 809 846 (x2c_range_all (fun t => natAxpySp 384 26508 31 (transS1Tab.getD (t % 282) []) (h.getD (t / 282) []) (x2Tab o (t / 282) (t % 282))) 808 1 chkB_8_d808) (x2c_join _ 809 810 846 (x2c_range_all (fun t => natAxpySp 384 26508 31 (transS1Tab.getD (t % 282) []) (h.getD (t / 282) []) (x2Tab o (t / 282) (t % 282))) 809 1 chkB_8_d809) (x2c_join _ 810 811 846 (x2c_range_all (fun t => natAxpySp 384 26508 31 (transS1Tab.getD (t % 282) []) (h.getD (t / 282) []) (x2Tab o (t / 282) (t % 282))) 810 1 chkB_8_d810) (x2c_join _ 811 812 846 (x2c_range_all (fun t => natAxpySp 384 26508 31 (transS1Tab.getD (t % 282) []) (h.getD (t / 282) []) (x2Tab o (t / 282) (t % 282))) 811 1 chkB_8_d811) (x2c_join _ 812 813 846 (x2c_range_all (fun t => natAxpySp 384 26508 31 (transS1Tab.getD (t % 282) []) (h.getD (t / 282) []) (x2Tab o (t / 282) (t % 282))) 812 1 chkB_8_d812) (x2c_join _ 813 814 846 (x2c_range_all (fun t => natAxpySp 384 26508 31 (transS1Tab.getD (t % 282) []) (h.getD (t / 282) []) (x2Tab o (t / 282) (t % 282))) 813 1 chkB_8_d813) (x2c_join _ 814 815 846 (x2c_range_all (fun t => natAxpySp 384 26508 31 (transS1Tab.getD (t % 282) []) (h.getD (t / 282) []) (x2Tab o (t / 282) (t % 282))) 814 1 chkB_8_d814) (x2c_join _ 815 816 846 (x2c_range_all (fun t => natAxpySp 384 26508 31 (transS1Tab.getD (t % 282) []) (h.getD (t / 282) []) (x2Tab o (t / 282) (t % 282))) 815 1 chkB_8_d815) (x2c_join _ 816 817 846 (x2c_range_all (fun t => natAxpySp 384 26508 31 (transS1Tab.getD (t % 282) []) (h.getD (t / 282) []) (x2Tab o (t / 282) (t % 282))) 816 1 chkB_8_d816) (x2c_join _ 817 818 846 (x2c_range_all (fun t => natAxpySp 384 26508 31 (transS1Tab.getD (t % 282) []) (h.getD (t / 282) []) (x2Tab o (t / 282) (t % 282))) 817 1 chkB_8_d817) (x2c_join _ 818 819 846 (x2c_range_all (fun t => natAxpySp 384 26508 31 (transS1Tab.getD (t % 282) []) (h.getD (t / 282) []) (x2Tab o (t / 282) (t % 282))) 818 1 chkB_8_d818) (x2c_join _ 819 820 846 (x2c_range_all (fun t => natAxpySp 384 26508 31 (transS1Tab.getD (t % 282) []) (h.getD (t / 282) []) (x2Tab o (t / 282) (t % 282))) 819 1 chkB_8_d819) (x2c_join _ 820 821 846 (x2c_range_all (fun t => natAxpySp 384 26508 31 (transS1Tab.getD (t % 282) []) (h.getD (t / 282) []) (x2Tab o (t / 282) (t % 282))) 820 1 chkB_8_d820) (x2c_join _ 821 822 846 (x2c_range_all (fun t => natAxpySp 384 26508 31 (transS1Tab.getD (t % 282) []) (h.getD (t / 282) []) (x2Tab o (t / 282) (t % 282))) 821 1 chkB_8_d821) (x2c_join _ 822 823 846 (x2c_range_all (fun t => natAxpySp 384 26508 31 (transS1Tab.getD (t % 282) []) (h.getD (t / 282) []) (x2Tab o (t / 282) (t % 282))) 822 1 chkB_8_d822) (x2c_join _ 823 824 846 (x2c_range_all (fun t => natAxpySp 384 26508 31 (transS1Tab.getD (t % 282) []) (h.getD (t / 282) []) (x2Tab o (t / 282) (t % 282))) 823 1 chkB_8_d823) (x2c_join _ 824 825 846 (x2c_range_all (fun t => natAxpySp 384 26508 31 (transS1Tab.getD (t % 282) []) (h.getD (t / 282) []) (x2Tab o (t / 282) (t % 282))) 824 1 chkB_8_d824) (x2c_join _ 825 826 846 (x2c_range_all (fun t => natAxpySp 384 26508 31 (transS1Tab.getD (t % 282) []) (h.getD (t / 282) []) (x2Tab o (t / 282) (t % 282))) 825 1 chkB_8_d825) (x2c_join _ 826 827 846 (x2c_range_all (fun t => natAxpySp 384 26508 31 (transS1Tab.getD (t % 282) []) (h.getD (t / 282) []) (x2Tab o (t / 282) (t % 282))) 826 1 chkB_8_d826) (x2c_join _ 827 828 846 (x2c_range_all (fun t => natAxpySp 384 26508 31 (transS1Tab.getD (t % 282) []) (h.getD (t / 282) []) (x2Tab o (t / 282) (t % 282))) 827 1 chkB_8_d827) (x2c_join _ 828 829 846 (x2c_range_all (fun t => natAxpySp 384 26508 31 (transS1Tab.getD (t % 282) []) (h.getD (t / 282) []) (x2Tab o (t / 282) (t % 282))) 828 1 chkB_8_d828) (x2c_join _ 829 830 846 (x2c_range_all (fun t => natAxpySp 384 26508 31 (transS1Tab.getD (t % 282) []) (h.getD (t / 282) []) (x2Tab o (t / 282) (t % 282))) 829 1 chkB_8_d829) (x2c_join _ 830 831 846 (x2c_range_all (fun t => natAxpySp 384 26508 31 (transS1Tab.getD (t % 282) []) (h.getD (t / 282) []) (x2Tab o (t / 282) (t % 282))) 830 1 chkB_8_d830) (x2c_join _ 831 832 846 (x2c_range_all (fun t => natAxpySp 384 26508 31 (transS1Tab.getD (t % 282) []) (h.getD (t / 282) []) (x2Tab o (t / 282) (t % 282))) 831 1 chkB_8_d831) (x2c_join _ 832 833 846 (x2c_range_all (fun t => natAxpySp 384 26508 31 (transS1Tab.getD (t % 282) []) (h.getD (t / 282) []) (x2Tab o (t / 282) (t % 282))) 832 1 chkB_8_d832) (x2c_join _ 833 834 846 (x2c_range_all (fun t => natAxpySp 384 26508 31 (transS1Tab.getD (t % 282) []) (h.getD (t / 282) []) (x2Tab o (t / 282) (t % 282))) 833 1 chkB_8_d833) (x2c_join _ 834 835 846 (x2c_range_all (fun t => natAxpySp 384 26508 31 (transS1Tab.getD (t % 282) []) (h.getD (t / 282) []) (x2Tab o (t / 282) (t % 282))) 834 1 chkB_8_d834) (x2c_join _ 835 836 846 (x2c_range_all (fun t => natAxpySp 384 26508 31 (transS1Tab.getD (t % 282) []) (h.getD (t / 282) []) (x2Tab o (t / 282) (t % 282))) 835 1 chkB_8_d835) (x2c_join _ 836 837 846 (x2c_range_all (fun t => natAxpySp 384 26508 31 (transS1Tab.getD (t % 282) []) (h.getD (t / 282) []) (x2Tab o (t / 282) (t % 282))) 836 1 chkB_8_d836) (x2c_join _ 837 838 846 (x2c_range_all (fun t => natAxpySp 384 26508 31 (transS1Tab.getD (t % 282) []) (h.getD (t / 282) []) (x2Tab o (t / 282) (t % 282))) 837 1 chkB_8_d837) (x2c_join _ 838 839 846 (x2c_range_all (fun t => natAxpySp 384 26508 31 (transS1Tab.getD (t % 282) []) (h.getD (t / 282) []) (x2Tab o (t / 282) (t % 282))) 838 1 chkB_8_d838) (x2c_join _ 839 840 846 (x2c_range_all (fun t => natAxpySp 384 26508 31 (transS1Tab.getD (t % 282) []) (h.getD (t / 282) []) (x2Tab o (t / 282) (t % 282))) 839 1 chkB_8_d839) (x2c_join _ 840 841 846 (x2c_range_all (fun t => natAxpySp 384 26508 31 (transS1Tab.getD (t % 282) []) (h.getD (t / 282) []) (x2Tab o (t / 282) (t % 282))) 840 1 chkB_8_d840) (x2c_join _ 841 842 846 (x2c_range_all (fun t => natAxpySp 384 26508 31 (transS1Tab.getD (t % 282) []) (h.getD (t / 282) []) (x2Tab o (t / 282) (t % 282))) 841 1 chkB_8_d841) (x2c_join _ 842 843 846 (x2c_range_all (fun t => natAxpySp 384 26508 31 (transS1Tab.getD (t % 282) []) (h.getD (t / 282) []) (x2Tab o (t / 282) (t % 282))) 842 1 chkB_8_d842) (x2c_join _ 843 844 846 (x2c_range_all (fun t => natAxpySp 384 26508 31 (transS1Tab.getD (t % 282) []) (h.getD (t / 282) []) (x2Tab o (t / 282) (t % 282))) 843 1 chkB_8_d843) (x2c_join _ 844 845 846 (x2c_range_all (fun t => natAxpySp 384 26508 31 (transS1Tab.getD (t % 282) []) (h.getD (t / 282) []) (x2Tab o (t / 282) (t % 282))) 844 1 chkB_8_d844) (x2c_range_all (fun t => natAxpySp 384 26508 31 (transS1Tab.getD (t % 282) []) (h.getD (t / 282) []) (x2Tab o (t / 282) (t % 282))) 845 1 chkB_8_d845))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))


end ThreeCopyQutritWerner.X2.CoreS1g
