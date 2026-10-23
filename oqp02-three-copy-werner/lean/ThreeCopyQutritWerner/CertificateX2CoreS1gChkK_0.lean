module

public import ThreeCopyQutritWerner.CertificateX2CoreS1gCs
public import ThreeCopyQutritWerner.CertificateX2Trans
public import ThreeCopyQutritWerner.CertificateX2CoreBatchGen
public import ThreeCopyQutritWerner.CertificateX2CoreBatchFlat

@[expose] public section


/-! Batched core S1g: packed columns of the axis-0 matrix, by rows, flat indices 0..512. -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option exponentiation.threshold 1000000

namespace ThreeCopyQutritWerner.X2.CoreS1g
open ThreeCopyQutritWerner ThreeCopyQutritWerner.X2

theorem chkK_0_d0 : (List.range' 0 16).all (fun t => colsRowOK 384 31 cs (r0exp.getD t []) t) = true := by
  decide +kernel

theorem chkK_0_d16 : (List.range' 16 16).all (fun t => colsRowOK 384 31 cs (r0exp.getD t []) t) = true := by
  decide +kernel

theorem chkK_0_d32 : (List.range' 32 16).all (fun t => colsRowOK 384 31 cs (r0exp.getD t []) t) = true := by
  decide +kernel

theorem chkK_0_d48 : (List.range' 48 16).all (fun t => colsRowOK 384 31 cs (r0exp.getD t []) t) = true := by
  decide +kernel

theorem chkK_0_d64 : (List.range' 64 16).all (fun t => colsRowOK 384 31 cs (r0exp.getD t []) t) = true := by
  decide +kernel

theorem chkK_0_d80 : (List.range' 80 16).all (fun t => colsRowOK 384 31 cs (r0exp.getD t []) t) = true := by
  decide +kernel

theorem chkK_0_d96 : (List.range' 96 16).all (fun t => colsRowOK 384 31 cs (r0exp.getD t []) t) = true := by
  decide +kernel

theorem chkK_0_d112 : (List.range' 112 16).all (fun t => colsRowOK 384 31 cs (r0exp.getD t []) t) = true := by
  decide +kernel

theorem chkK_0_d128 : (List.range' 128 16).all (fun t => colsRowOK 384 31 cs (r0exp.getD t []) t) = true := by
  decide +kernel

theorem chkK_0_d144 : (List.range' 144 16).all (fun t => colsRowOK 384 31 cs (r0exp.getD t []) t) = true := by
  decide +kernel

theorem chkK_0_d160 : (List.range' 160 16).all (fun t => colsRowOK 384 31 cs (r0exp.getD t []) t) = true := by
  decide +kernel

theorem chkK_0_d176 : (List.range' 176 16).all (fun t => colsRowOK 384 31 cs (r0exp.getD t []) t) = true := by
  decide +kernel

theorem chkK_0_d192 : (List.range' 192 16).all (fun t => colsRowOK 384 31 cs (r0exp.getD t []) t) = true := by
  decide +kernel

theorem chkK_0_d208 : (List.range' 208 16).all (fun t => colsRowOK 384 31 cs (r0exp.getD t []) t) = true := by
  decide +kernel

theorem chkK_0_d224 : (List.range' 224 16).all (fun t => colsRowOK 384 31 cs (r0exp.getD t []) t) = true := by
  decide +kernel

theorem chkK_0_d240 : (List.range' 240 16).all (fun t => colsRowOK 384 31 cs (r0exp.getD t []) t) = true := by
  decide +kernel

theorem chkK_0_d256 : (List.range' 256 16).all (fun t => colsRowOK 384 31 cs (r0exp.getD t []) t) = true := by
  decide +kernel

theorem chkK_0_d272 : (List.range' 272 16).all (fun t => colsRowOK 384 31 cs (r0exp.getD t []) t) = true := by
  decide +kernel

theorem chkK_0_d288 : (List.range' 288 16).all (fun t => colsRowOK 384 31 cs (r0exp.getD t []) t) = true := by
  decide +kernel

theorem chkK_0_d304 : (List.range' 304 16).all (fun t => colsRowOK 384 31 cs (r0exp.getD t []) t) = true := by
  decide +kernel

theorem chkK_0_d320 : (List.range' 320 16).all (fun t => colsRowOK 384 31 cs (r0exp.getD t []) t) = true := by
  decide +kernel

theorem chkK_0_d336 : (List.range' 336 16).all (fun t => colsRowOK 384 31 cs (r0exp.getD t []) t) = true := by
  decide +kernel

theorem chkK_0_d352 : (List.range' 352 16).all (fun t => colsRowOK 384 31 cs (r0exp.getD t []) t) = true := by
  decide +kernel

theorem chkK_0_d368 : (List.range' 368 16).all (fun t => colsRowOK 384 31 cs (r0exp.getD t []) t) = true := by
  decide +kernel

theorem chkK_0_d384 : (List.range' 384 16).all (fun t => colsRowOK 384 31 cs (r0exp.getD t []) t) = true := by
  decide +kernel

theorem chkK_0_d400 : (List.range' 400 16).all (fun t => colsRowOK 384 31 cs (r0exp.getD t []) t) = true := by
  decide +kernel

theorem chkK_0_d416 : (List.range' 416 16).all (fun t => colsRowOK 384 31 cs (r0exp.getD t []) t) = true := by
  decide +kernel

theorem chkK_0_d432 : (List.range' 432 16).all (fun t => colsRowOK 384 31 cs (r0exp.getD t []) t) = true := by
  decide +kernel

theorem chkK_0_d448 : (List.range' 448 16).all (fun t => colsRowOK 384 31 cs (r0exp.getD t []) t) = true := by
  decide +kernel

theorem chkK_0_d464 : (List.range' 464 16).all (fun t => colsRowOK 384 31 cs (r0exp.getD t []) t) = true := by
  decide +kernel

theorem chkK_0_d480 : (List.range' 480 16).all (fun t => colsRowOK 384 31 cs (r0exp.getD t []) t) = true := by
  decide +kernel

theorem chkK_0_d496 : (List.range' 496 16).all (fun t => colsRowOK 384 31 cs (r0exp.getD t []) t) = true := by
  decide +kernel

theorem chkK_0_d512 : (List.range' 512 1).all (fun t => colsRowOK 384 31 cs (r0exp.getD t []) t) = true := by
  decide +kernel

theorem chkK_0 : ∀ t, 0 ≤ t → t < 513 → (colsRowOK 384 31 cs (r0exp.getD t []) t) = true := by
  exact (x2c_join _ 0 16 513 (x2c_range_all (fun t => colsRowOK 384 31 cs (r0exp.getD t []) t) 0 16 chkK_0_d0) (x2c_join _ 16 32 513 (x2c_range_all (fun t => colsRowOK 384 31 cs (r0exp.getD t []) t) 16 16 chkK_0_d16) (x2c_join _ 32 48 513 (x2c_range_all (fun t => colsRowOK 384 31 cs (r0exp.getD t []) t) 32 16 chkK_0_d32) (x2c_join _ 48 64 513 (x2c_range_all (fun t => colsRowOK 384 31 cs (r0exp.getD t []) t) 48 16 chkK_0_d48) (x2c_join _ 64 80 513 (x2c_range_all (fun t => colsRowOK 384 31 cs (r0exp.getD t []) t) 64 16 chkK_0_d64) (x2c_join _ 80 96 513 (x2c_range_all (fun t => colsRowOK 384 31 cs (r0exp.getD t []) t) 80 16 chkK_0_d80) (x2c_join _ 96 112 513 (x2c_range_all (fun t => colsRowOK 384 31 cs (r0exp.getD t []) t) 96 16 chkK_0_d96) (x2c_join _ 112 128 513 (x2c_range_all (fun t => colsRowOK 384 31 cs (r0exp.getD t []) t) 112 16 chkK_0_d112) (x2c_join _ 128 144 513 (x2c_range_all (fun t => colsRowOK 384 31 cs (r0exp.getD t []) t) 128 16 chkK_0_d128) (x2c_join _ 144 160 513 (x2c_range_all (fun t => colsRowOK 384 31 cs (r0exp.getD t []) t) 144 16 chkK_0_d144) (x2c_join _ 160 176 513 (x2c_range_all (fun t => colsRowOK 384 31 cs (r0exp.getD t []) t) 160 16 chkK_0_d160) (x2c_join _ 176 192 513 (x2c_range_all (fun t => colsRowOK 384 31 cs (r0exp.getD t []) t) 176 16 chkK_0_d176) (x2c_join _ 192 208 513 (x2c_range_all (fun t => colsRowOK 384 31 cs (r0exp.getD t []) t) 192 16 chkK_0_d192) (x2c_join _ 208 224 513 (x2c_range_all (fun t => colsRowOK 384 31 cs (r0exp.getD t []) t) 208 16 chkK_0_d208) (x2c_join _ 224 240 513 (x2c_range_all (fun t => colsRowOK 384 31 cs (r0exp.getD t []) t) 224 16 chkK_0_d224) (x2c_join _ 240 256 513 (x2c_range_all (fun t => colsRowOK 384 31 cs (r0exp.getD t []) t) 240 16 chkK_0_d240) (x2c_join _ 256 272 513 (x2c_range_all (fun t => colsRowOK 384 31 cs (r0exp.getD t []) t) 256 16 chkK_0_d256) (x2c_join _ 272 288 513 (x2c_range_all (fun t => colsRowOK 384 31 cs (r0exp.getD t []) t) 272 16 chkK_0_d272) (x2c_join _ 288 304 513 (x2c_range_all (fun t => colsRowOK 384 31 cs (r0exp.getD t []) t) 288 16 chkK_0_d288) (x2c_join _ 304 320 513 (x2c_range_all (fun t => colsRowOK 384 31 cs (r0exp.getD t []) t) 304 16 chkK_0_d304) (x2c_join _ 320 336 513 (x2c_range_all (fun t => colsRowOK 384 31 cs (r0exp.getD t []) t) 320 16 chkK_0_d320) (x2c_join _ 336 352 513 (x2c_range_all (fun t => colsRowOK 384 31 cs (r0exp.getD t []) t) 336 16 chkK_0_d336) (x2c_join _ 352 368 513 (x2c_range_all (fun t => colsRowOK 384 31 cs (r0exp.getD t []) t) 352 16 chkK_0_d352) (x2c_join _ 368 384 513 (x2c_range_all (fun t => colsRowOK 384 31 cs (r0exp.getD t []) t) 368 16 chkK_0_d368) (x2c_join _ 384 400 513 (x2c_range_all (fun t => colsRowOK 384 31 cs (r0exp.getD t []) t) 384 16 chkK_0_d384) (x2c_join _ 400 416 513 (x2c_range_all (fun t => colsRowOK 384 31 cs (r0exp.getD t []) t) 400 16 chkK_0_d400) (x2c_join _ 416 432 513 (x2c_range_all (fun t => colsRowOK 384 31 cs (r0exp.getD t []) t) 416 16 chkK_0_d416) (x2c_join _ 432 448 513 (x2c_range_all (fun t => colsRowOK 384 31 cs (r0exp.getD t []) t) 432 16 chkK_0_d432) (x2c_join _ 448 464 513 (x2c_range_all (fun t => colsRowOK 384 31 cs (r0exp.getD t []) t) 448 16 chkK_0_d448) (x2c_join _ 464 480 513 (x2c_range_all (fun t => colsRowOK 384 31 cs (r0exp.getD t []) t) 464 16 chkK_0_d464) (x2c_join _ 480 496 513 (x2c_range_all (fun t => colsRowOK 384 31 cs (r0exp.getD t []) t) 480 16 chkK_0_d480) (x2c_join _ 496 512 513 (x2c_range_all (fun t => colsRowOK 384 31 cs (r0exp.getD t []) t) 496 16 chkK_0_d496) (x2c_range_all (fun t => colsRowOK 384 31 cs (r0exp.getD t []) t) 512 1 chkK_0_d512)))))))))))))))))))))))))))))))))


end ThreeCopyQutritWerner.X2.CoreS1g
