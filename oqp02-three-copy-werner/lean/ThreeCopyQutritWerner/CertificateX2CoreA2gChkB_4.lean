module

public import ThreeCopyQutritWerner.CertificateX2CoreA2gO
public import ThreeCopyQutritWerner.CertificateX2Trans
public import ThreeCopyQutritWerner.CertificateX2CoreBatchGen
public import ThreeCopyQutritWerner.CertificateX2CoreBatchFlat

@[expose] public section


/-! Batched core A2g: axis-1 stage, one output per declaration, flat indices 384..479. -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option exponentiation.threshold 1000000

namespace ThreeCopyQutritWerner.X2.CoreA2g
open ThreeCopyQutritWerner ThreeCopyQutritWerner.X2

theorem chkB_4_d384 : (List.range' 384 1).all (fun t => natAxpySp 384 21714 31 (transA2Tab.getD (t % 231) []) (h.getD (t / 231) []) (x2Tab o (t / 231) (t % 231))) = true := by
  decide +kernel

theorem chkB_4_d385 : (List.range' 385 1).all (fun t => natAxpySp 384 21714 31 (transA2Tab.getD (t % 231) []) (h.getD (t / 231) []) (x2Tab o (t / 231) (t % 231))) = true := by
  decide +kernel

theorem chkB_4_d386 : (List.range' 386 1).all (fun t => natAxpySp 384 21714 31 (transA2Tab.getD (t % 231) []) (h.getD (t / 231) []) (x2Tab o (t / 231) (t % 231))) = true := by
  decide +kernel

theorem chkB_4_d387 : (List.range' 387 1).all (fun t => natAxpySp 384 21714 31 (transA2Tab.getD (t % 231) []) (h.getD (t / 231) []) (x2Tab o (t / 231) (t % 231))) = true := by
  decide +kernel

theorem chkB_4_d388 : (List.range' 388 1).all (fun t => natAxpySp 384 21714 31 (transA2Tab.getD (t % 231) []) (h.getD (t / 231) []) (x2Tab o (t / 231) (t % 231))) = true := by
  decide +kernel

theorem chkB_4_d389 : (List.range' 389 1).all (fun t => natAxpySp 384 21714 31 (transA2Tab.getD (t % 231) []) (h.getD (t / 231) []) (x2Tab o (t / 231) (t % 231))) = true := by
  decide +kernel

theorem chkB_4_d390 : (List.range' 390 1).all (fun t => natAxpySp 384 21714 31 (transA2Tab.getD (t % 231) []) (h.getD (t / 231) []) (x2Tab o (t / 231) (t % 231))) = true := by
  decide +kernel

theorem chkB_4_d391 : (List.range' 391 1).all (fun t => natAxpySp 384 21714 31 (transA2Tab.getD (t % 231) []) (h.getD (t / 231) []) (x2Tab o (t / 231) (t % 231))) = true := by
  decide +kernel

theorem chkB_4_d392 : (List.range' 392 1).all (fun t => natAxpySp 384 21714 31 (transA2Tab.getD (t % 231) []) (h.getD (t / 231) []) (x2Tab o (t / 231) (t % 231))) = true := by
  decide +kernel

theorem chkB_4_d393 : (List.range' 393 1).all (fun t => natAxpySp 384 21714 31 (transA2Tab.getD (t % 231) []) (h.getD (t / 231) []) (x2Tab o (t / 231) (t % 231))) = true := by
  decide +kernel

theorem chkB_4_d394 : (List.range' 394 1).all (fun t => natAxpySp 384 21714 31 (transA2Tab.getD (t % 231) []) (h.getD (t / 231) []) (x2Tab o (t / 231) (t % 231))) = true := by
  decide +kernel

theorem chkB_4_d395 : (List.range' 395 1).all (fun t => natAxpySp 384 21714 31 (transA2Tab.getD (t % 231) []) (h.getD (t / 231) []) (x2Tab o (t / 231) (t % 231))) = true := by
  decide +kernel

theorem chkB_4_d396 : (List.range' 396 1).all (fun t => natAxpySp 384 21714 31 (transA2Tab.getD (t % 231) []) (h.getD (t / 231) []) (x2Tab o (t / 231) (t % 231))) = true := by
  decide +kernel

theorem chkB_4_d397 : (List.range' 397 1).all (fun t => natAxpySp 384 21714 31 (transA2Tab.getD (t % 231) []) (h.getD (t / 231) []) (x2Tab o (t / 231) (t % 231))) = true := by
  decide +kernel

theorem chkB_4_d398 : (List.range' 398 1).all (fun t => natAxpySp 384 21714 31 (transA2Tab.getD (t % 231) []) (h.getD (t / 231) []) (x2Tab o (t / 231) (t % 231))) = true := by
  decide +kernel

theorem chkB_4_d399 : (List.range' 399 1).all (fun t => natAxpySp 384 21714 31 (transA2Tab.getD (t % 231) []) (h.getD (t / 231) []) (x2Tab o (t / 231) (t % 231))) = true := by
  decide +kernel

theorem chkB_4_d400 : (List.range' 400 1).all (fun t => natAxpySp 384 21714 31 (transA2Tab.getD (t % 231) []) (h.getD (t / 231) []) (x2Tab o (t / 231) (t % 231))) = true := by
  decide +kernel

theorem chkB_4_d401 : (List.range' 401 1).all (fun t => natAxpySp 384 21714 31 (transA2Tab.getD (t % 231) []) (h.getD (t / 231) []) (x2Tab o (t / 231) (t % 231))) = true := by
  decide +kernel

theorem chkB_4_d402 : (List.range' 402 1).all (fun t => natAxpySp 384 21714 31 (transA2Tab.getD (t % 231) []) (h.getD (t / 231) []) (x2Tab o (t / 231) (t % 231))) = true := by
  decide +kernel

theorem chkB_4_d403 : (List.range' 403 1).all (fun t => natAxpySp 384 21714 31 (transA2Tab.getD (t % 231) []) (h.getD (t / 231) []) (x2Tab o (t / 231) (t % 231))) = true := by
  decide +kernel

theorem chkB_4_d404 : (List.range' 404 1).all (fun t => natAxpySp 384 21714 31 (transA2Tab.getD (t % 231) []) (h.getD (t / 231) []) (x2Tab o (t / 231) (t % 231))) = true := by
  decide +kernel

theorem chkB_4_d405 : (List.range' 405 1).all (fun t => natAxpySp 384 21714 31 (transA2Tab.getD (t % 231) []) (h.getD (t / 231) []) (x2Tab o (t / 231) (t % 231))) = true := by
  decide +kernel

theorem chkB_4_d406 : (List.range' 406 1).all (fun t => natAxpySp 384 21714 31 (transA2Tab.getD (t % 231) []) (h.getD (t / 231) []) (x2Tab o (t / 231) (t % 231))) = true := by
  decide +kernel

theorem chkB_4_d407 : (List.range' 407 1).all (fun t => natAxpySp 384 21714 31 (transA2Tab.getD (t % 231) []) (h.getD (t / 231) []) (x2Tab o (t / 231) (t % 231))) = true := by
  decide +kernel

theorem chkB_4_d408 : (List.range' 408 1).all (fun t => natAxpySp 384 21714 31 (transA2Tab.getD (t % 231) []) (h.getD (t / 231) []) (x2Tab o (t / 231) (t % 231))) = true := by
  decide +kernel

theorem chkB_4_d409 : (List.range' 409 1).all (fun t => natAxpySp 384 21714 31 (transA2Tab.getD (t % 231) []) (h.getD (t / 231) []) (x2Tab o (t / 231) (t % 231))) = true := by
  decide +kernel

theorem chkB_4_d410 : (List.range' 410 1).all (fun t => natAxpySp 384 21714 31 (transA2Tab.getD (t % 231) []) (h.getD (t / 231) []) (x2Tab o (t / 231) (t % 231))) = true := by
  decide +kernel

theorem chkB_4_d411 : (List.range' 411 1).all (fun t => natAxpySp 384 21714 31 (transA2Tab.getD (t % 231) []) (h.getD (t / 231) []) (x2Tab o (t / 231) (t % 231))) = true := by
  decide +kernel

theorem chkB_4_d412 : (List.range' 412 1).all (fun t => natAxpySp 384 21714 31 (transA2Tab.getD (t % 231) []) (h.getD (t / 231) []) (x2Tab o (t / 231) (t % 231))) = true := by
  decide +kernel

theorem chkB_4_d413 : (List.range' 413 1).all (fun t => natAxpySp 384 21714 31 (transA2Tab.getD (t % 231) []) (h.getD (t / 231) []) (x2Tab o (t / 231) (t % 231))) = true := by
  decide +kernel

theorem chkB_4_d414 : (List.range' 414 1).all (fun t => natAxpySp 384 21714 31 (transA2Tab.getD (t % 231) []) (h.getD (t / 231) []) (x2Tab o (t / 231) (t % 231))) = true := by
  decide +kernel

theorem chkB_4_d415 : (List.range' 415 1).all (fun t => natAxpySp 384 21714 31 (transA2Tab.getD (t % 231) []) (h.getD (t / 231) []) (x2Tab o (t / 231) (t % 231))) = true := by
  decide +kernel

theorem chkB_4_d416 : (List.range' 416 1).all (fun t => natAxpySp 384 21714 31 (transA2Tab.getD (t % 231) []) (h.getD (t / 231) []) (x2Tab o (t / 231) (t % 231))) = true := by
  decide +kernel

theorem chkB_4_d417 : (List.range' 417 1).all (fun t => natAxpySp 384 21714 31 (transA2Tab.getD (t % 231) []) (h.getD (t / 231) []) (x2Tab o (t / 231) (t % 231))) = true := by
  decide +kernel

theorem chkB_4_d418 : (List.range' 418 1).all (fun t => natAxpySp 384 21714 31 (transA2Tab.getD (t % 231) []) (h.getD (t / 231) []) (x2Tab o (t / 231) (t % 231))) = true := by
  decide +kernel

theorem chkB_4_d419 : (List.range' 419 1).all (fun t => natAxpySp 384 21714 31 (transA2Tab.getD (t % 231) []) (h.getD (t / 231) []) (x2Tab o (t / 231) (t % 231))) = true := by
  decide +kernel

theorem chkB_4_d420 : (List.range' 420 1).all (fun t => natAxpySp 384 21714 31 (transA2Tab.getD (t % 231) []) (h.getD (t / 231) []) (x2Tab o (t / 231) (t % 231))) = true := by
  decide +kernel

theorem chkB_4_d421 : (List.range' 421 1).all (fun t => natAxpySp 384 21714 31 (transA2Tab.getD (t % 231) []) (h.getD (t / 231) []) (x2Tab o (t / 231) (t % 231))) = true := by
  decide +kernel

theorem chkB_4_d422 : (List.range' 422 1).all (fun t => natAxpySp 384 21714 31 (transA2Tab.getD (t % 231) []) (h.getD (t / 231) []) (x2Tab o (t / 231) (t % 231))) = true := by
  decide +kernel

theorem chkB_4_d423 : (List.range' 423 1).all (fun t => natAxpySp 384 21714 31 (transA2Tab.getD (t % 231) []) (h.getD (t / 231) []) (x2Tab o (t / 231) (t % 231))) = true := by
  decide +kernel

theorem chkB_4_d424 : (List.range' 424 1).all (fun t => natAxpySp 384 21714 31 (transA2Tab.getD (t % 231) []) (h.getD (t / 231) []) (x2Tab o (t / 231) (t % 231))) = true := by
  decide +kernel

theorem chkB_4_d425 : (List.range' 425 1).all (fun t => natAxpySp 384 21714 31 (transA2Tab.getD (t % 231) []) (h.getD (t / 231) []) (x2Tab o (t / 231) (t % 231))) = true := by
  decide +kernel

theorem chkB_4_d426 : (List.range' 426 1).all (fun t => natAxpySp 384 21714 31 (transA2Tab.getD (t % 231) []) (h.getD (t / 231) []) (x2Tab o (t / 231) (t % 231))) = true := by
  decide +kernel

theorem chkB_4_d427 : (List.range' 427 1).all (fun t => natAxpySp 384 21714 31 (transA2Tab.getD (t % 231) []) (h.getD (t / 231) []) (x2Tab o (t / 231) (t % 231))) = true := by
  decide +kernel

theorem chkB_4_d428 : (List.range' 428 1).all (fun t => natAxpySp 384 21714 31 (transA2Tab.getD (t % 231) []) (h.getD (t / 231) []) (x2Tab o (t / 231) (t % 231))) = true := by
  decide +kernel

theorem chkB_4_d429 : (List.range' 429 1).all (fun t => natAxpySp 384 21714 31 (transA2Tab.getD (t % 231) []) (h.getD (t / 231) []) (x2Tab o (t / 231) (t % 231))) = true := by
  decide +kernel

theorem chkB_4_d430 : (List.range' 430 1).all (fun t => natAxpySp 384 21714 31 (transA2Tab.getD (t % 231) []) (h.getD (t / 231) []) (x2Tab o (t / 231) (t % 231))) = true := by
  decide +kernel

theorem chkB_4_d431 : (List.range' 431 1).all (fun t => natAxpySp 384 21714 31 (transA2Tab.getD (t % 231) []) (h.getD (t / 231) []) (x2Tab o (t / 231) (t % 231))) = true := by
  decide +kernel

theorem chkB_4_d432 : (List.range' 432 1).all (fun t => natAxpySp 384 21714 31 (transA2Tab.getD (t % 231) []) (h.getD (t / 231) []) (x2Tab o (t / 231) (t % 231))) = true := by
  decide +kernel

theorem chkB_4_d433 : (List.range' 433 1).all (fun t => natAxpySp 384 21714 31 (transA2Tab.getD (t % 231) []) (h.getD (t / 231) []) (x2Tab o (t / 231) (t % 231))) = true := by
  decide +kernel

theorem chkB_4_d434 : (List.range' 434 1).all (fun t => natAxpySp 384 21714 31 (transA2Tab.getD (t % 231) []) (h.getD (t / 231) []) (x2Tab o (t / 231) (t % 231))) = true := by
  decide +kernel

theorem chkB_4_d435 : (List.range' 435 1).all (fun t => natAxpySp 384 21714 31 (transA2Tab.getD (t % 231) []) (h.getD (t / 231) []) (x2Tab o (t / 231) (t % 231))) = true := by
  decide +kernel

theorem chkB_4_d436 : (List.range' 436 1).all (fun t => natAxpySp 384 21714 31 (transA2Tab.getD (t % 231) []) (h.getD (t / 231) []) (x2Tab o (t / 231) (t % 231))) = true := by
  decide +kernel

theorem chkB_4_d437 : (List.range' 437 1).all (fun t => natAxpySp 384 21714 31 (transA2Tab.getD (t % 231) []) (h.getD (t / 231) []) (x2Tab o (t / 231) (t % 231))) = true := by
  decide +kernel

theorem chkB_4_d438 : (List.range' 438 1).all (fun t => natAxpySp 384 21714 31 (transA2Tab.getD (t % 231) []) (h.getD (t / 231) []) (x2Tab o (t / 231) (t % 231))) = true := by
  decide +kernel

theorem chkB_4_d439 : (List.range' 439 1).all (fun t => natAxpySp 384 21714 31 (transA2Tab.getD (t % 231) []) (h.getD (t / 231) []) (x2Tab o (t / 231) (t % 231))) = true := by
  decide +kernel

theorem chkB_4_d440 : (List.range' 440 1).all (fun t => natAxpySp 384 21714 31 (transA2Tab.getD (t % 231) []) (h.getD (t / 231) []) (x2Tab o (t / 231) (t % 231))) = true := by
  decide +kernel

theorem chkB_4_d441 : (List.range' 441 1).all (fun t => natAxpySp 384 21714 31 (transA2Tab.getD (t % 231) []) (h.getD (t / 231) []) (x2Tab o (t / 231) (t % 231))) = true := by
  decide +kernel

theorem chkB_4_d442 : (List.range' 442 1).all (fun t => natAxpySp 384 21714 31 (transA2Tab.getD (t % 231) []) (h.getD (t / 231) []) (x2Tab o (t / 231) (t % 231))) = true := by
  decide +kernel

theorem chkB_4_d443 : (List.range' 443 1).all (fun t => natAxpySp 384 21714 31 (transA2Tab.getD (t % 231) []) (h.getD (t / 231) []) (x2Tab o (t / 231) (t % 231))) = true := by
  decide +kernel

theorem chkB_4_d444 : (List.range' 444 1).all (fun t => natAxpySp 384 21714 31 (transA2Tab.getD (t % 231) []) (h.getD (t / 231) []) (x2Tab o (t / 231) (t % 231))) = true := by
  decide +kernel

theorem chkB_4_d445 : (List.range' 445 1).all (fun t => natAxpySp 384 21714 31 (transA2Tab.getD (t % 231) []) (h.getD (t / 231) []) (x2Tab o (t / 231) (t % 231))) = true := by
  decide +kernel

theorem chkB_4_d446 : (List.range' 446 1).all (fun t => natAxpySp 384 21714 31 (transA2Tab.getD (t % 231) []) (h.getD (t / 231) []) (x2Tab o (t / 231) (t % 231))) = true := by
  decide +kernel

theorem chkB_4_d447 : (List.range' 447 1).all (fun t => natAxpySp 384 21714 31 (transA2Tab.getD (t % 231) []) (h.getD (t / 231) []) (x2Tab o (t / 231) (t % 231))) = true := by
  decide +kernel

theorem chkB_4_d448 : (List.range' 448 1).all (fun t => natAxpySp 384 21714 31 (transA2Tab.getD (t % 231) []) (h.getD (t / 231) []) (x2Tab o (t / 231) (t % 231))) = true := by
  decide +kernel

theorem chkB_4_d449 : (List.range' 449 1).all (fun t => natAxpySp 384 21714 31 (transA2Tab.getD (t % 231) []) (h.getD (t / 231) []) (x2Tab o (t / 231) (t % 231))) = true := by
  decide +kernel

theorem chkB_4_d450 : (List.range' 450 1).all (fun t => natAxpySp 384 21714 31 (transA2Tab.getD (t % 231) []) (h.getD (t / 231) []) (x2Tab o (t / 231) (t % 231))) = true := by
  decide +kernel

theorem chkB_4_d451 : (List.range' 451 1).all (fun t => natAxpySp 384 21714 31 (transA2Tab.getD (t % 231) []) (h.getD (t / 231) []) (x2Tab o (t / 231) (t % 231))) = true := by
  decide +kernel

theorem chkB_4_d452 : (List.range' 452 1).all (fun t => natAxpySp 384 21714 31 (transA2Tab.getD (t % 231) []) (h.getD (t / 231) []) (x2Tab o (t / 231) (t % 231))) = true := by
  decide +kernel

theorem chkB_4_d453 : (List.range' 453 1).all (fun t => natAxpySp 384 21714 31 (transA2Tab.getD (t % 231) []) (h.getD (t / 231) []) (x2Tab o (t / 231) (t % 231))) = true := by
  decide +kernel

theorem chkB_4_d454 : (List.range' 454 1).all (fun t => natAxpySp 384 21714 31 (transA2Tab.getD (t % 231) []) (h.getD (t / 231) []) (x2Tab o (t / 231) (t % 231))) = true := by
  decide +kernel

theorem chkB_4_d455 : (List.range' 455 1).all (fun t => natAxpySp 384 21714 31 (transA2Tab.getD (t % 231) []) (h.getD (t / 231) []) (x2Tab o (t / 231) (t % 231))) = true := by
  decide +kernel

theorem chkB_4_d456 : (List.range' 456 1).all (fun t => natAxpySp 384 21714 31 (transA2Tab.getD (t % 231) []) (h.getD (t / 231) []) (x2Tab o (t / 231) (t % 231))) = true := by
  decide +kernel

theorem chkB_4_d457 : (List.range' 457 1).all (fun t => natAxpySp 384 21714 31 (transA2Tab.getD (t % 231) []) (h.getD (t / 231) []) (x2Tab o (t / 231) (t % 231))) = true := by
  decide +kernel

theorem chkB_4_d458 : (List.range' 458 1).all (fun t => natAxpySp 384 21714 31 (transA2Tab.getD (t % 231) []) (h.getD (t / 231) []) (x2Tab o (t / 231) (t % 231))) = true := by
  decide +kernel

theorem chkB_4_d459 : (List.range' 459 1).all (fun t => natAxpySp 384 21714 31 (transA2Tab.getD (t % 231) []) (h.getD (t / 231) []) (x2Tab o (t / 231) (t % 231))) = true := by
  decide +kernel

theorem chkB_4_d460 : (List.range' 460 1).all (fun t => natAxpySp 384 21714 31 (transA2Tab.getD (t % 231) []) (h.getD (t / 231) []) (x2Tab o (t / 231) (t % 231))) = true := by
  decide +kernel

theorem chkB_4_d461 : (List.range' 461 1).all (fun t => natAxpySp 384 21714 31 (transA2Tab.getD (t % 231) []) (h.getD (t / 231) []) (x2Tab o (t / 231) (t % 231))) = true := by
  decide +kernel

theorem chkB_4_d462 : (List.range' 462 1).all (fun t => natAxpySp 384 21714 31 (transA2Tab.getD (t % 231) []) (h.getD (t / 231) []) (x2Tab o (t / 231) (t % 231))) = true := by
  decide +kernel

theorem chkB_4_d463 : (List.range' 463 1).all (fun t => natAxpySp 384 21714 31 (transA2Tab.getD (t % 231) []) (h.getD (t / 231) []) (x2Tab o (t / 231) (t % 231))) = true := by
  decide +kernel

theorem chkB_4_d464 : (List.range' 464 1).all (fun t => natAxpySp 384 21714 31 (transA2Tab.getD (t % 231) []) (h.getD (t / 231) []) (x2Tab o (t / 231) (t % 231))) = true := by
  decide +kernel

theorem chkB_4_d465 : (List.range' 465 1).all (fun t => natAxpySp 384 21714 31 (transA2Tab.getD (t % 231) []) (h.getD (t / 231) []) (x2Tab o (t / 231) (t % 231))) = true := by
  decide +kernel

theorem chkB_4_d466 : (List.range' 466 1).all (fun t => natAxpySp 384 21714 31 (transA2Tab.getD (t % 231) []) (h.getD (t / 231) []) (x2Tab o (t / 231) (t % 231))) = true := by
  decide +kernel

theorem chkB_4_d467 : (List.range' 467 1).all (fun t => natAxpySp 384 21714 31 (transA2Tab.getD (t % 231) []) (h.getD (t / 231) []) (x2Tab o (t / 231) (t % 231))) = true := by
  decide +kernel

theorem chkB_4_d468 : (List.range' 468 1).all (fun t => natAxpySp 384 21714 31 (transA2Tab.getD (t % 231) []) (h.getD (t / 231) []) (x2Tab o (t / 231) (t % 231))) = true := by
  decide +kernel

theorem chkB_4_d469 : (List.range' 469 1).all (fun t => natAxpySp 384 21714 31 (transA2Tab.getD (t % 231) []) (h.getD (t / 231) []) (x2Tab o (t / 231) (t % 231))) = true := by
  decide +kernel

theorem chkB_4_d470 : (List.range' 470 1).all (fun t => natAxpySp 384 21714 31 (transA2Tab.getD (t % 231) []) (h.getD (t / 231) []) (x2Tab o (t / 231) (t % 231))) = true := by
  decide +kernel

theorem chkB_4_d471 : (List.range' 471 1).all (fun t => natAxpySp 384 21714 31 (transA2Tab.getD (t % 231) []) (h.getD (t / 231) []) (x2Tab o (t / 231) (t % 231))) = true := by
  decide +kernel

theorem chkB_4_d472 : (List.range' 472 1).all (fun t => natAxpySp 384 21714 31 (transA2Tab.getD (t % 231) []) (h.getD (t / 231) []) (x2Tab o (t / 231) (t % 231))) = true := by
  decide +kernel

theorem chkB_4_d473 : (List.range' 473 1).all (fun t => natAxpySp 384 21714 31 (transA2Tab.getD (t % 231) []) (h.getD (t / 231) []) (x2Tab o (t / 231) (t % 231))) = true := by
  decide +kernel

theorem chkB_4_d474 : (List.range' 474 1).all (fun t => natAxpySp 384 21714 31 (transA2Tab.getD (t % 231) []) (h.getD (t / 231) []) (x2Tab o (t / 231) (t % 231))) = true := by
  decide +kernel

theorem chkB_4_d475 : (List.range' 475 1).all (fun t => natAxpySp 384 21714 31 (transA2Tab.getD (t % 231) []) (h.getD (t / 231) []) (x2Tab o (t / 231) (t % 231))) = true := by
  decide +kernel

theorem chkB_4_d476 : (List.range' 476 1).all (fun t => natAxpySp 384 21714 31 (transA2Tab.getD (t % 231) []) (h.getD (t / 231) []) (x2Tab o (t / 231) (t % 231))) = true := by
  decide +kernel

theorem chkB_4_d477 : (List.range' 477 1).all (fun t => natAxpySp 384 21714 31 (transA2Tab.getD (t % 231) []) (h.getD (t / 231) []) (x2Tab o (t / 231) (t % 231))) = true := by
  decide +kernel

theorem chkB_4_d478 : (List.range' 478 1).all (fun t => natAxpySp 384 21714 31 (transA2Tab.getD (t % 231) []) (h.getD (t / 231) []) (x2Tab o (t / 231) (t % 231))) = true := by
  decide +kernel

theorem chkB_4_d479 : (List.range' 479 1).all (fun t => natAxpySp 384 21714 31 (transA2Tab.getD (t % 231) []) (h.getD (t / 231) []) (x2Tab o (t / 231) (t % 231))) = true := by
  decide +kernel

theorem chkB_4 : ∀ t, 384 ≤ t → t < 480 → (natAxpySp 384 21714 31 (transA2Tab.getD (t % 231) []) (h.getD (t / 231) []) (x2Tab o (t / 231) (t % 231))) = true := by
  exact (x2c_join _ 384 385 480 (x2c_range_all (fun t => natAxpySp 384 21714 31 (transA2Tab.getD (t % 231) []) (h.getD (t / 231) []) (x2Tab o (t / 231) (t % 231))) 384 1 chkB_4_d384) (x2c_join _ 385 386 480 (x2c_range_all (fun t => natAxpySp 384 21714 31 (transA2Tab.getD (t % 231) []) (h.getD (t / 231) []) (x2Tab o (t / 231) (t % 231))) 385 1 chkB_4_d385) (x2c_join _ 386 387 480 (x2c_range_all (fun t => natAxpySp 384 21714 31 (transA2Tab.getD (t % 231) []) (h.getD (t / 231) []) (x2Tab o (t / 231) (t % 231))) 386 1 chkB_4_d386) (x2c_join _ 387 388 480 (x2c_range_all (fun t => natAxpySp 384 21714 31 (transA2Tab.getD (t % 231) []) (h.getD (t / 231) []) (x2Tab o (t / 231) (t % 231))) 387 1 chkB_4_d387) (x2c_join _ 388 389 480 (x2c_range_all (fun t => natAxpySp 384 21714 31 (transA2Tab.getD (t % 231) []) (h.getD (t / 231) []) (x2Tab o (t / 231) (t % 231))) 388 1 chkB_4_d388) (x2c_join _ 389 390 480 (x2c_range_all (fun t => natAxpySp 384 21714 31 (transA2Tab.getD (t % 231) []) (h.getD (t / 231) []) (x2Tab o (t / 231) (t % 231))) 389 1 chkB_4_d389) (x2c_join _ 390 391 480 (x2c_range_all (fun t => natAxpySp 384 21714 31 (transA2Tab.getD (t % 231) []) (h.getD (t / 231) []) (x2Tab o (t / 231) (t % 231))) 390 1 chkB_4_d390) (x2c_join _ 391 392 480 (x2c_range_all (fun t => natAxpySp 384 21714 31 (transA2Tab.getD (t % 231) []) (h.getD (t / 231) []) (x2Tab o (t / 231) (t % 231))) 391 1 chkB_4_d391) (x2c_join _ 392 393 480 (x2c_range_all (fun t => natAxpySp 384 21714 31 (transA2Tab.getD (t % 231) []) (h.getD (t / 231) []) (x2Tab o (t / 231) (t % 231))) 392 1 chkB_4_d392) (x2c_join _ 393 394 480 (x2c_range_all (fun t => natAxpySp 384 21714 31 (transA2Tab.getD (t % 231) []) (h.getD (t / 231) []) (x2Tab o (t / 231) (t % 231))) 393 1 chkB_4_d393) (x2c_join _ 394 395 480 (x2c_range_all (fun t => natAxpySp 384 21714 31 (transA2Tab.getD (t % 231) []) (h.getD (t / 231) []) (x2Tab o (t / 231) (t % 231))) 394 1 chkB_4_d394) (x2c_join _ 395 396 480 (x2c_range_all (fun t => natAxpySp 384 21714 31 (transA2Tab.getD (t % 231) []) (h.getD (t / 231) []) (x2Tab o (t / 231) (t % 231))) 395 1 chkB_4_d395) (x2c_join _ 396 397 480 (x2c_range_all (fun t => natAxpySp 384 21714 31 (transA2Tab.getD (t % 231) []) (h.getD (t / 231) []) (x2Tab o (t / 231) (t % 231))) 396 1 chkB_4_d396) (x2c_join _ 397 398 480 (x2c_range_all (fun t => natAxpySp 384 21714 31 (transA2Tab.getD (t % 231) []) (h.getD (t / 231) []) (x2Tab o (t / 231) (t % 231))) 397 1 chkB_4_d397) (x2c_join _ 398 399 480 (x2c_range_all (fun t => natAxpySp 384 21714 31 (transA2Tab.getD (t % 231) []) (h.getD (t / 231) []) (x2Tab o (t / 231) (t % 231))) 398 1 chkB_4_d398) (x2c_join _ 399 400 480 (x2c_range_all (fun t => natAxpySp 384 21714 31 (transA2Tab.getD (t % 231) []) (h.getD (t / 231) []) (x2Tab o (t / 231) (t % 231))) 399 1 chkB_4_d399) (x2c_join _ 400 401 480 (x2c_range_all (fun t => natAxpySp 384 21714 31 (transA2Tab.getD (t % 231) []) (h.getD (t / 231) []) (x2Tab o (t / 231) (t % 231))) 400 1 chkB_4_d400) (x2c_join _ 401 402 480 (x2c_range_all (fun t => natAxpySp 384 21714 31 (transA2Tab.getD (t % 231) []) (h.getD (t / 231) []) (x2Tab o (t / 231) (t % 231))) 401 1 chkB_4_d401) (x2c_join _ 402 403 480 (x2c_range_all (fun t => natAxpySp 384 21714 31 (transA2Tab.getD (t % 231) []) (h.getD (t / 231) []) (x2Tab o (t / 231) (t % 231))) 402 1 chkB_4_d402) (x2c_join _ 403 404 480 (x2c_range_all (fun t => natAxpySp 384 21714 31 (transA2Tab.getD (t % 231) []) (h.getD (t / 231) []) (x2Tab o (t / 231) (t % 231))) 403 1 chkB_4_d403) (x2c_join _ 404 405 480 (x2c_range_all (fun t => natAxpySp 384 21714 31 (transA2Tab.getD (t % 231) []) (h.getD (t / 231) []) (x2Tab o (t / 231) (t % 231))) 404 1 chkB_4_d404) (x2c_join _ 405 406 480 (x2c_range_all (fun t => natAxpySp 384 21714 31 (transA2Tab.getD (t % 231) []) (h.getD (t / 231) []) (x2Tab o (t / 231) (t % 231))) 405 1 chkB_4_d405) (x2c_join _ 406 407 480 (x2c_range_all (fun t => natAxpySp 384 21714 31 (transA2Tab.getD (t % 231) []) (h.getD (t / 231) []) (x2Tab o (t / 231) (t % 231))) 406 1 chkB_4_d406) (x2c_join _ 407 408 480 (x2c_range_all (fun t => natAxpySp 384 21714 31 (transA2Tab.getD (t % 231) []) (h.getD (t / 231) []) (x2Tab o (t / 231) (t % 231))) 407 1 chkB_4_d407) (x2c_join _ 408 409 480 (x2c_range_all (fun t => natAxpySp 384 21714 31 (transA2Tab.getD (t % 231) []) (h.getD (t / 231) []) (x2Tab o (t / 231) (t % 231))) 408 1 chkB_4_d408) (x2c_join _ 409 410 480 (x2c_range_all (fun t => natAxpySp 384 21714 31 (transA2Tab.getD (t % 231) []) (h.getD (t / 231) []) (x2Tab o (t / 231) (t % 231))) 409 1 chkB_4_d409) (x2c_join _ 410 411 480 (x2c_range_all (fun t => natAxpySp 384 21714 31 (transA2Tab.getD (t % 231) []) (h.getD (t / 231) []) (x2Tab o (t / 231) (t % 231))) 410 1 chkB_4_d410) (x2c_join _ 411 412 480 (x2c_range_all (fun t => natAxpySp 384 21714 31 (transA2Tab.getD (t % 231) []) (h.getD (t / 231) []) (x2Tab o (t / 231) (t % 231))) 411 1 chkB_4_d411) (x2c_join _ 412 413 480 (x2c_range_all (fun t => natAxpySp 384 21714 31 (transA2Tab.getD (t % 231) []) (h.getD (t / 231) []) (x2Tab o (t / 231) (t % 231))) 412 1 chkB_4_d412) (x2c_join _ 413 414 480 (x2c_range_all (fun t => natAxpySp 384 21714 31 (transA2Tab.getD (t % 231) []) (h.getD (t / 231) []) (x2Tab o (t / 231) (t % 231))) 413 1 chkB_4_d413) (x2c_join _ 414 415 480 (x2c_range_all (fun t => natAxpySp 384 21714 31 (transA2Tab.getD (t % 231) []) (h.getD (t / 231) []) (x2Tab o (t / 231) (t % 231))) 414 1 chkB_4_d414) (x2c_join _ 415 416 480 (x2c_range_all (fun t => natAxpySp 384 21714 31 (transA2Tab.getD (t % 231) []) (h.getD (t / 231) []) (x2Tab o (t / 231) (t % 231))) 415 1 chkB_4_d415) (x2c_join _ 416 417 480 (x2c_range_all (fun t => natAxpySp 384 21714 31 (transA2Tab.getD (t % 231) []) (h.getD (t / 231) []) (x2Tab o (t / 231) (t % 231))) 416 1 chkB_4_d416) (x2c_join _ 417 418 480 (x2c_range_all (fun t => natAxpySp 384 21714 31 (transA2Tab.getD (t % 231) []) (h.getD (t / 231) []) (x2Tab o (t / 231) (t % 231))) 417 1 chkB_4_d417) (x2c_join _ 418 419 480 (x2c_range_all (fun t => natAxpySp 384 21714 31 (transA2Tab.getD (t % 231) []) (h.getD (t / 231) []) (x2Tab o (t / 231) (t % 231))) 418 1 chkB_4_d418) (x2c_join _ 419 420 480 (x2c_range_all (fun t => natAxpySp 384 21714 31 (transA2Tab.getD (t % 231) []) (h.getD (t / 231) []) (x2Tab o (t / 231) (t % 231))) 419 1 chkB_4_d419) (x2c_join _ 420 421 480 (x2c_range_all (fun t => natAxpySp 384 21714 31 (transA2Tab.getD (t % 231) []) (h.getD (t / 231) []) (x2Tab o (t / 231) (t % 231))) 420 1 chkB_4_d420) (x2c_join _ 421 422 480 (x2c_range_all (fun t => natAxpySp 384 21714 31 (transA2Tab.getD (t % 231) []) (h.getD (t / 231) []) (x2Tab o (t / 231) (t % 231))) 421 1 chkB_4_d421) (x2c_join _ 422 423 480 (x2c_range_all (fun t => natAxpySp 384 21714 31 (transA2Tab.getD (t % 231) []) (h.getD (t / 231) []) (x2Tab o (t / 231) (t % 231))) 422 1 chkB_4_d422) (x2c_join _ 423 424 480 (x2c_range_all (fun t => natAxpySp 384 21714 31 (transA2Tab.getD (t % 231) []) (h.getD (t / 231) []) (x2Tab o (t / 231) (t % 231))) 423 1 chkB_4_d423) (x2c_join _ 424 425 480 (x2c_range_all (fun t => natAxpySp 384 21714 31 (transA2Tab.getD (t % 231) []) (h.getD (t / 231) []) (x2Tab o (t / 231) (t % 231))) 424 1 chkB_4_d424) (x2c_join _ 425 426 480 (x2c_range_all (fun t => natAxpySp 384 21714 31 (transA2Tab.getD (t % 231) []) (h.getD (t / 231) []) (x2Tab o (t / 231) (t % 231))) 425 1 chkB_4_d425) (x2c_join _ 426 427 480 (x2c_range_all (fun t => natAxpySp 384 21714 31 (transA2Tab.getD (t % 231) []) (h.getD (t / 231) []) (x2Tab o (t / 231) (t % 231))) 426 1 chkB_4_d426) (x2c_join _ 427 428 480 (x2c_range_all (fun t => natAxpySp 384 21714 31 (transA2Tab.getD (t % 231) []) (h.getD (t / 231) []) (x2Tab o (t / 231) (t % 231))) 427 1 chkB_4_d427) (x2c_join _ 428 429 480 (x2c_range_all (fun t => natAxpySp 384 21714 31 (transA2Tab.getD (t % 231) []) (h.getD (t / 231) []) (x2Tab o (t / 231) (t % 231))) 428 1 chkB_4_d428) (x2c_join _ 429 430 480 (x2c_range_all (fun t => natAxpySp 384 21714 31 (transA2Tab.getD (t % 231) []) (h.getD (t / 231) []) (x2Tab o (t / 231) (t % 231))) 429 1 chkB_4_d429) (x2c_join _ 430 431 480 (x2c_range_all (fun t => natAxpySp 384 21714 31 (transA2Tab.getD (t % 231) []) (h.getD (t / 231) []) (x2Tab o (t / 231) (t % 231))) 430 1 chkB_4_d430) (x2c_join _ 431 432 480 (x2c_range_all (fun t => natAxpySp 384 21714 31 (transA2Tab.getD (t % 231) []) (h.getD (t / 231) []) (x2Tab o (t / 231) (t % 231))) 431 1 chkB_4_d431) (x2c_join _ 432 433 480 (x2c_range_all (fun t => natAxpySp 384 21714 31 (transA2Tab.getD (t % 231) []) (h.getD (t / 231) []) (x2Tab o (t / 231) (t % 231))) 432 1 chkB_4_d432) (x2c_join _ 433 434 480 (x2c_range_all (fun t => natAxpySp 384 21714 31 (transA2Tab.getD (t % 231) []) (h.getD (t / 231) []) (x2Tab o (t / 231) (t % 231))) 433 1 chkB_4_d433) (x2c_join _ 434 435 480 (x2c_range_all (fun t => natAxpySp 384 21714 31 (transA2Tab.getD (t % 231) []) (h.getD (t / 231) []) (x2Tab o (t / 231) (t % 231))) 434 1 chkB_4_d434) (x2c_join _ 435 436 480 (x2c_range_all (fun t => natAxpySp 384 21714 31 (transA2Tab.getD (t % 231) []) (h.getD (t / 231) []) (x2Tab o (t / 231) (t % 231))) 435 1 chkB_4_d435) (x2c_join _ 436 437 480 (x2c_range_all (fun t => natAxpySp 384 21714 31 (transA2Tab.getD (t % 231) []) (h.getD (t / 231) []) (x2Tab o (t / 231) (t % 231))) 436 1 chkB_4_d436) (x2c_join _ 437 438 480 (x2c_range_all (fun t => natAxpySp 384 21714 31 (transA2Tab.getD (t % 231) []) (h.getD (t / 231) []) (x2Tab o (t / 231) (t % 231))) 437 1 chkB_4_d437) (x2c_join _ 438 439 480 (x2c_range_all (fun t => natAxpySp 384 21714 31 (transA2Tab.getD (t % 231) []) (h.getD (t / 231) []) (x2Tab o (t / 231) (t % 231))) 438 1 chkB_4_d438) (x2c_join _ 439 440 480 (x2c_range_all (fun t => natAxpySp 384 21714 31 (transA2Tab.getD (t % 231) []) (h.getD (t / 231) []) (x2Tab o (t / 231) (t % 231))) 439 1 chkB_4_d439) (x2c_join _ 440 441 480 (x2c_range_all (fun t => natAxpySp 384 21714 31 (transA2Tab.getD (t % 231) []) (h.getD (t / 231) []) (x2Tab o (t / 231) (t % 231))) 440 1 chkB_4_d440) (x2c_join _ 441 442 480 (x2c_range_all (fun t => natAxpySp 384 21714 31 (transA2Tab.getD (t % 231) []) (h.getD (t / 231) []) (x2Tab o (t / 231) (t % 231))) 441 1 chkB_4_d441) (x2c_join _ 442 443 480 (x2c_range_all (fun t => natAxpySp 384 21714 31 (transA2Tab.getD (t % 231) []) (h.getD (t / 231) []) (x2Tab o (t / 231) (t % 231))) 442 1 chkB_4_d442) (x2c_join _ 443 444 480 (x2c_range_all (fun t => natAxpySp 384 21714 31 (transA2Tab.getD (t % 231) []) (h.getD (t / 231) []) (x2Tab o (t / 231) (t % 231))) 443 1 chkB_4_d443) (x2c_join _ 444 445 480 (x2c_range_all (fun t => natAxpySp 384 21714 31 (transA2Tab.getD (t % 231) []) (h.getD (t / 231) []) (x2Tab o (t / 231) (t % 231))) 444 1 chkB_4_d444) (x2c_join _ 445 446 480 (x2c_range_all (fun t => natAxpySp 384 21714 31 (transA2Tab.getD (t % 231) []) (h.getD (t / 231) []) (x2Tab o (t / 231) (t % 231))) 445 1 chkB_4_d445) (x2c_join _ 446 447 480 (x2c_range_all (fun t => natAxpySp 384 21714 31 (transA2Tab.getD (t % 231) []) (h.getD (t / 231) []) (x2Tab o (t / 231) (t % 231))) 446 1 chkB_4_d446) (x2c_join _ 447 448 480 (x2c_range_all (fun t => natAxpySp 384 21714 31 (transA2Tab.getD (t % 231) []) (h.getD (t / 231) []) (x2Tab o (t / 231) (t % 231))) 447 1 chkB_4_d447) (x2c_join _ 448 449 480 (x2c_range_all (fun t => natAxpySp 384 21714 31 (transA2Tab.getD (t % 231) []) (h.getD (t / 231) []) (x2Tab o (t / 231) (t % 231))) 448 1 chkB_4_d448) (x2c_join _ 449 450 480 (x2c_range_all (fun t => natAxpySp 384 21714 31 (transA2Tab.getD (t % 231) []) (h.getD (t / 231) []) (x2Tab o (t / 231) (t % 231))) 449 1 chkB_4_d449) (x2c_join _ 450 451 480 (x2c_range_all (fun t => natAxpySp 384 21714 31 (transA2Tab.getD (t % 231) []) (h.getD (t / 231) []) (x2Tab o (t / 231) (t % 231))) 450 1 chkB_4_d450) (x2c_join _ 451 452 480 (x2c_range_all (fun t => natAxpySp 384 21714 31 (transA2Tab.getD (t % 231) []) (h.getD (t / 231) []) (x2Tab o (t / 231) (t % 231))) 451 1 chkB_4_d451) (x2c_join _ 452 453 480 (x2c_range_all (fun t => natAxpySp 384 21714 31 (transA2Tab.getD (t % 231) []) (h.getD (t / 231) []) (x2Tab o (t / 231) (t % 231))) 452 1 chkB_4_d452) (x2c_join _ 453 454 480 (x2c_range_all (fun t => natAxpySp 384 21714 31 (transA2Tab.getD (t % 231) []) (h.getD (t / 231) []) (x2Tab o (t / 231) (t % 231))) 453 1 chkB_4_d453) (x2c_join _ 454 455 480 (x2c_range_all (fun t => natAxpySp 384 21714 31 (transA2Tab.getD (t % 231) []) (h.getD (t / 231) []) (x2Tab o (t / 231) (t % 231))) 454 1 chkB_4_d454) (x2c_join _ 455 456 480 (x2c_range_all (fun t => natAxpySp 384 21714 31 (transA2Tab.getD (t % 231) []) (h.getD (t / 231) []) (x2Tab o (t / 231) (t % 231))) 455 1 chkB_4_d455) (x2c_join _ 456 457 480 (x2c_range_all (fun t => natAxpySp 384 21714 31 (transA2Tab.getD (t % 231) []) (h.getD (t / 231) []) (x2Tab o (t / 231) (t % 231))) 456 1 chkB_4_d456) (x2c_join _ 457 458 480 (x2c_range_all (fun t => natAxpySp 384 21714 31 (transA2Tab.getD (t % 231) []) (h.getD (t / 231) []) (x2Tab o (t / 231) (t % 231))) 457 1 chkB_4_d457) (x2c_join _ 458 459 480 (x2c_range_all (fun t => natAxpySp 384 21714 31 (transA2Tab.getD (t % 231) []) (h.getD (t / 231) []) (x2Tab o (t / 231) (t % 231))) 458 1 chkB_4_d458) (x2c_join _ 459 460 480 (x2c_range_all (fun t => natAxpySp 384 21714 31 (transA2Tab.getD (t % 231) []) (h.getD (t / 231) []) (x2Tab o (t / 231) (t % 231))) 459 1 chkB_4_d459) (x2c_join _ 460 461 480 (x2c_range_all (fun t => natAxpySp 384 21714 31 (transA2Tab.getD (t % 231) []) (h.getD (t / 231) []) (x2Tab o (t / 231) (t % 231))) 460 1 chkB_4_d460) (x2c_join _ 461 462 480 (x2c_range_all (fun t => natAxpySp 384 21714 31 (transA2Tab.getD (t % 231) []) (h.getD (t / 231) []) (x2Tab o (t / 231) (t % 231))) 461 1 chkB_4_d461) (x2c_join _ 462 463 480 (x2c_range_all (fun t => natAxpySp 384 21714 31 (transA2Tab.getD (t % 231) []) (h.getD (t / 231) []) (x2Tab o (t / 231) (t % 231))) 462 1 chkB_4_d462) (x2c_join _ 463 464 480 (x2c_range_all (fun t => natAxpySp 384 21714 31 (transA2Tab.getD (t % 231) []) (h.getD (t / 231) []) (x2Tab o (t / 231) (t % 231))) 463 1 chkB_4_d463) (x2c_join _ 464 465 480 (x2c_range_all (fun t => natAxpySp 384 21714 31 (transA2Tab.getD (t % 231) []) (h.getD (t / 231) []) (x2Tab o (t / 231) (t % 231))) 464 1 chkB_4_d464) (x2c_join _ 465 466 480 (x2c_range_all (fun t => natAxpySp 384 21714 31 (transA2Tab.getD (t % 231) []) (h.getD (t / 231) []) (x2Tab o (t / 231) (t % 231))) 465 1 chkB_4_d465) (x2c_join _ 466 467 480 (x2c_range_all (fun t => natAxpySp 384 21714 31 (transA2Tab.getD (t % 231) []) (h.getD (t / 231) []) (x2Tab o (t / 231) (t % 231))) 466 1 chkB_4_d466) (x2c_join _ 467 468 480 (x2c_range_all (fun t => natAxpySp 384 21714 31 (transA2Tab.getD (t % 231) []) (h.getD (t / 231) []) (x2Tab o (t / 231) (t % 231))) 467 1 chkB_4_d467) (x2c_join _ 468 469 480 (x2c_range_all (fun t => natAxpySp 384 21714 31 (transA2Tab.getD (t % 231) []) (h.getD (t / 231) []) (x2Tab o (t / 231) (t % 231))) 468 1 chkB_4_d468) (x2c_join _ 469 470 480 (x2c_range_all (fun t => natAxpySp 384 21714 31 (transA2Tab.getD (t % 231) []) (h.getD (t / 231) []) (x2Tab o (t / 231) (t % 231))) 469 1 chkB_4_d469) (x2c_join _ 470 471 480 (x2c_range_all (fun t => natAxpySp 384 21714 31 (transA2Tab.getD (t % 231) []) (h.getD (t / 231) []) (x2Tab o (t / 231) (t % 231))) 470 1 chkB_4_d470) (x2c_join _ 471 472 480 (x2c_range_all (fun t => natAxpySp 384 21714 31 (transA2Tab.getD (t % 231) []) (h.getD (t / 231) []) (x2Tab o (t / 231) (t % 231))) 471 1 chkB_4_d471) (x2c_join _ 472 473 480 (x2c_range_all (fun t => natAxpySp 384 21714 31 (transA2Tab.getD (t % 231) []) (h.getD (t / 231) []) (x2Tab o (t / 231) (t % 231))) 472 1 chkB_4_d472) (x2c_join _ 473 474 480 (x2c_range_all (fun t => natAxpySp 384 21714 31 (transA2Tab.getD (t % 231) []) (h.getD (t / 231) []) (x2Tab o (t / 231) (t % 231))) 473 1 chkB_4_d473) (x2c_join _ 474 475 480 (x2c_range_all (fun t => natAxpySp 384 21714 31 (transA2Tab.getD (t % 231) []) (h.getD (t / 231) []) (x2Tab o (t / 231) (t % 231))) 474 1 chkB_4_d474) (x2c_join _ 475 476 480 (x2c_range_all (fun t => natAxpySp 384 21714 31 (transA2Tab.getD (t % 231) []) (h.getD (t / 231) []) (x2Tab o (t / 231) (t % 231))) 475 1 chkB_4_d475) (x2c_join _ 476 477 480 (x2c_range_all (fun t => natAxpySp 384 21714 31 (transA2Tab.getD (t % 231) []) (h.getD (t / 231) []) (x2Tab o (t / 231) (t % 231))) 476 1 chkB_4_d476) (x2c_join _ 477 478 480 (x2c_range_all (fun t => natAxpySp 384 21714 31 (transA2Tab.getD (t % 231) []) (h.getD (t / 231) []) (x2Tab o (t / 231) (t % 231))) 477 1 chkB_4_d477) (x2c_join _ 478 479 480 (x2c_range_all (fun t => natAxpySp 384 21714 31 (transA2Tab.getD (t % 231) []) (h.getD (t / 231) []) (x2Tab o (t / 231) (t % 231))) 478 1 chkB_4_d478) (x2c_range_all (fun t => natAxpySp 384 21714 31 (transA2Tab.getD (t % 231) []) (h.getD (t / 231) []) (x2Tab o (t / 231) (t % 231))) 479 1 chkB_4_d479))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))


end ThreeCopyQutritWerner.X2.CoreA2g
