module

public import ThreeCopyQutritWerner.CertificateX2CoreA2gG
public import ThreeCopyQutritWerner.CertificateX2Trans
public import ThreeCopyQutritWerner.CertificateX2CoreBatchGen
public import ThreeCopyQutritWerner.CertificateX2CoreBatchFlat

@[expose] public section


/-! Batched core A2g: axis-2 stage, one output per declaration, flat indices 480..575. -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option exponentiation.threshold 1000000

namespace ThreeCopyQutritWerner.X2.CoreA2g
open ThreeCopyQutritWerner ThreeCopyQutritWerner.X2

theorem chkA_5_d480 : (List.range' 480 1).all (fun t => natAxpySp 384 21714 31 (transA2Tab.getD (t % 231) []) (f0.getD (t / 231) []) (x2Tab g (t / 231) (t % 231))) = true := by
  decide +kernel

theorem chkA_5_d481 : (List.range' 481 1).all (fun t => natAxpySp 384 21714 31 (transA2Tab.getD (t % 231) []) (f0.getD (t / 231) []) (x2Tab g (t / 231) (t % 231))) = true := by
  decide +kernel

theorem chkA_5_d482 : (List.range' 482 1).all (fun t => natAxpySp 384 21714 31 (transA2Tab.getD (t % 231) []) (f0.getD (t / 231) []) (x2Tab g (t / 231) (t % 231))) = true := by
  decide +kernel

theorem chkA_5_d483 : (List.range' 483 1).all (fun t => natAxpySp 384 21714 31 (transA2Tab.getD (t % 231) []) (f0.getD (t / 231) []) (x2Tab g (t / 231) (t % 231))) = true := by
  decide +kernel

theorem chkA_5_d484 : (List.range' 484 1).all (fun t => natAxpySp 384 21714 31 (transA2Tab.getD (t % 231) []) (f0.getD (t / 231) []) (x2Tab g (t / 231) (t % 231))) = true := by
  decide +kernel

theorem chkA_5_d485 : (List.range' 485 1).all (fun t => natAxpySp 384 21714 31 (transA2Tab.getD (t % 231) []) (f0.getD (t / 231) []) (x2Tab g (t / 231) (t % 231))) = true := by
  decide +kernel

theorem chkA_5_d486 : (List.range' 486 1).all (fun t => natAxpySp 384 21714 31 (transA2Tab.getD (t % 231) []) (f0.getD (t / 231) []) (x2Tab g (t / 231) (t % 231))) = true := by
  decide +kernel

theorem chkA_5_d487 : (List.range' 487 1).all (fun t => natAxpySp 384 21714 31 (transA2Tab.getD (t % 231) []) (f0.getD (t / 231) []) (x2Tab g (t / 231) (t % 231))) = true := by
  decide +kernel

theorem chkA_5_d488 : (List.range' 488 1).all (fun t => natAxpySp 384 21714 31 (transA2Tab.getD (t % 231) []) (f0.getD (t / 231) []) (x2Tab g (t / 231) (t % 231))) = true := by
  decide +kernel

theorem chkA_5_d489 : (List.range' 489 1).all (fun t => natAxpySp 384 21714 31 (transA2Tab.getD (t % 231) []) (f0.getD (t / 231) []) (x2Tab g (t / 231) (t % 231))) = true := by
  decide +kernel

theorem chkA_5_d490 : (List.range' 490 1).all (fun t => natAxpySp 384 21714 31 (transA2Tab.getD (t % 231) []) (f0.getD (t / 231) []) (x2Tab g (t / 231) (t % 231))) = true := by
  decide +kernel

theorem chkA_5_d491 : (List.range' 491 1).all (fun t => natAxpySp 384 21714 31 (transA2Tab.getD (t % 231) []) (f0.getD (t / 231) []) (x2Tab g (t / 231) (t % 231))) = true := by
  decide +kernel

theorem chkA_5_d492 : (List.range' 492 1).all (fun t => natAxpySp 384 21714 31 (transA2Tab.getD (t % 231) []) (f0.getD (t / 231) []) (x2Tab g (t / 231) (t % 231))) = true := by
  decide +kernel

theorem chkA_5_d493 : (List.range' 493 1).all (fun t => natAxpySp 384 21714 31 (transA2Tab.getD (t % 231) []) (f0.getD (t / 231) []) (x2Tab g (t / 231) (t % 231))) = true := by
  decide +kernel

theorem chkA_5_d494 : (List.range' 494 1).all (fun t => natAxpySp 384 21714 31 (transA2Tab.getD (t % 231) []) (f0.getD (t / 231) []) (x2Tab g (t / 231) (t % 231))) = true := by
  decide +kernel

theorem chkA_5_d495 : (List.range' 495 1).all (fun t => natAxpySp 384 21714 31 (transA2Tab.getD (t % 231) []) (f0.getD (t / 231) []) (x2Tab g (t / 231) (t % 231))) = true := by
  decide +kernel

theorem chkA_5_d496 : (List.range' 496 1).all (fun t => natAxpySp 384 21714 31 (transA2Tab.getD (t % 231) []) (f0.getD (t / 231) []) (x2Tab g (t / 231) (t % 231))) = true := by
  decide +kernel

theorem chkA_5_d497 : (List.range' 497 1).all (fun t => natAxpySp 384 21714 31 (transA2Tab.getD (t % 231) []) (f0.getD (t / 231) []) (x2Tab g (t / 231) (t % 231))) = true := by
  decide +kernel

theorem chkA_5_d498 : (List.range' 498 1).all (fun t => natAxpySp 384 21714 31 (transA2Tab.getD (t % 231) []) (f0.getD (t / 231) []) (x2Tab g (t / 231) (t % 231))) = true := by
  decide +kernel

theorem chkA_5_d499 : (List.range' 499 1).all (fun t => natAxpySp 384 21714 31 (transA2Tab.getD (t % 231) []) (f0.getD (t / 231) []) (x2Tab g (t / 231) (t % 231))) = true := by
  decide +kernel

theorem chkA_5_d500 : (List.range' 500 1).all (fun t => natAxpySp 384 21714 31 (transA2Tab.getD (t % 231) []) (f0.getD (t / 231) []) (x2Tab g (t / 231) (t % 231))) = true := by
  decide +kernel

theorem chkA_5_d501 : (List.range' 501 1).all (fun t => natAxpySp 384 21714 31 (transA2Tab.getD (t % 231) []) (f0.getD (t / 231) []) (x2Tab g (t / 231) (t % 231))) = true := by
  decide +kernel

theorem chkA_5_d502 : (List.range' 502 1).all (fun t => natAxpySp 384 21714 31 (transA2Tab.getD (t % 231) []) (f0.getD (t / 231) []) (x2Tab g (t / 231) (t % 231))) = true := by
  decide +kernel

theorem chkA_5_d503 : (List.range' 503 1).all (fun t => natAxpySp 384 21714 31 (transA2Tab.getD (t % 231) []) (f0.getD (t / 231) []) (x2Tab g (t / 231) (t % 231))) = true := by
  decide +kernel

theorem chkA_5_d504 : (List.range' 504 1).all (fun t => natAxpySp 384 21714 31 (transA2Tab.getD (t % 231) []) (f0.getD (t / 231) []) (x2Tab g (t / 231) (t % 231))) = true := by
  decide +kernel

theorem chkA_5_d505 : (List.range' 505 1).all (fun t => natAxpySp 384 21714 31 (transA2Tab.getD (t % 231) []) (f0.getD (t / 231) []) (x2Tab g (t / 231) (t % 231))) = true := by
  decide +kernel

theorem chkA_5_d506 : (List.range' 506 1).all (fun t => natAxpySp 384 21714 31 (transA2Tab.getD (t % 231) []) (f0.getD (t / 231) []) (x2Tab g (t / 231) (t % 231))) = true := by
  decide +kernel

theorem chkA_5_d507 : (List.range' 507 1).all (fun t => natAxpySp 384 21714 31 (transA2Tab.getD (t % 231) []) (f0.getD (t / 231) []) (x2Tab g (t / 231) (t % 231))) = true := by
  decide +kernel

theorem chkA_5_d508 : (List.range' 508 1).all (fun t => natAxpySp 384 21714 31 (transA2Tab.getD (t % 231) []) (f0.getD (t / 231) []) (x2Tab g (t / 231) (t % 231))) = true := by
  decide +kernel

theorem chkA_5_d509 : (List.range' 509 1).all (fun t => natAxpySp 384 21714 31 (transA2Tab.getD (t % 231) []) (f0.getD (t / 231) []) (x2Tab g (t / 231) (t % 231))) = true := by
  decide +kernel

theorem chkA_5_d510 : (List.range' 510 1).all (fun t => natAxpySp 384 21714 31 (transA2Tab.getD (t % 231) []) (f0.getD (t / 231) []) (x2Tab g (t / 231) (t % 231))) = true := by
  decide +kernel

theorem chkA_5_d511 : (List.range' 511 1).all (fun t => natAxpySp 384 21714 31 (transA2Tab.getD (t % 231) []) (f0.getD (t / 231) []) (x2Tab g (t / 231) (t % 231))) = true := by
  decide +kernel

theorem chkA_5_d512 : (List.range' 512 1).all (fun t => natAxpySp 384 21714 31 (transA2Tab.getD (t % 231) []) (f0.getD (t / 231) []) (x2Tab g (t / 231) (t % 231))) = true := by
  decide +kernel

theorem chkA_5_d513 : (List.range' 513 1).all (fun t => natAxpySp 384 21714 31 (transA2Tab.getD (t % 231) []) (f0.getD (t / 231) []) (x2Tab g (t / 231) (t % 231))) = true := by
  decide +kernel

theorem chkA_5_d514 : (List.range' 514 1).all (fun t => natAxpySp 384 21714 31 (transA2Tab.getD (t % 231) []) (f0.getD (t / 231) []) (x2Tab g (t / 231) (t % 231))) = true := by
  decide +kernel

theorem chkA_5_d515 : (List.range' 515 1).all (fun t => natAxpySp 384 21714 31 (transA2Tab.getD (t % 231) []) (f0.getD (t / 231) []) (x2Tab g (t / 231) (t % 231))) = true := by
  decide +kernel

theorem chkA_5_d516 : (List.range' 516 1).all (fun t => natAxpySp 384 21714 31 (transA2Tab.getD (t % 231) []) (f0.getD (t / 231) []) (x2Tab g (t / 231) (t % 231))) = true := by
  decide +kernel

theorem chkA_5_d517 : (List.range' 517 1).all (fun t => natAxpySp 384 21714 31 (transA2Tab.getD (t % 231) []) (f0.getD (t / 231) []) (x2Tab g (t / 231) (t % 231))) = true := by
  decide +kernel

theorem chkA_5_d518 : (List.range' 518 1).all (fun t => natAxpySp 384 21714 31 (transA2Tab.getD (t % 231) []) (f0.getD (t / 231) []) (x2Tab g (t / 231) (t % 231))) = true := by
  decide +kernel

theorem chkA_5_d519 : (List.range' 519 1).all (fun t => natAxpySp 384 21714 31 (transA2Tab.getD (t % 231) []) (f0.getD (t / 231) []) (x2Tab g (t / 231) (t % 231))) = true := by
  decide +kernel

theorem chkA_5_d520 : (List.range' 520 1).all (fun t => natAxpySp 384 21714 31 (transA2Tab.getD (t % 231) []) (f0.getD (t / 231) []) (x2Tab g (t / 231) (t % 231))) = true := by
  decide +kernel

theorem chkA_5_d521 : (List.range' 521 1).all (fun t => natAxpySp 384 21714 31 (transA2Tab.getD (t % 231) []) (f0.getD (t / 231) []) (x2Tab g (t / 231) (t % 231))) = true := by
  decide +kernel

theorem chkA_5_d522 : (List.range' 522 1).all (fun t => natAxpySp 384 21714 31 (transA2Tab.getD (t % 231) []) (f0.getD (t / 231) []) (x2Tab g (t / 231) (t % 231))) = true := by
  decide +kernel

theorem chkA_5_d523 : (List.range' 523 1).all (fun t => natAxpySp 384 21714 31 (transA2Tab.getD (t % 231) []) (f0.getD (t / 231) []) (x2Tab g (t / 231) (t % 231))) = true := by
  decide +kernel

theorem chkA_5_d524 : (List.range' 524 1).all (fun t => natAxpySp 384 21714 31 (transA2Tab.getD (t % 231) []) (f0.getD (t / 231) []) (x2Tab g (t / 231) (t % 231))) = true := by
  decide +kernel

theorem chkA_5_d525 : (List.range' 525 1).all (fun t => natAxpySp 384 21714 31 (transA2Tab.getD (t % 231) []) (f0.getD (t / 231) []) (x2Tab g (t / 231) (t % 231))) = true := by
  decide +kernel

theorem chkA_5_d526 : (List.range' 526 1).all (fun t => natAxpySp 384 21714 31 (transA2Tab.getD (t % 231) []) (f0.getD (t / 231) []) (x2Tab g (t / 231) (t % 231))) = true := by
  decide +kernel

theorem chkA_5_d527 : (List.range' 527 1).all (fun t => natAxpySp 384 21714 31 (transA2Tab.getD (t % 231) []) (f0.getD (t / 231) []) (x2Tab g (t / 231) (t % 231))) = true := by
  decide +kernel

theorem chkA_5_d528 : (List.range' 528 1).all (fun t => natAxpySp 384 21714 31 (transA2Tab.getD (t % 231) []) (f0.getD (t / 231) []) (x2Tab g (t / 231) (t % 231))) = true := by
  decide +kernel

theorem chkA_5_d529 : (List.range' 529 1).all (fun t => natAxpySp 384 21714 31 (transA2Tab.getD (t % 231) []) (f0.getD (t / 231) []) (x2Tab g (t / 231) (t % 231))) = true := by
  decide +kernel

theorem chkA_5_d530 : (List.range' 530 1).all (fun t => natAxpySp 384 21714 31 (transA2Tab.getD (t % 231) []) (f0.getD (t / 231) []) (x2Tab g (t / 231) (t % 231))) = true := by
  decide +kernel

theorem chkA_5_d531 : (List.range' 531 1).all (fun t => natAxpySp 384 21714 31 (transA2Tab.getD (t % 231) []) (f0.getD (t / 231) []) (x2Tab g (t / 231) (t % 231))) = true := by
  decide +kernel

theorem chkA_5_d532 : (List.range' 532 1).all (fun t => natAxpySp 384 21714 31 (transA2Tab.getD (t % 231) []) (f0.getD (t / 231) []) (x2Tab g (t / 231) (t % 231))) = true := by
  decide +kernel

theorem chkA_5_d533 : (List.range' 533 1).all (fun t => natAxpySp 384 21714 31 (transA2Tab.getD (t % 231) []) (f0.getD (t / 231) []) (x2Tab g (t / 231) (t % 231))) = true := by
  decide +kernel

theorem chkA_5_d534 : (List.range' 534 1).all (fun t => natAxpySp 384 21714 31 (transA2Tab.getD (t % 231) []) (f0.getD (t / 231) []) (x2Tab g (t / 231) (t % 231))) = true := by
  decide +kernel

theorem chkA_5_d535 : (List.range' 535 1).all (fun t => natAxpySp 384 21714 31 (transA2Tab.getD (t % 231) []) (f0.getD (t / 231) []) (x2Tab g (t / 231) (t % 231))) = true := by
  decide +kernel

theorem chkA_5_d536 : (List.range' 536 1).all (fun t => natAxpySp 384 21714 31 (transA2Tab.getD (t % 231) []) (f0.getD (t / 231) []) (x2Tab g (t / 231) (t % 231))) = true := by
  decide +kernel

theorem chkA_5_d537 : (List.range' 537 1).all (fun t => natAxpySp 384 21714 31 (transA2Tab.getD (t % 231) []) (f0.getD (t / 231) []) (x2Tab g (t / 231) (t % 231))) = true := by
  decide +kernel

theorem chkA_5_d538 : (List.range' 538 1).all (fun t => natAxpySp 384 21714 31 (transA2Tab.getD (t % 231) []) (f0.getD (t / 231) []) (x2Tab g (t / 231) (t % 231))) = true := by
  decide +kernel

theorem chkA_5_d539 : (List.range' 539 1).all (fun t => natAxpySp 384 21714 31 (transA2Tab.getD (t % 231) []) (f0.getD (t / 231) []) (x2Tab g (t / 231) (t % 231))) = true := by
  decide +kernel

theorem chkA_5_d540 : (List.range' 540 1).all (fun t => natAxpySp 384 21714 31 (transA2Tab.getD (t % 231) []) (f0.getD (t / 231) []) (x2Tab g (t / 231) (t % 231))) = true := by
  decide +kernel

theorem chkA_5_d541 : (List.range' 541 1).all (fun t => natAxpySp 384 21714 31 (transA2Tab.getD (t % 231) []) (f0.getD (t / 231) []) (x2Tab g (t / 231) (t % 231))) = true := by
  decide +kernel

theorem chkA_5_d542 : (List.range' 542 1).all (fun t => natAxpySp 384 21714 31 (transA2Tab.getD (t % 231) []) (f0.getD (t / 231) []) (x2Tab g (t / 231) (t % 231))) = true := by
  decide +kernel

theorem chkA_5_d543 : (List.range' 543 1).all (fun t => natAxpySp 384 21714 31 (transA2Tab.getD (t % 231) []) (f0.getD (t / 231) []) (x2Tab g (t / 231) (t % 231))) = true := by
  decide +kernel

theorem chkA_5_d544 : (List.range' 544 1).all (fun t => natAxpySp 384 21714 31 (transA2Tab.getD (t % 231) []) (f0.getD (t / 231) []) (x2Tab g (t / 231) (t % 231))) = true := by
  decide +kernel

theorem chkA_5_d545 : (List.range' 545 1).all (fun t => natAxpySp 384 21714 31 (transA2Tab.getD (t % 231) []) (f0.getD (t / 231) []) (x2Tab g (t / 231) (t % 231))) = true := by
  decide +kernel

theorem chkA_5_d546 : (List.range' 546 1).all (fun t => natAxpySp 384 21714 31 (transA2Tab.getD (t % 231) []) (f0.getD (t / 231) []) (x2Tab g (t / 231) (t % 231))) = true := by
  decide +kernel

theorem chkA_5_d547 : (List.range' 547 1).all (fun t => natAxpySp 384 21714 31 (transA2Tab.getD (t % 231) []) (f0.getD (t / 231) []) (x2Tab g (t / 231) (t % 231))) = true := by
  decide +kernel

theorem chkA_5_d548 : (List.range' 548 1).all (fun t => natAxpySp 384 21714 31 (transA2Tab.getD (t % 231) []) (f0.getD (t / 231) []) (x2Tab g (t / 231) (t % 231))) = true := by
  decide +kernel

theorem chkA_5_d549 : (List.range' 549 1).all (fun t => natAxpySp 384 21714 31 (transA2Tab.getD (t % 231) []) (f0.getD (t / 231) []) (x2Tab g (t / 231) (t % 231))) = true := by
  decide +kernel

theorem chkA_5_d550 : (List.range' 550 1).all (fun t => natAxpySp 384 21714 31 (transA2Tab.getD (t % 231) []) (f0.getD (t / 231) []) (x2Tab g (t / 231) (t % 231))) = true := by
  decide +kernel

theorem chkA_5_d551 : (List.range' 551 1).all (fun t => natAxpySp 384 21714 31 (transA2Tab.getD (t % 231) []) (f0.getD (t / 231) []) (x2Tab g (t / 231) (t % 231))) = true := by
  decide +kernel

theorem chkA_5_d552 : (List.range' 552 1).all (fun t => natAxpySp 384 21714 31 (transA2Tab.getD (t % 231) []) (f0.getD (t / 231) []) (x2Tab g (t / 231) (t % 231))) = true := by
  decide +kernel

theorem chkA_5_d553 : (List.range' 553 1).all (fun t => natAxpySp 384 21714 31 (transA2Tab.getD (t % 231) []) (f0.getD (t / 231) []) (x2Tab g (t / 231) (t % 231))) = true := by
  decide +kernel

theorem chkA_5_d554 : (List.range' 554 1).all (fun t => natAxpySp 384 21714 31 (transA2Tab.getD (t % 231) []) (f0.getD (t / 231) []) (x2Tab g (t / 231) (t % 231))) = true := by
  decide +kernel

theorem chkA_5_d555 : (List.range' 555 1).all (fun t => natAxpySp 384 21714 31 (transA2Tab.getD (t % 231) []) (f0.getD (t / 231) []) (x2Tab g (t / 231) (t % 231))) = true := by
  decide +kernel

theorem chkA_5_d556 : (List.range' 556 1).all (fun t => natAxpySp 384 21714 31 (transA2Tab.getD (t % 231) []) (f0.getD (t / 231) []) (x2Tab g (t / 231) (t % 231))) = true := by
  decide +kernel

theorem chkA_5_d557 : (List.range' 557 1).all (fun t => natAxpySp 384 21714 31 (transA2Tab.getD (t % 231) []) (f0.getD (t / 231) []) (x2Tab g (t / 231) (t % 231))) = true := by
  decide +kernel

theorem chkA_5_d558 : (List.range' 558 1).all (fun t => natAxpySp 384 21714 31 (transA2Tab.getD (t % 231) []) (f0.getD (t / 231) []) (x2Tab g (t / 231) (t % 231))) = true := by
  decide +kernel

theorem chkA_5_d559 : (List.range' 559 1).all (fun t => natAxpySp 384 21714 31 (transA2Tab.getD (t % 231) []) (f0.getD (t / 231) []) (x2Tab g (t / 231) (t % 231))) = true := by
  decide +kernel

theorem chkA_5_d560 : (List.range' 560 1).all (fun t => natAxpySp 384 21714 31 (transA2Tab.getD (t % 231) []) (f0.getD (t / 231) []) (x2Tab g (t / 231) (t % 231))) = true := by
  decide +kernel

theorem chkA_5_d561 : (List.range' 561 1).all (fun t => natAxpySp 384 21714 31 (transA2Tab.getD (t % 231) []) (f0.getD (t / 231) []) (x2Tab g (t / 231) (t % 231))) = true := by
  decide +kernel

theorem chkA_5_d562 : (List.range' 562 1).all (fun t => natAxpySp 384 21714 31 (transA2Tab.getD (t % 231) []) (f0.getD (t / 231) []) (x2Tab g (t / 231) (t % 231))) = true := by
  decide +kernel

theorem chkA_5_d563 : (List.range' 563 1).all (fun t => natAxpySp 384 21714 31 (transA2Tab.getD (t % 231) []) (f0.getD (t / 231) []) (x2Tab g (t / 231) (t % 231))) = true := by
  decide +kernel

theorem chkA_5_d564 : (List.range' 564 1).all (fun t => natAxpySp 384 21714 31 (transA2Tab.getD (t % 231) []) (f0.getD (t / 231) []) (x2Tab g (t / 231) (t % 231))) = true := by
  decide +kernel

theorem chkA_5_d565 : (List.range' 565 1).all (fun t => natAxpySp 384 21714 31 (transA2Tab.getD (t % 231) []) (f0.getD (t / 231) []) (x2Tab g (t / 231) (t % 231))) = true := by
  decide +kernel

theorem chkA_5_d566 : (List.range' 566 1).all (fun t => natAxpySp 384 21714 31 (transA2Tab.getD (t % 231) []) (f0.getD (t / 231) []) (x2Tab g (t / 231) (t % 231))) = true := by
  decide +kernel

theorem chkA_5_d567 : (List.range' 567 1).all (fun t => natAxpySp 384 21714 31 (transA2Tab.getD (t % 231) []) (f0.getD (t / 231) []) (x2Tab g (t / 231) (t % 231))) = true := by
  decide +kernel

theorem chkA_5_d568 : (List.range' 568 1).all (fun t => natAxpySp 384 21714 31 (transA2Tab.getD (t % 231) []) (f0.getD (t / 231) []) (x2Tab g (t / 231) (t % 231))) = true := by
  decide +kernel

theorem chkA_5_d569 : (List.range' 569 1).all (fun t => natAxpySp 384 21714 31 (transA2Tab.getD (t % 231) []) (f0.getD (t / 231) []) (x2Tab g (t / 231) (t % 231))) = true := by
  decide +kernel

theorem chkA_5_d570 : (List.range' 570 1).all (fun t => natAxpySp 384 21714 31 (transA2Tab.getD (t % 231) []) (f0.getD (t / 231) []) (x2Tab g (t / 231) (t % 231))) = true := by
  decide +kernel

theorem chkA_5_d571 : (List.range' 571 1).all (fun t => natAxpySp 384 21714 31 (transA2Tab.getD (t % 231) []) (f0.getD (t / 231) []) (x2Tab g (t / 231) (t % 231))) = true := by
  decide +kernel

theorem chkA_5_d572 : (List.range' 572 1).all (fun t => natAxpySp 384 21714 31 (transA2Tab.getD (t % 231) []) (f0.getD (t / 231) []) (x2Tab g (t / 231) (t % 231))) = true := by
  decide +kernel

theorem chkA_5_d573 : (List.range' 573 1).all (fun t => natAxpySp 384 21714 31 (transA2Tab.getD (t % 231) []) (f0.getD (t / 231) []) (x2Tab g (t / 231) (t % 231))) = true := by
  decide +kernel

theorem chkA_5_d574 : (List.range' 574 1).all (fun t => natAxpySp 384 21714 31 (transA2Tab.getD (t % 231) []) (f0.getD (t / 231) []) (x2Tab g (t / 231) (t % 231))) = true := by
  decide +kernel

theorem chkA_5_d575 : (List.range' 575 1).all (fun t => natAxpySp 384 21714 31 (transA2Tab.getD (t % 231) []) (f0.getD (t / 231) []) (x2Tab g (t / 231) (t % 231))) = true := by
  decide +kernel

theorem chkA_5 : ∀ t, 480 ≤ t → t < 576 → (natAxpySp 384 21714 31 (transA2Tab.getD (t % 231) []) (f0.getD (t / 231) []) (x2Tab g (t / 231) (t % 231))) = true := by
  exact (x2c_join _ 480 481 576 (x2c_range_all (fun t => natAxpySp 384 21714 31 (transA2Tab.getD (t % 231) []) (f0.getD (t / 231) []) (x2Tab g (t / 231) (t % 231))) 480 1 chkA_5_d480) (x2c_join _ 481 482 576 (x2c_range_all (fun t => natAxpySp 384 21714 31 (transA2Tab.getD (t % 231) []) (f0.getD (t / 231) []) (x2Tab g (t / 231) (t % 231))) 481 1 chkA_5_d481) (x2c_join _ 482 483 576 (x2c_range_all (fun t => natAxpySp 384 21714 31 (transA2Tab.getD (t % 231) []) (f0.getD (t / 231) []) (x2Tab g (t / 231) (t % 231))) 482 1 chkA_5_d482) (x2c_join _ 483 484 576 (x2c_range_all (fun t => natAxpySp 384 21714 31 (transA2Tab.getD (t % 231) []) (f0.getD (t / 231) []) (x2Tab g (t / 231) (t % 231))) 483 1 chkA_5_d483) (x2c_join _ 484 485 576 (x2c_range_all (fun t => natAxpySp 384 21714 31 (transA2Tab.getD (t % 231) []) (f0.getD (t / 231) []) (x2Tab g (t / 231) (t % 231))) 484 1 chkA_5_d484) (x2c_join _ 485 486 576 (x2c_range_all (fun t => natAxpySp 384 21714 31 (transA2Tab.getD (t % 231) []) (f0.getD (t / 231) []) (x2Tab g (t / 231) (t % 231))) 485 1 chkA_5_d485) (x2c_join _ 486 487 576 (x2c_range_all (fun t => natAxpySp 384 21714 31 (transA2Tab.getD (t % 231) []) (f0.getD (t / 231) []) (x2Tab g (t / 231) (t % 231))) 486 1 chkA_5_d486) (x2c_join _ 487 488 576 (x2c_range_all (fun t => natAxpySp 384 21714 31 (transA2Tab.getD (t % 231) []) (f0.getD (t / 231) []) (x2Tab g (t / 231) (t % 231))) 487 1 chkA_5_d487) (x2c_join _ 488 489 576 (x2c_range_all (fun t => natAxpySp 384 21714 31 (transA2Tab.getD (t % 231) []) (f0.getD (t / 231) []) (x2Tab g (t / 231) (t % 231))) 488 1 chkA_5_d488) (x2c_join _ 489 490 576 (x2c_range_all (fun t => natAxpySp 384 21714 31 (transA2Tab.getD (t % 231) []) (f0.getD (t / 231) []) (x2Tab g (t / 231) (t % 231))) 489 1 chkA_5_d489) (x2c_join _ 490 491 576 (x2c_range_all (fun t => natAxpySp 384 21714 31 (transA2Tab.getD (t % 231) []) (f0.getD (t / 231) []) (x2Tab g (t / 231) (t % 231))) 490 1 chkA_5_d490) (x2c_join _ 491 492 576 (x2c_range_all (fun t => natAxpySp 384 21714 31 (transA2Tab.getD (t % 231) []) (f0.getD (t / 231) []) (x2Tab g (t / 231) (t % 231))) 491 1 chkA_5_d491) (x2c_join _ 492 493 576 (x2c_range_all (fun t => natAxpySp 384 21714 31 (transA2Tab.getD (t % 231) []) (f0.getD (t / 231) []) (x2Tab g (t / 231) (t % 231))) 492 1 chkA_5_d492) (x2c_join _ 493 494 576 (x2c_range_all (fun t => natAxpySp 384 21714 31 (transA2Tab.getD (t % 231) []) (f0.getD (t / 231) []) (x2Tab g (t / 231) (t % 231))) 493 1 chkA_5_d493) (x2c_join _ 494 495 576 (x2c_range_all (fun t => natAxpySp 384 21714 31 (transA2Tab.getD (t % 231) []) (f0.getD (t / 231) []) (x2Tab g (t / 231) (t % 231))) 494 1 chkA_5_d494) (x2c_join _ 495 496 576 (x2c_range_all (fun t => natAxpySp 384 21714 31 (transA2Tab.getD (t % 231) []) (f0.getD (t / 231) []) (x2Tab g (t / 231) (t % 231))) 495 1 chkA_5_d495) (x2c_join _ 496 497 576 (x2c_range_all (fun t => natAxpySp 384 21714 31 (transA2Tab.getD (t % 231) []) (f0.getD (t / 231) []) (x2Tab g (t / 231) (t % 231))) 496 1 chkA_5_d496) (x2c_join _ 497 498 576 (x2c_range_all (fun t => natAxpySp 384 21714 31 (transA2Tab.getD (t % 231) []) (f0.getD (t / 231) []) (x2Tab g (t / 231) (t % 231))) 497 1 chkA_5_d497) (x2c_join _ 498 499 576 (x2c_range_all (fun t => natAxpySp 384 21714 31 (transA2Tab.getD (t % 231) []) (f0.getD (t / 231) []) (x2Tab g (t / 231) (t % 231))) 498 1 chkA_5_d498) (x2c_join _ 499 500 576 (x2c_range_all (fun t => natAxpySp 384 21714 31 (transA2Tab.getD (t % 231) []) (f0.getD (t / 231) []) (x2Tab g (t / 231) (t % 231))) 499 1 chkA_5_d499) (x2c_join _ 500 501 576 (x2c_range_all (fun t => natAxpySp 384 21714 31 (transA2Tab.getD (t % 231) []) (f0.getD (t / 231) []) (x2Tab g (t / 231) (t % 231))) 500 1 chkA_5_d500) (x2c_join _ 501 502 576 (x2c_range_all (fun t => natAxpySp 384 21714 31 (transA2Tab.getD (t % 231) []) (f0.getD (t / 231) []) (x2Tab g (t / 231) (t % 231))) 501 1 chkA_5_d501) (x2c_join _ 502 503 576 (x2c_range_all (fun t => natAxpySp 384 21714 31 (transA2Tab.getD (t % 231) []) (f0.getD (t / 231) []) (x2Tab g (t / 231) (t % 231))) 502 1 chkA_5_d502) (x2c_join _ 503 504 576 (x2c_range_all (fun t => natAxpySp 384 21714 31 (transA2Tab.getD (t % 231) []) (f0.getD (t / 231) []) (x2Tab g (t / 231) (t % 231))) 503 1 chkA_5_d503) (x2c_join _ 504 505 576 (x2c_range_all (fun t => natAxpySp 384 21714 31 (transA2Tab.getD (t % 231) []) (f0.getD (t / 231) []) (x2Tab g (t / 231) (t % 231))) 504 1 chkA_5_d504) (x2c_join _ 505 506 576 (x2c_range_all (fun t => natAxpySp 384 21714 31 (transA2Tab.getD (t % 231) []) (f0.getD (t / 231) []) (x2Tab g (t / 231) (t % 231))) 505 1 chkA_5_d505) (x2c_join _ 506 507 576 (x2c_range_all (fun t => natAxpySp 384 21714 31 (transA2Tab.getD (t % 231) []) (f0.getD (t / 231) []) (x2Tab g (t / 231) (t % 231))) 506 1 chkA_5_d506) (x2c_join _ 507 508 576 (x2c_range_all (fun t => natAxpySp 384 21714 31 (transA2Tab.getD (t % 231) []) (f0.getD (t / 231) []) (x2Tab g (t / 231) (t % 231))) 507 1 chkA_5_d507) (x2c_join _ 508 509 576 (x2c_range_all (fun t => natAxpySp 384 21714 31 (transA2Tab.getD (t % 231) []) (f0.getD (t / 231) []) (x2Tab g (t / 231) (t % 231))) 508 1 chkA_5_d508) (x2c_join _ 509 510 576 (x2c_range_all (fun t => natAxpySp 384 21714 31 (transA2Tab.getD (t % 231) []) (f0.getD (t / 231) []) (x2Tab g (t / 231) (t % 231))) 509 1 chkA_5_d509) (x2c_join _ 510 511 576 (x2c_range_all (fun t => natAxpySp 384 21714 31 (transA2Tab.getD (t % 231) []) (f0.getD (t / 231) []) (x2Tab g (t / 231) (t % 231))) 510 1 chkA_5_d510) (x2c_join _ 511 512 576 (x2c_range_all (fun t => natAxpySp 384 21714 31 (transA2Tab.getD (t % 231) []) (f0.getD (t / 231) []) (x2Tab g (t / 231) (t % 231))) 511 1 chkA_5_d511) (x2c_join _ 512 513 576 (x2c_range_all (fun t => natAxpySp 384 21714 31 (transA2Tab.getD (t % 231) []) (f0.getD (t / 231) []) (x2Tab g (t / 231) (t % 231))) 512 1 chkA_5_d512) (x2c_join _ 513 514 576 (x2c_range_all (fun t => natAxpySp 384 21714 31 (transA2Tab.getD (t % 231) []) (f0.getD (t / 231) []) (x2Tab g (t / 231) (t % 231))) 513 1 chkA_5_d513) (x2c_join _ 514 515 576 (x2c_range_all (fun t => natAxpySp 384 21714 31 (transA2Tab.getD (t % 231) []) (f0.getD (t / 231) []) (x2Tab g (t / 231) (t % 231))) 514 1 chkA_5_d514) (x2c_join _ 515 516 576 (x2c_range_all (fun t => natAxpySp 384 21714 31 (transA2Tab.getD (t % 231) []) (f0.getD (t / 231) []) (x2Tab g (t / 231) (t % 231))) 515 1 chkA_5_d515) (x2c_join _ 516 517 576 (x2c_range_all (fun t => natAxpySp 384 21714 31 (transA2Tab.getD (t % 231) []) (f0.getD (t / 231) []) (x2Tab g (t / 231) (t % 231))) 516 1 chkA_5_d516) (x2c_join _ 517 518 576 (x2c_range_all (fun t => natAxpySp 384 21714 31 (transA2Tab.getD (t % 231) []) (f0.getD (t / 231) []) (x2Tab g (t / 231) (t % 231))) 517 1 chkA_5_d517) (x2c_join _ 518 519 576 (x2c_range_all (fun t => natAxpySp 384 21714 31 (transA2Tab.getD (t % 231) []) (f0.getD (t / 231) []) (x2Tab g (t / 231) (t % 231))) 518 1 chkA_5_d518) (x2c_join _ 519 520 576 (x2c_range_all (fun t => natAxpySp 384 21714 31 (transA2Tab.getD (t % 231) []) (f0.getD (t / 231) []) (x2Tab g (t / 231) (t % 231))) 519 1 chkA_5_d519) (x2c_join _ 520 521 576 (x2c_range_all (fun t => natAxpySp 384 21714 31 (transA2Tab.getD (t % 231) []) (f0.getD (t / 231) []) (x2Tab g (t / 231) (t % 231))) 520 1 chkA_5_d520) (x2c_join _ 521 522 576 (x2c_range_all (fun t => natAxpySp 384 21714 31 (transA2Tab.getD (t % 231) []) (f0.getD (t / 231) []) (x2Tab g (t / 231) (t % 231))) 521 1 chkA_5_d521) (x2c_join _ 522 523 576 (x2c_range_all (fun t => natAxpySp 384 21714 31 (transA2Tab.getD (t % 231) []) (f0.getD (t / 231) []) (x2Tab g (t / 231) (t % 231))) 522 1 chkA_5_d522) (x2c_join _ 523 524 576 (x2c_range_all (fun t => natAxpySp 384 21714 31 (transA2Tab.getD (t % 231) []) (f0.getD (t / 231) []) (x2Tab g (t / 231) (t % 231))) 523 1 chkA_5_d523) (x2c_join _ 524 525 576 (x2c_range_all (fun t => natAxpySp 384 21714 31 (transA2Tab.getD (t % 231) []) (f0.getD (t / 231) []) (x2Tab g (t / 231) (t % 231))) 524 1 chkA_5_d524) (x2c_join _ 525 526 576 (x2c_range_all (fun t => natAxpySp 384 21714 31 (transA2Tab.getD (t % 231) []) (f0.getD (t / 231) []) (x2Tab g (t / 231) (t % 231))) 525 1 chkA_5_d525) (x2c_join _ 526 527 576 (x2c_range_all (fun t => natAxpySp 384 21714 31 (transA2Tab.getD (t % 231) []) (f0.getD (t / 231) []) (x2Tab g (t / 231) (t % 231))) 526 1 chkA_5_d526) (x2c_join _ 527 528 576 (x2c_range_all (fun t => natAxpySp 384 21714 31 (transA2Tab.getD (t % 231) []) (f0.getD (t / 231) []) (x2Tab g (t / 231) (t % 231))) 527 1 chkA_5_d527) (x2c_join _ 528 529 576 (x2c_range_all (fun t => natAxpySp 384 21714 31 (transA2Tab.getD (t % 231) []) (f0.getD (t / 231) []) (x2Tab g (t / 231) (t % 231))) 528 1 chkA_5_d528) (x2c_join _ 529 530 576 (x2c_range_all (fun t => natAxpySp 384 21714 31 (transA2Tab.getD (t % 231) []) (f0.getD (t / 231) []) (x2Tab g (t / 231) (t % 231))) 529 1 chkA_5_d529) (x2c_join _ 530 531 576 (x2c_range_all (fun t => natAxpySp 384 21714 31 (transA2Tab.getD (t % 231) []) (f0.getD (t / 231) []) (x2Tab g (t / 231) (t % 231))) 530 1 chkA_5_d530) (x2c_join _ 531 532 576 (x2c_range_all (fun t => natAxpySp 384 21714 31 (transA2Tab.getD (t % 231) []) (f0.getD (t / 231) []) (x2Tab g (t / 231) (t % 231))) 531 1 chkA_5_d531) (x2c_join _ 532 533 576 (x2c_range_all (fun t => natAxpySp 384 21714 31 (transA2Tab.getD (t % 231) []) (f0.getD (t / 231) []) (x2Tab g (t / 231) (t % 231))) 532 1 chkA_5_d532) (x2c_join _ 533 534 576 (x2c_range_all (fun t => natAxpySp 384 21714 31 (transA2Tab.getD (t % 231) []) (f0.getD (t / 231) []) (x2Tab g (t / 231) (t % 231))) 533 1 chkA_5_d533) (x2c_join _ 534 535 576 (x2c_range_all (fun t => natAxpySp 384 21714 31 (transA2Tab.getD (t % 231) []) (f0.getD (t / 231) []) (x2Tab g (t / 231) (t % 231))) 534 1 chkA_5_d534) (x2c_join _ 535 536 576 (x2c_range_all (fun t => natAxpySp 384 21714 31 (transA2Tab.getD (t % 231) []) (f0.getD (t / 231) []) (x2Tab g (t / 231) (t % 231))) 535 1 chkA_5_d535) (x2c_join _ 536 537 576 (x2c_range_all (fun t => natAxpySp 384 21714 31 (transA2Tab.getD (t % 231) []) (f0.getD (t / 231) []) (x2Tab g (t / 231) (t % 231))) 536 1 chkA_5_d536) (x2c_join _ 537 538 576 (x2c_range_all (fun t => natAxpySp 384 21714 31 (transA2Tab.getD (t % 231) []) (f0.getD (t / 231) []) (x2Tab g (t / 231) (t % 231))) 537 1 chkA_5_d537) (x2c_join _ 538 539 576 (x2c_range_all (fun t => natAxpySp 384 21714 31 (transA2Tab.getD (t % 231) []) (f0.getD (t / 231) []) (x2Tab g (t / 231) (t % 231))) 538 1 chkA_5_d538) (x2c_join _ 539 540 576 (x2c_range_all (fun t => natAxpySp 384 21714 31 (transA2Tab.getD (t % 231) []) (f0.getD (t / 231) []) (x2Tab g (t / 231) (t % 231))) 539 1 chkA_5_d539) (x2c_join _ 540 541 576 (x2c_range_all (fun t => natAxpySp 384 21714 31 (transA2Tab.getD (t % 231) []) (f0.getD (t / 231) []) (x2Tab g (t / 231) (t % 231))) 540 1 chkA_5_d540) (x2c_join _ 541 542 576 (x2c_range_all (fun t => natAxpySp 384 21714 31 (transA2Tab.getD (t % 231) []) (f0.getD (t / 231) []) (x2Tab g (t / 231) (t % 231))) 541 1 chkA_5_d541) (x2c_join _ 542 543 576 (x2c_range_all (fun t => natAxpySp 384 21714 31 (transA2Tab.getD (t % 231) []) (f0.getD (t / 231) []) (x2Tab g (t / 231) (t % 231))) 542 1 chkA_5_d542) (x2c_join _ 543 544 576 (x2c_range_all (fun t => natAxpySp 384 21714 31 (transA2Tab.getD (t % 231) []) (f0.getD (t / 231) []) (x2Tab g (t / 231) (t % 231))) 543 1 chkA_5_d543) (x2c_join _ 544 545 576 (x2c_range_all (fun t => natAxpySp 384 21714 31 (transA2Tab.getD (t % 231) []) (f0.getD (t / 231) []) (x2Tab g (t / 231) (t % 231))) 544 1 chkA_5_d544) (x2c_join _ 545 546 576 (x2c_range_all (fun t => natAxpySp 384 21714 31 (transA2Tab.getD (t % 231) []) (f0.getD (t / 231) []) (x2Tab g (t / 231) (t % 231))) 545 1 chkA_5_d545) (x2c_join _ 546 547 576 (x2c_range_all (fun t => natAxpySp 384 21714 31 (transA2Tab.getD (t % 231) []) (f0.getD (t / 231) []) (x2Tab g (t / 231) (t % 231))) 546 1 chkA_5_d546) (x2c_join _ 547 548 576 (x2c_range_all (fun t => natAxpySp 384 21714 31 (transA2Tab.getD (t % 231) []) (f0.getD (t / 231) []) (x2Tab g (t / 231) (t % 231))) 547 1 chkA_5_d547) (x2c_join _ 548 549 576 (x2c_range_all (fun t => natAxpySp 384 21714 31 (transA2Tab.getD (t % 231) []) (f0.getD (t / 231) []) (x2Tab g (t / 231) (t % 231))) 548 1 chkA_5_d548) (x2c_join _ 549 550 576 (x2c_range_all (fun t => natAxpySp 384 21714 31 (transA2Tab.getD (t % 231) []) (f0.getD (t / 231) []) (x2Tab g (t / 231) (t % 231))) 549 1 chkA_5_d549) (x2c_join _ 550 551 576 (x2c_range_all (fun t => natAxpySp 384 21714 31 (transA2Tab.getD (t % 231) []) (f0.getD (t / 231) []) (x2Tab g (t / 231) (t % 231))) 550 1 chkA_5_d550) (x2c_join _ 551 552 576 (x2c_range_all (fun t => natAxpySp 384 21714 31 (transA2Tab.getD (t % 231) []) (f0.getD (t / 231) []) (x2Tab g (t / 231) (t % 231))) 551 1 chkA_5_d551) (x2c_join _ 552 553 576 (x2c_range_all (fun t => natAxpySp 384 21714 31 (transA2Tab.getD (t % 231) []) (f0.getD (t / 231) []) (x2Tab g (t / 231) (t % 231))) 552 1 chkA_5_d552) (x2c_join _ 553 554 576 (x2c_range_all (fun t => natAxpySp 384 21714 31 (transA2Tab.getD (t % 231) []) (f0.getD (t / 231) []) (x2Tab g (t / 231) (t % 231))) 553 1 chkA_5_d553) (x2c_join _ 554 555 576 (x2c_range_all (fun t => natAxpySp 384 21714 31 (transA2Tab.getD (t % 231) []) (f0.getD (t / 231) []) (x2Tab g (t / 231) (t % 231))) 554 1 chkA_5_d554) (x2c_join _ 555 556 576 (x2c_range_all (fun t => natAxpySp 384 21714 31 (transA2Tab.getD (t % 231) []) (f0.getD (t / 231) []) (x2Tab g (t / 231) (t % 231))) 555 1 chkA_5_d555) (x2c_join _ 556 557 576 (x2c_range_all (fun t => natAxpySp 384 21714 31 (transA2Tab.getD (t % 231) []) (f0.getD (t / 231) []) (x2Tab g (t / 231) (t % 231))) 556 1 chkA_5_d556) (x2c_join _ 557 558 576 (x2c_range_all (fun t => natAxpySp 384 21714 31 (transA2Tab.getD (t % 231) []) (f0.getD (t / 231) []) (x2Tab g (t / 231) (t % 231))) 557 1 chkA_5_d557) (x2c_join _ 558 559 576 (x2c_range_all (fun t => natAxpySp 384 21714 31 (transA2Tab.getD (t % 231) []) (f0.getD (t / 231) []) (x2Tab g (t / 231) (t % 231))) 558 1 chkA_5_d558) (x2c_join _ 559 560 576 (x2c_range_all (fun t => natAxpySp 384 21714 31 (transA2Tab.getD (t % 231) []) (f0.getD (t / 231) []) (x2Tab g (t / 231) (t % 231))) 559 1 chkA_5_d559) (x2c_join _ 560 561 576 (x2c_range_all (fun t => natAxpySp 384 21714 31 (transA2Tab.getD (t % 231) []) (f0.getD (t / 231) []) (x2Tab g (t / 231) (t % 231))) 560 1 chkA_5_d560) (x2c_join _ 561 562 576 (x2c_range_all (fun t => natAxpySp 384 21714 31 (transA2Tab.getD (t % 231) []) (f0.getD (t / 231) []) (x2Tab g (t / 231) (t % 231))) 561 1 chkA_5_d561) (x2c_join _ 562 563 576 (x2c_range_all (fun t => natAxpySp 384 21714 31 (transA2Tab.getD (t % 231) []) (f0.getD (t / 231) []) (x2Tab g (t / 231) (t % 231))) 562 1 chkA_5_d562) (x2c_join _ 563 564 576 (x2c_range_all (fun t => natAxpySp 384 21714 31 (transA2Tab.getD (t % 231) []) (f0.getD (t / 231) []) (x2Tab g (t / 231) (t % 231))) 563 1 chkA_5_d563) (x2c_join _ 564 565 576 (x2c_range_all (fun t => natAxpySp 384 21714 31 (transA2Tab.getD (t % 231) []) (f0.getD (t / 231) []) (x2Tab g (t / 231) (t % 231))) 564 1 chkA_5_d564) (x2c_join _ 565 566 576 (x2c_range_all (fun t => natAxpySp 384 21714 31 (transA2Tab.getD (t % 231) []) (f0.getD (t / 231) []) (x2Tab g (t / 231) (t % 231))) 565 1 chkA_5_d565) (x2c_join _ 566 567 576 (x2c_range_all (fun t => natAxpySp 384 21714 31 (transA2Tab.getD (t % 231) []) (f0.getD (t / 231) []) (x2Tab g (t / 231) (t % 231))) 566 1 chkA_5_d566) (x2c_join _ 567 568 576 (x2c_range_all (fun t => natAxpySp 384 21714 31 (transA2Tab.getD (t % 231) []) (f0.getD (t / 231) []) (x2Tab g (t / 231) (t % 231))) 567 1 chkA_5_d567) (x2c_join _ 568 569 576 (x2c_range_all (fun t => natAxpySp 384 21714 31 (transA2Tab.getD (t % 231) []) (f0.getD (t / 231) []) (x2Tab g (t / 231) (t % 231))) 568 1 chkA_5_d568) (x2c_join _ 569 570 576 (x2c_range_all (fun t => natAxpySp 384 21714 31 (transA2Tab.getD (t % 231) []) (f0.getD (t / 231) []) (x2Tab g (t / 231) (t % 231))) 569 1 chkA_5_d569) (x2c_join _ 570 571 576 (x2c_range_all (fun t => natAxpySp 384 21714 31 (transA2Tab.getD (t % 231) []) (f0.getD (t / 231) []) (x2Tab g (t / 231) (t % 231))) 570 1 chkA_5_d570) (x2c_join _ 571 572 576 (x2c_range_all (fun t => natAxpySp 384 21714 31 (transA2Tab.getD (t % 231) []) (f0.getD (t / 231) []) (x2Tab g (t / 231) (t % 231))) 571 1 chkA_5_d571) (x2c_join _ 572 573 576 (x2c_range_all (fun t => natAxpySp 384 21714 31 (transA2Tab.getD (t % 231) []) (f0.getD (t / 231) []) (x2Tab g (t / 231) (t % 231))) 572 1 chkA_5_d572) (x2c_join _ 573 574 576 (x2c_range_all (fun t => natAxpySp 384 21714 31 (transA2Tab.getD (t % 231) []) (f0.getD (t / 231) []) (x2Tab g (t / 231) (t % 231))) 573 1 chkA_5_d573) (x2c_join _ 574 575 576 (x2c_range_all (fun t => natAxpySp 384 21714 31 (transA2Tab.getD (t % 231) []) (f0.getD (t / 231) []) (x2Tab g (t / 231) (t % 231))) 574 1 chkA_5_d574) (x2c_range_all (fun t => natAxpySp 384 21714 31 (transA2Tab.getD (t % 231) []) (f0.getD (t / 231) []) (x2Tab g (t / 231) (t % 231))) 575 1 chkA_5_d575))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))


end ThreeCopyQutritWerner.X2.CoreA2g
