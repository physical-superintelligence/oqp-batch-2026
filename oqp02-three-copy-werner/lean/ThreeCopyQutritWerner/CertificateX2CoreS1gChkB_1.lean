module

public import ThreeCopyQutritWerner.CertificateX2CoreS1gO
public import ThreeCopyQutritWerner.CertificateX2Trans
public import ThreeCopyQutritWerner.CertificateX2CoreBatchGen
public import ThreeCopyQutritWerner.CertificateX2CoreBatchFlat

@[expose] public section


/-! Batched core S1g: axis-1 stage, one output per declaration, flat indices 96..191. -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option exponentiation.threshold 1000000

namespace ThreeCopyQutritWerner.X2.CoreS1g
open ThreeCopyQutritWerner ThreeCopyQutritWerner.X2

theorem chkB_1_d96 : (List.range' 96 1).all (fun t => natAxpySp 384 26508 31 (transS1Tab.getD (t % 282) []) (h.getD (t / 282) []) (x2Tab o (t / 282) (t % 282))) = true := by
  decide +kernel

theorem chkB_1_d97 : (List.range' 97 1).all (fun t => natAxpySp 384 26508 31 (transS1Tab.getD (t % 282) []) (h.getD (t / 282) []) (x2Tab o (t / 282) (t % 282))) = true := by
  decide +kernel

theorem chkB_1_d98 : (List.range' 98 1).all (fun t => natAxpySp 384 26508 31 (transS1Tab.getD (t % 282) []) (h.getD (t / 282) []) (x2Tab o (t / 282) (t % 282))) = true := by
  decide +kernel

theorem chkB_1_d99 : (List.range' 99 1).all (fun t => natAxpySp 384 26508 31 (transS1Tab.getD (t % 282) []) (h.getD (t / 282) []) (x2Tab o (t / 282) (t % 282))) = true := by
  decide +kernel

theorem chkB_1_d100 : (List.range' 100 1).all (fun t => natAxpySp 384 26508 31 (transS1Tab.getD (t % 282) []) (h.getD (t / 282) []) (x2Tab o (t / 282) (t % 282))) = true := by
  decide +kernel

theorem chkB_1_d101 : (List.range' 101 1).all (fun t => natAxpySp 384 26508 31 (transS1Tab.getD (t % 282) []) (h.getD (t / 282) []) (x2Tab o (t / 282) (t % 282))) = true := by
  decide +kernel

theorem chkB_1_d102 : (List.range' 102 1).all (fun t => natAxpySp 384 26508 31 (transS1Tab.getD (t % 282) []) (h.getD (t / 282) []) (x2Tab o (t / 282) (t % 282))) = true := by
  decide +kernel

theorem chkB_1_d103 : (List.range' 103 1).all (fun t => natAxpySp 384 26508 31 (transS1Tab.getD (t % 282) []) (h.getD (t / 282) []) (x2Tab o (t / 282) (t % 282))) = true := by
  decide +kernel

theorem chkB_1_d104 : (List.range' 104 1).all (fun t => natAxpySp 384 26508 31 (transS1Tab.getD (t % 282) []) (h.getD (t / 282) []) (x2Tab o (t / 282) (t % 282))) = true := by
  decide +kernel

theorem chkB_1_d105 : (List.range' 105 1).all (fun t => natAxpySp 384 26508 31 (transS1Tab.getD (t % 282) []) (h.getD (t / 282) []) (x2Tab o (t / 282) (t % 282))) = true := by
  decide +kernel

theorem chkB_1_d106 : (List.range' 106 1).all (fun t => natAxpySp 384 26508 31 (transS1Tab.getD (t % 282) []) (h.getD (t / 282) []) (x2Tab o (t / 282) (t % 282))) = true := by
  decide +kernel

theorem chkB_1_d107 : (List.range' 107 1).all (fun t => natAxpySp 384 26508 31 (transS1Tab.getD (t % 282) []) (h.getD (t / 282) []) (x2Tab o (t / 282) (t % 282))) = true := by
  decide +kernel

theorem chkB_1_d108 : (List.range' 108 1).all (fun t => natAxpySp 384 26508 31 (transS1Tab.getD (t % 282) []) (h.getD (t / 282) []) (x2Tab o (t / 282) (t % 282))) = true := by
  decide +kernel

theorem chkB_1_d109 : (List.range' 109 1).all (fun t => natAxpySp 384 26508 31 (transS1Tab.getD (t % 282) []) (h.getD (t / 282) []) (x2Tab o (t / 282) (t % 282))) = true := by
  decide +kernel

theorem chkB_1_d110 : (List.range' 110 1).all (fun t => natAxpySp 384 26508 31 (transS1Tab.getD (t % 282) []) (h.getD (t / 282) []) (x2Tab o (t / 282) (t % 282))) = true := by
  decide +kernel

theorem chkB_1_d111 : (List.range' 111 1).all (fun t => natAxpySp 384 26508 31 (transS1Tab.getD (t % 282) []) (h.getD (t / 282) []) (x2Tab o (t / 282) (t % 282))) = true := by
  decide +kernel

theorem chkB_1_d112 : (List.range' 112 1).all (fun t => natAxpySp 384 26508 31 (transS1Tab.getD (t % 282) []) (h.getD (t / 282) []) (x2Tab o (t / 282) (t % 282))) = true := by
  decide +kernel

theorem chkB_1_d113 : (List.range' 113 1).all (fun t => natAxpySp 384 26508 31 (transS1Tab.getD (t % 282) []) (h.getD (t / 282) []) (x2Tab o (t / 282) (t % 282))) = true := by
  decide +kernel

theorem chkB_1_d114 : (List.range' 114 1).all (fun t => natAxpySp 384 26508 31 (transS1Tab.getD (t % 282) []) (h.getD (t / 282) []) (x2Tab o (t / 282) (t % 282))) = true := by
  decide +kernel

theorem chkB_1_d115 : (List.range' 115 1).all (fun t => natAxpySp 384 26508 31 (transS1Tab.getD (t % 282) []) (h.getD (t / 282) []) (x2Tab o (t / 282) (t % 282))) = true := by
  decide +kernel

theorem chkB_1_d116 : (List.range' 116 1).all (fun t => natAxpySp 384 26508 31 (transS1Tab.getD (t % 282) []) (h.getD (t / 282) []) (x2Tab o (t / 282) (t % 282))) = true := by
  decide +kernel

theorem chkB_1_d117 : (List.range' 117 1).all (fun t => natAxpySp 384 26508 31 (transS1Tab.getD (t % 282) []) (h.getD (t / 282) []) (x2Tab o (t / 282) (t % 282))) = true := by
  decide +kernel

theorem chkB_1_d118 : (List.range' 118 1).all (fun t => natAxpySp 384 26508 31 (transS1Tab.getD (t % 282) []) (h.getD (t / 282) []) (x2Tab o (t / 282) (t % 282))) = true := by
  decide +kernel

theorem chkB_1_d119 : (List.range' 119 1).all (fun t => natAxpySp 384 26508 31 (transS1Tab.getD (t % 282) []) (h.getD (t / 282) []) (x2Tab o (t / 282) (t % 282))) = true := by
  decide +kernel

theorem chkB_1_d120 : (List.range' 120 1).all (fun t => natAxpySp 384 26508 31 (transS1Tab.getD (t % 282) []) (h.getD (t / 282) []) (x2Tab o (t / 282) (t % 282))) = true := by
  decide +kernel

theorem chkB_1_d121 : (List.range' 121 1).all (fun t => natAxpySp 384 26508 31 (transS1Tab.getD (t % 282) []) (h.getD (t / 282) []) (x2Tab o (t / 282) (t % 282))) = true := by
  decide +kernel

theorem chkB_1_d122 : (List.range' 122 1).all (fun t => natAxpySp 384 26508 31 (transS1Tab.getD (t % 282) []) (h.getD (t / 282) []) (x2Tab o (t / 282) (t % 282))) = true := by
  decide +kernel

theorem chkB_1_d123 : (List.range' 123 1).all (fun t => natAxpySp 384 26508 31 (transS1Tab.getD (t % 282) []) (h.getD (t / 282) []) (x2Tab o (t / 282) (t % 282))) = true := by
  decide +kernel

theorem chkB_1_d124 : (List.range' 124 1).all (fun t => natAxpySp 384 26508 31 (transS1Tab.getD (t % 282) []) (h.getD (t / 282) []) (x2Tab o (t / 282) (t % 282))) = true := by
  decide +kernel

theorem chkB_1_d125 : (List.range' 125 1).all (fun t => natAxpySp 384 26508 31 (transS1Tab.getD (t % 282) []) (h.getD (t / 282) []) (x2Tab o (t / 282) (t % 282))) = true := by
  decide +kernel

theorem chkB_1_d126 : (List.range' 126 1).all (fun t => natAxpySp 384 26508 31 (transS1Tab.getD (t % 282) []) (h.getD (t / 282) []) (x2Tab o (t / 282) (t % 282))) = true := by
  decide +kernel

theorem chkB_1_d127 : (List.range' 127 1).all (fun t => natAxpySp 384 26508 31 (transS1Tab.getD (t % 282) []) (h.getD (t / 282) []) (x2Tab o (t / 282) (t % 282))) = true := by
  decide +kernel

theorem chkB_1_d128 : (List.range' 128 1).all (fun t => natAxpySp 384 26508 31 (transS1Tab.getD (t % 282) []) (h.getD (t / 282) []) (x2Tab o (t / 282) (t % 282))) = true := by
  decide +kernel

theorem chkB_1_d129 : (List.range' 129 1).all (fun t => natAxpySp 384 26508 31 (transS1Tab.getD (t % 282) []) (h.getD (t / 282) []) (x2Tab o (t / 282) (t % 282))) = true := by
  decide +kernel

theorem chkB_1_d130 : (List.range' 130 1).all (fun t => natAxpySp 384 26508 31 (transS1Tab.getD (t % 282) []) (h.getD (t / 282) []) (x2Tab o (t / 282) (t % 282))) = true := by
  decide +kernel

theorem chkB_1_d131 : (List.range' 131 1).all (fun t => natAxpySp 384 26508 31 (transS1Tab.getD (t % 282) []) (h.getD (t / 282) []) (x2Tab o (t / 282) (t % 282))) = true := by
  decide +kernel

theorem chkB_1_d132 : (List.range' 132 1).all (fun t => natAxpySp 384 26508 31 (transS1Tab.getD (t % 282) []) (h.getD (t / 282) []) (x2Tab o (t / 282) (t % 282))) = true := by
  decide +kernel

theorem chkB_1_d133 : (List.range' 133 1).all (fun t => natAxpySp 384 26508 31 (transS1Tab.getD (t % 282) []) (h.getD (t / 282) []) (x2Tab o (t / 282) (t % 282))) = true := by
  decide +kernel

theorem chkB_1_d134 : (List.range' 134 1).all (fun t => natAxpySp 384 26508 31 (transS1Tab.getD (t % 282) []) (h.getD (t / 282) []) (x2Tab o (t / 282) (t % 282))) = true := by
  decide +kernel

theorem chkB_1_d135 : (List.range' 135 1).all (fun t => natAxpySp 384 26508 31 (transS1Tab.getD (t % 282) []) (h.getD (t / 282) []) (x2Tab o (t / 282) (t % 282))) = true := by
  decide +kernel

theorem chkB_1_d136 : (List.range' 136 1).all (fun t => natAxpySp 384 26508 31 (transS1Tab.getD (t % 282) []) (h.getD (t / 282) []) (x2Tab o (t / 282) (t % 282))) = true := by
  decide +kernel

theorem chkB_1_d137 : (List.range' 137 1).all (fun t => natAxpySp 384 26508 31 (transS1Tab.getD (t % 282) []) (h.getD (t / 282) []) (x2Tab o (t / 282) (t % 282))) = true := by
  decide +kernel

theorem chkB_1_d138 : (List.range' 138 1).all (fun t => natAxpySp 384 26508 31 (transS1Tab.getD (t % 282) []) (h.getD (t / 282) []) (x2Tab o (t / 282) (t % 282))) = true := by
  decide +kernel

theorem chkB_1_d139 : (List.range' 139 1).all (fun t => natAxpySp 384 26508 31 (transS1Tab.getD (t % 282) []) (h.getD (t / 282) []) (x2Tab o (t / 282) (t % 282))) = true := by
  decide +kernel

theorem chkB_1_d140 : (List.range' 140 1).all (fun t => natAxpySp 384 26508 31 (transS1Tab.getD (t % 282) []) (h.getD (t / 282) []) (x2Tab o (t / 282) (t % 282))) = true := by
  decide +kernel

theorem chkB_1_d141 : (List.range' 141 1).all (fun t => natAxpySp 384 26508 31 (transS1Tab.getD (t % 282) []) (h.getD (t / 282) []) (x2Tab o (t / 282) (t % 282))) = true := by
  decide +kernel

theorem chkB_1_d142 : (List.range' 142 1).all (fun t => natAxpySp 384 26508 31 (transS1Tab.getD (t % 282) []) (h.getD (t / 282) []) (x2Tab o (t / 282) (t % 282))) = true := by
  decide +kernel

theorem chkB_1_d143 : (List.range' 143 1).all (fun t => natAxpySp 384 26508 31 (transS1Tab.getD (t % 282) []) (h.getD (t / 282) []) (x2Tab o (t / 282) (t % 282))) = true := by
  decide +kernel

theorem chkB_1_d144 : (List.range' 144 1).all (fun t => natAxpySp 384 26508 31 (transS1Tab.getD (t % 282) []) (h.getD (t / 282) []) (x2Tab o (t / 282) (t % 282))) = true := by
  decide +kernel

theorem chkB_1_d145 : (List.range' 145 1).all (fun t => natAxpySp 384 26508 31 (transS1Tab.getD (t % 282) []) (h.getD (t / 282) []) (x2Tab o (t / 282) (t % 282))) = true := by
  decide +kernel

theorem chkB_1_d146 : (List.range' 146 1).all (fun t => natAxpySp 384 26508 31 (transS1Tab.getD (t % 282) []) (h.getD (t / 282) []) (x2Tab o (t / 282) (t % 282))) = true := by
  decide +kernel

theorem chkB_1_d147 : (List.range' 147 1).all (fun t => natAxpySp 384 26508 31 (transS1Tab.getD (t % 282) []) (h.getD (t / 282) []) (x2Tab o (t / 282) (t % 282))) = true := by
  decide +kernel

theorem chkB_1_d148 : (List.range' 148 1).all (fun t => natAxpySp 384 26508 31 (transS1Tab.getD (t % 282) []) (h.getD (t / 282) []) (x2Tab o (t / 282) (t % 282))) = true := by
  decide +kernel

theorem chkB_1_d149 : (List.range' 149 1).all (fun t => natAxpySp 384 26508 31 (transS1Tab.getD (t % 282) []) (h.getD (t / 282) []) (x2Tab o (t / 282) (t % 282))) = true := by
  decide +kernel

theorem chkB_1_d150 : (List.range' 150 1).all (fun t => natAxpySp 384 26508 31 (transS1Tab.getD (t % 282) []) (h.getD (t / 282) []) (x2Tab o (t / 282) (t % 282))) = true := by
  decide +kernel

theorem chkB_1_d151 : (List.range' 151 1).all (fun t => natAxpySp 384 26508 31 (transS1Tab.getD (t % 282) []) (h.getD (t / 282) []) (x2Tab o (t / 282) (t % 282))) = true := by
  decide +kernel

theorem chkB_1_d152 : (List.range' 152 1).all (fun t => natAxpySp 384 26508 31 (transS1Tab.getD (t % 282) []) (h.getD (t / 282) []) (x2Tab o (t / 282) (t % 282))) = true := by
  decide +kernel

theorem chkB_1_d153 : (List.range' 153 1).all (fun t => natAxpySp 384 26508 31 (transS1Tab.getD (t % 282) []) (h.getD (t / 282) []) (x2Tab o (t / 282) (t % 282))) = true := by
  decide +kernel

theorem chkB_1_d154 : (List.range' 154 1).all (fun t => natAxpySp 384 26508 31 (transS1Tab.getD (t % 282) []) (h.getD (t / 282) []) (x2Tab o (t / 282) (t % 282))) = true := by
  decide +kernel

theorem chkB_1_d155 : (List.range' 155 1).all (fun t => natAxpySp 384 26508 31 (transS1Tab.getD (t % 282) []) (h.getD (t / 282) []) (x2Tab o (t / 282) (t % 282))) = true := by
  decide +kernel

theorem chkB_1_d156 : (List.range' 156 1).all (fun t => natAxpySp 384 26508 31 (transS1Tab.getD (t % 282) []) (h.getD (t / 282) []) (x2Tab o (t / 282) (t % 282))) = true := by
  decide +kernel

theorem chkB_1_d157 : (List.range' 157 1).all (fun t => natAxpySp 384 26508 31 (transS1Tab.getD (t % 282) []) (h.getD (t / 282) []) (x2Tab o (t / 282) (t % 282))) = true := by
  decide +kernel

theorem chkB_1_d158 : (List.range' 158 1).all (fun t => natAxpySp 384 26508 31 (transS1Tab.getD (t % 282) []) (h.getD (t / 282) []) (x2Tab o (t / 282) (t % 282))) = true := by
  decide +kernel

theorem chkB_1_d159 : (List.range' 159 1).all (fun t => natAxpySp 384 26508 31 (transS1Tab.getD (t % 282) []) (h.getD (t / 282) []) (x2Tab o (t / 282) (t % 282))) = true := by
  decide +kernel

theorem chkB_1_d160 : (List.range' 160 1).all (fun t => natAxpySp 384 26508 31 (transS1Tab.getD (t % 282) []) (h.getD (t / 282) []) (x2Tab o (t / 282) (t % 282))) = true := by
  decide +kernel

theorem chkB_1_d161 : (List.range' 161 1).all (fun t => natAxpySp 384 26508 31 (transS1Tab.getD (t % 282) []) (h.getD (t / 282) []) (x2Tab o (t / 282) (t % 282))) = true := by
  decide +kernel

theorem chkB_1_d162 : (List.range' 162 1).all (fun t => natAxpySp 384 26508 31 (transS1Tab.getD (t % 282) []) (h.getD (t / 282) []) (x2Tab o (t / 282) (t % 282))) = true := by
  decide +kernel

theorem chkB_1_d163 : (List.range' 163 1).all (fun t => natAxpySp 384 26508 31 (transS1Tab.getD (t % 282) []) (h.getD (t / 282) []) (x2Tab o (t / 282) (t % 282))) = true := by
  decide +kernel

theorem chkB_1_d164 : (List.range' 164 1).all (fun t => natAxpySp 384 26508 31 (transS1Tab.getD (t % 282) []) (h.getD (t / 282) []) (x2Tab o (t / 282) (t % 282))) = true := by
  decide +kernel

theorem chkB_1_d165 : (List.range' 165 1).all (fun t => natAxpySp 384 26508 31 (transS1Tab.getD (t % 282) []) (h.getD (t / 282) []) (x2Tab o (t / 282) (t % 282))) = true := by
  decide +kernel

theorem chkB_1_d166 : (List.range' 166 1).all (fun t => natAxpySp 384 26508 31 (transS1Tab.getD (t % 282) []) (h.getD (t / 282) []) (x2Tab o (t / 282) (t % 282))) = true := by
  decide +kernel

theorem chkB_1_d167 : (List.range' 167 1).all (fun t => natAxpySp 384 26508 31 (transS1Tab.getD (t % 282) []) (h.getD (t / 282) []) (x2Tab o (t / 282) (t % 282))) = true := by
  decide +kernel

theorem chkB_1_d168 : (List.range' 168 1).all (fun t => natAxpySp 384 26508 31 (transS1Tab.getD (t % 282) []) (h.getD (t / 282) []) (x2Tab o (t / 282) (t % 282))) = true := by
  decide +kernel

theorem chkB_1_d169 : (List.range' 169 1).all (fun t => natAxpySp 384 26508 31 (transS1Tab.getD (t % 282) []) (h.getD (t / 282) []) (x2Tab o (t / 282) (t % 282))) = true := by
  decide +kernel

theorem chkB_1_d170 : (List.range' 170 1).all (fun t => natAxpySp 384 26508 31 (transS1Tab.getD (t % 282) []) (h.getD (t / 282) []) (x2Tab o (t / 282) (t % 282))) = true := by
  decide +kernel

theorem chkB_1_d171 : (List.range' 171 1).all (fun t => natAxpySp 384 26508 31 (transS1Tab.getD (t % 282) []) (h.getD (t / 282) []) (x2Tab o (t / 282) (t % 282))) = true := by
  decide +kernel

theorem chkB_1_d172 : (List.range' 172 1).all (fun t => natAxpySp 384 26508 31 (transS1Tab.getD (t % 282) []) (h.getD (t / 282) []) (x2Tab o (t / 282) (t % 282))) = true := by
  decide +kernel

theorem chkB_1_d173 : (List.range' 173 1).all (fun t => natAxpySp 384 26508 31 (transS1Tab.getD (t % 282) []) (h.getD (t / 282) []) (x2Tab o (t / 282) (t % 282))) = true := by
  decide +kernel

theorem chkB_1_d174 : (List.range' 174 1).all (fun t => natAxpySp 384 26508 31 (transS1Tab.getD (t % 282) []) (h.getD (t / 282) []) (x2Tab o (t / 282) (t % 282))) = true := by
  decide +kernel

theorem chkB_1_d175 : (List.range' 175 1).all (fun t => natAxpySp 384 26508 31 (transS1Tab.getD (t % 282) []) (h.getD (t / 282) []) (x2Tab o (t / 282) (t % 282))) = true := by
  decide +kernel

theorem chkB_1_d176 : (List.range' 176 1).all (fun t => natAxpySp 384 26508 31 (transS1Tab.getD (t % 282) []) (h.getD (t / 282) []) (x2Tab o (t / 282) (t % 282))) = true := by
  decide +kernel

theorem chkB_1_d177 : (List.range' 177 1).all (fun t => natAxpySp 384 26508 31 (transS1Tab.getD (t % 282) []) (h.getD (t / 282) []) (x2Tab o (t / 282) (t % 282))) = true := by
  decide +kernel

theorem chkB_1_d178 : (List.range' 178 1).all (fun t => natAxpySp 384 26508 31 (transS1Tab.getD (t % 282) []) (h.getD (t / 282) []) (x2Tab o (t / 282) (t % 282))) = true := by
  decide +kernel

theorem chkB_1_d179 : (List.range' 179 1).all (fun t => natAxpySp 384 26508 31 (transS1Tab.getD (t % 282) []) (h.getD (t / 282) []) (x2Tab o (t / 282) (t % 282))) = true := by
  decide +kernel

theorem chkB_1_d180 : (List.range' 180 1).all (fun t => natAxpySp 384 26508 31 (transS1Tab.getD (t % 282) []) (h.getD (t / 282) []) (x2Tab o (t / 282) (t % 282))) = true := by
  decide +kernel

theorem chkB_1_d181 : (List.range' 181 1).all (fun t => natAxpySp 384 26508 31 (transS1Tab.getD (t % 282) []) (h.getD (t / 282) []) (x2Tab o (t / 282) (t % 282))) = true := by
  decide +kernel

theorem chkB_1_d182 : (List.range' 182 1).all (fun t => natAxpySp 384 26508 31 (transS1Tab.getD (t % 282) []) (h.getD (t / 282) []) (x2Tab o (t / 282) (t % 282))) = true := by
  decide +kernel

theorem chkB_1_d183 : (List.range' 183 1).all (fun t => natAxpySp 384 26508 31 (transS1Tab.getD (t % 282) []) (h.getD (t / 282) []) (x2Tab o (t / 282) (t % 282))) = true := by
  decide +kernel

theorem chkB_1_d184 : (List.range' 184 1).all (fun t => natAxpySp 384 26508 31 (transS1Tab.getD (t % 282) []) (h.getD (t / 282) []) (x2Tab o (t / 282) (t % 282))) = true := by
  decide +kernel

theorem chkB_1_d185 : (List.range' 185 1).all (fun t => natAxpySp 384 26508 31 (transS1Tab.getD (t % 282) []) (h.getD (t / 282) []) (x2Tab o (t / 282) (t % 282))) = true := by
  decide +kernel

theorem chkB_1_d186 : (List.range' 186 1).all (fun t => natAxpySp 384 26508 31 (transS1Tab.getD (t % 282) []) (h.getD (t / 282) []) (x2Tab o (t / 282) (t % 282))) = true := by
  decide +kernel

theorem chkB_1_d187 : (List.range' 187 1).all (fun t => natAxpySp 384 26508 31 (transS1Tab.getD (t % 282) []) (h.getD (t / 282) []) (x2Tab o (t / 282) (t % 282))) = true := by
  decide +kernel

theorem chkB_1_d188 : (List.range' 188 1).all (fun t => natAxpySp 384 26508 31 (transS1Tab.getD (t % 282) []) (h.getD (t / 282) []) (x2Tab o (t / 282) (t % 282))) = true := by
  decide +kernel

theorem chkB_1_d189 : (List.range' 189 1).all (fun t => natAxpySp 384 26508 31 (transS1Tab.getD (t % 282) []) (h.getD (t / 282) []) (x2Tab o (t / 282) (t % 282))) = true := by
  decide +kernel

theorem chkB_1_d190 : (List.range' 190 1).all (fun t => natAxpySp 384 26508 31 (transS1Tab.getD (t % 282) []) (h.getD (t / 282) []) (x2Tab o (t / 282) (t % 282))) = true := by
  decide +kernel

theorem chkB_1_d191 : (List.range' 191 1).all (fun t => natAxpySp 384 26508 31 (transS1Tab.getD (t % 282) []) (h.getD (t / 282) []) (x2Tab o (t / 282) (t % 282))) = true := by
  decide +kernel

theorem chkB_1 : ∀ t, 96 ≤ t → t < 192 → (natAxpySp 384 26508 31 (transS1Tab.getD (t % 282) []) (h.getD (t / 282) []) (x2Tab o (t / 282) (t % 282))) = true := by
  exact (x2c_join _ 96 97 192 (x2c_range_all (fun t => natAxpySp 384 26508 31 (transS1Tab.getD (t % 282) []) (h.getD (t / 282) []) (x2Tab o (t / 282) (t % 282))) 96 1 chkB_1_d96) (x2c_join _ 97 98 192 (x2c_range_all (fun t => natAxpySp 384 26508 31 (transS1Tab.getD (t % 282) []) (h.getD (t / 282) []) (x2Tab o (t / 282) (t % 282))) 97 1 chkB_1_d97) (x2c_join _ 98 99 192 (x2c_range_all (fun t => natAxpySp 384 26508 31 (transS1Tab.getD (t % 282) []) (h.getD (t / 282) []) (x2Tab o (t / 282) (t % 282))) 98 1 chkB_1_d98) (x2c_join _ 99 100 192 (x2c_range_all (fun t => natAxpySp 384 26508 31 (transS1Tab.getD (t % 282) []) (h.getD (t / 282) []) (x2Tab o (t / 282) (t % 282))) 99 1 chkB_1_d99) (x2c_join _ 100 101 192 (x2c_range_all (fun t => natAxpySp 384 26508 31 (transS1Tab.getD (t % 282) []) (h.getD (t / 282) []) (x2Tab o (t / 282) (t % 282))) 100 1 chkB_1_d100) (x2c_join _ 101 102 192 (x2c_range_all (fun t => natAxpySp 384 26508 31 (transS1Tab.getD (t % 282) []) (h.getD (t / 282) []) (x2Tab o (t / 282) (t % 282))) 101 1 chkB_1_d101) (x2c_join _ 102 103 192 (x2c_range_all (fun t => natAxpySp 384 26508 31 (transS1Tab.getD (t % 282) []) (h.getD (t / 282) []) (x2Tab o (t / 282) (t % 282))) 102 1 chkB_1_d102) (x2c_join _ 103 104 192 (x2c_range_all (fun t => natAxpySp 384 26508 31 (transS1Tab.getD (t % 282) []) (h.getD (t / 282) []) (x2Tab o (t / 282) (t % 282))) 103 1 chkB_1_d103) (x2c_join _ 104 105 192 (x2c_range_all (fun t => natAxpySp 384 26508 31 (transS1Tab.getD (t % 282) []) (h.getD (t / 282) []) (x2Tab o (t / 282) (t % 282))) 104 1 chkB_1_d104) (x2c_join _ 105 106 192 (x2c_range_all (fun t => natAxpySp 384 26508 31 (transS1Tab.getD (t % 282) []) (h.getD (t / 282) []) (x2Tab o (t / 282) (t % 282))) 105 1 chkB_1_d105) (x2c_join _ 106 107 192 (x2c_range_all (fun t => natAxpySp 384 26508 31 (transS1Tab.getD (t % 282) []) (h.getD (t / 282) []) (x2Tab o (t / 282) (t % 282))) 106 1 chkB_1_d106) (x2c_join _ 107 108 192 (x2c_range_all (fun t => natAxpySp 384 26508 31 (transS1Tab.getD (t % 282) []) (h.getD (t / 282) []) (x2Tab o (t / 282) (t % 282))) 107 1 chkB_1_d107) (x2c_join _ 108 109 192 (x2c_range_all (fun t => natAxpySp 384 26508 31 (transS1Tab.getD (t % 282) []) (h.getD (t / 282) []) (x2Tab o (t / 282) (t % 282))) 108 1 chkB_1_d108) (x2c_join _ 109 110 192 (x2c_range_all (fun t => natAxpySp 384 26508 31 (transS1Tab.getD (t % 282) []) (h.getD (t / 282) []) (x2Tab o (t / 282) (t % 282))) 109 1 chkB_1_d109) (x2c_join _ 110 111 192 (x2c_range_all (fun t => natAxpySp 384 26508 31 (transS1Tab.getD (t % 282) []) (h.getD (t / 282) []) (x2Tab o (t / 282) (t % 282))) 110 1 chkB_1_d110) (x2c_join _ 111 112 192 (x2c_range_all (fun t => natAxpySp 384 26508 31 (transS1Tab.getD (t % 282) []) (h.getD (t / 282) []) (x2Tab o (t / 282) (t % 282))) 111 1 chkB_1_d111) (x2c_join _ 112 113 192 (x2c_range_all (fun t => natAxpySp 384 26508 31 (transS1Tab.getD (t % 282) []) (h.getD (t / 282) []) (x2Tab o (t / 282) (t % 282))) 112 1 chkB_1_d112) (x2c_join _ 113 114 192 (x2c_range_all (fun t => natAxpySp 384 26508 31 (transS1Tab.getD (t % 282) []) (h.getD (t / 282) []) (x2Tab o (t / 282) (t % 282))) 113 1 chkB_1_d113) (x2c_join _ 114 115 192 (x2c_range_all (fun t => natAxpySp 384 26508 31 (transS1Tab.getD (t % 282) []) (h.getD (t / 282) []) (x2Tab o (t / 282) (t % 282))) 114 1 chkB_1_d114) (x2c_join _ 115 116 192 (x2c_range_all (fun t => natAxpySp 384 26508 31 (transS1Tab.getD (t % 282) []) (h.getD (t / 282) []) (x2Tab o (t / 282) (t % 282))) 115 1 chkB_1_d115) (x2c_join _ 116 117 192 (x2c_range_all (fun t => natAxpySp 384 26508 31 (transS1Tab.getD (t % 282) []) (h.getD (t / 282) []) (x2Tab o (t / 282) (t % 282))) 116 1 chkB_1_d116) (x2c_join _ 117 118 192 (x2c_range_all (fun t => natAxpySp 384 26508 31 (transS1Tab.getD (t % 282) []) (h.getD (t / 282) []) (x2Tab o (t / 282) (t % 282))) 117 1 chkB_1_d117) (x2c_join _ 118 119 192 (x2c_range_all (fun t => natAxpySp 384 26508 31 (transS1Tab.getD (t % 282) []) (h.getD (t / 282) []) (x2Tab o (t / 282) (t % 282))) 118 1 chkB_1_d118) (x2c_join _ 119 120 192 (x2c_range_all (fun t => natAxpySp 384 26508 31 (transS1Tab.getD (t % 282) []) (h.getD (t / 282) []) (x2Tab o (t / 282) (t % 282))) 119 1 chkB_1_d119) (x2c_join _ 120 121 192 (x2c_range_all (fun t => natAxpySp 384 26508 31 (transS1Tab.getD (t % 282) []) (h.getD (t / 282) []) (x2Tab o (t / 282) (t % 282))) 120 1 chkB_1_d120) (x2c_join _ 121 122 192 (x2c_range_all (fun t => natAxpySp 384 26508 31 (transS1Tab.getD (t % 282) []) (h.getD (t / 282) []) (x2Tab o (t / 282) (t % 282))) 121 1 chkB_1_d121) (x2c_join _ 122 123 192 (x2c_range_all (fun t => natAxpySp 384 26508 31 (transS1Tab.getD (t % 282) []) (h.getD (t / 282) []) (x2Tab o (t / 282) (t % 282))) 122 1 chkB_1_d122) (x2c_join _ 123 124 192 (x2c_range_all (fun t => natAxpySp 384 26508 31 (transS1Tab.getD (t % 282) []) (h.getD (t / 282) []) (x2Tab o (t / 282) (t % 282))) 123 1 chkB_1_d123) (x2c_join _ 124 125 192 (x2c_range_all (fun t => natAxpySp 384 26508 31 (transS1Tab.getD (t % 282) []) (h.getD (t / 282) []) (x2Tab o (t / 282) (t % 282))) 124 1 chkB_1_d124) (x2c_join _ 125 126 192 (x2c_range_all (fun t => natAxpySp 384 26508 31 (transS1Tab.getD (t % 282) []) (h.getD (t / 282) []) (x2Tab o (t / 282) (t % 282))) 125 1 chkB_1_d125) (x2c_join _ 126 127 192 (x2c_range_all (fun t => natAxpySp 384 26508 31 (transS1Tab.getD (t % 282) []) (h.getD (t / 282) []) (x2Tab o (t / 282) (t % 282))) 126 1 chkB_1_d126) (x2c_join _ 127 128 192 (x2c_range_all (fun t => natAxpySp 384 26508 31 (transS1Tab.getD (t % 282) []) (h.getD (t / 282) []) (x2Tab o (t / 282) (t % 282))) 127 1 chkB_1_d127) (x2c_join _ 128 129 192 (x2c_range_all (fun t => natAxpySp 384 26508 31 (transS1Tab.getD (t % 282) []) (h.getD (t / 282) []) (x2Tab o (t / 282) (t % 282))) 128 1 chkB_1_d128) (x2c_join _ 129 130 192 (x2c_range_all (fun t => natAxpySp 384 26508 31 (transS1Tab.getD (t % 282) []) (h.getD (t / 282) []) (x2Tab o (t / 282) (t % 282))) 129 1 chkB_1_d129) (x2c_join _ 130 131 192 (x2c_range_all (fun t => natAxpySp 384 26508 31 (transS1Tab.getD (t % 282) []) (h.getD (t / 282) []) (x2Tab o (t / 282) (t % 282))) 130 1 chkB_1_d130) (x2c_join _ 131 132 192 (x2c_range_all (fun t => natAxpySp 384 26508 31 (transS1Tab.getD (t % 282) []) (h.getD (t / 282) []) (x2Tab o (t / 282) (t % 282))) 131 1 chkB_1_d131) (x2c_join _ 132 133 192 (x2c_range_all (fun t => natAxpySp 384 26508 31 (transS1Tab.getD (t % 282) []) (h.getD (t / 282) []) (x2Tab o (t / 282) (t % 282))) 132 1 chkB_1_d132) (x2c_join _ 133 134 192 (x2c_range_all (fun t => natAxpySp 384 26508 31 (transS1Tab.getD (t % 282) []) (h.getD (t / 282) []) (x2Tab o (t / 282) (t % 282))) 133 1 chkB_1_d133) (x2c_join _ 134 135 192 (x2c_range_all (fun t => natAxpySp 384 26508 31 (transS1Tab.getD (t % 282) []) (h.getD (t / 282) []) (x2Tab o (t / 282) (t % 282))) 134 1 chkB_1_d134) (x2c_join _ 135 136 192 (x2c_range_all (fun t => natAxpySp 384 26508 31 (transS1Tab.getD (t % 282) []) (h.getD (t / 282) []) (x2Tab o (t / 282) (t % 282))) 135 1 chkB_1_d135) (x2c_join _ 136 137 192 (x2c_range_all (fun t => natAxpySp 384 26508 31 (transS1Tab.getD (t % 282) []) (h.getD (t / 282) []) (x2Tab o (t / 282) (t % 282))) 136 1 chkB_1_d136) (x2c_join _ 137 138 192 (x2c_range_all (fun t => natAxpySp 384 26508 31 (transS1Tab.getD (t % 282) []) (h.getD (t / 282) []) (x2Tab o (t / 282) (t % 282))) 137 1 chkB_1_d137) (x2c_join _ 138 139 192 (x2c_range_all (fun t => natAxpySp 384 26508 31 (transS1Tab.getD (t % 282) []) (h.getD (t / 282) []) (x2Tab o (t / 282) (t % 282))) 138 1 chkB_1_d138) (x2c_join _ 139 140 192 (x2c_range_all (fun t => natAxpySp 384 26508 31 (transS1Tab.getD (t % 282) []) (h.getD (t / 282) []) (x2Tab o (t / 282) (t % 282))) 139 1 chkB_1_d139) (x2c_join _ 140 141 192 (x2c_range_all (fun t => natAxpySp 384 26508 31 (transS1Tab.getD (t % 282) []) (h.getD (t / 282) []) (x2Tab o (t / 282) (t % 282))) 140 1 chkB_1_d140) (x2c_join _ 141 142 192 (x2c_range_all (fun t => natAxpySp 384 26508 31 (transS1Tab.getD (t % 282) []) (h.getD (t / 282) []) (x2Tab o (t / 282) (t % 282))) 141 1 chkB_1_d141) (x2c_join _ 142 143 192 (x2c_range_all (fun t => natAxpySp 384 26508 31 (transS1Tab.getD (t % 282) []) (h.getD (t / 282) []) (x2Tab o (t / 282) (t % 282))) 142 1 chkB_1_d142) (x2c_join _ 143 144 192 (x2c_range_all (fun t => natAxpySp 384 26508 31 (transS1Tab.getD (t % 282) []) (h.getD (t / 282) []) (x2Tab o (t / 282) (t % 282))) 143 1 chkB_1_d143) (x2c_join _ 144 145 192 (x2c_range_all (fun t => natAxpySp 384 26508 31 (transS1Tab.getD (t % 282) []) (h.getD (t / 282) []) (x2Tab o (t / 282) (t % 282))) 144 1 chkB_1_d144) (x2c_join _ 145 146 192 (x2c_range_all (fun t => natAxpySp 384 26508 31 (transS1Tab.getD (t % 282) []) (h.getD (t / 282) []) (x2Tab o (t / 282) (t % 282))) 145 1 chkB_1_d145) (x2c_join _ 146 147 192 (x2c_range_all (fun t => natAxpySp 384 26508 31 (transS1Tab.getD (t % 282) []) (h.getD (t / 282) []) (x2Tab o (t / 282) (t % 282))) 146 1 chkB_1_d146) (x2c_join _ 147 148 192 (x2c_range_all (fun t => natAxpySp 384 26508 31 (transS1Tab.getD (t % 282) []) (h.getD (t / 282) []) (x2Tab o (t / 282) (t % 282))) 147 1 chkB_1_d147) (x2c_join _ 148 149 192 (x2c_range_all (fun t => natAxpySp 384 26508 31 (transS1Tab.getD (t % 282) []) (h.getD (t / 282) []) (x2Tab o (t / 282) (t % 282))) 148 1 chkB_1_d148) (x2c_join _ 149 150 192 (x2c_range_all (fun t => natAxpySp 384 26508 31 (transS1Tab.getD (t % 282) []) (h.getD (t / 282) []) (x2Tab o (t / 282) (t % 282))) 149 1 chkB_1_d149) (x2c_join _ 150 151 192 (x2c_range_all (fun t => natAxpySp 384 26508 31 (transS1Tab.getD (t % 282) []) (h.getD (t / 282) []) (x2Tab o (t / 282) (t % 282))) 150 1 chkB_1_d150) (x2c_join _ 151 152 192 (x2c_range_all (fun t => natAxpySp 384 26508 31 (transS1Tab.getD (t % 282) []) (h.getD (t / 282) []) (x2Tab o (t / 282) (t % 282))) 151 1 chkB_1_d151) (x2c_join _ 152 153 192 (x2c_range_all (fun t => natAxpySp 384 26508 31 (transS1Tab.getD (t % 282) []) (h.getD (t / 282) []) (x2Tab o (t / 282) (t % 282))) 152 1 chkB_1_d152) (x2c_join _ 153 154 192 (x2c_range_all (fun t => natAxpySp 384 26508 31 (transS1Tab.getD (t % 282) []) (h.getD (t / 282) []) (x2Tab o (t / 282) (t % 282))) 153 1 chkB_1_d153) (x2c_join _ 154 155 192 (x2c_range_all (fun t => natAxpySp 384 26508 31 (transS1Tab.getD (t % 282) []) (h.getD (t / 282) []) (x2Tab o (t / 282) (t % 282))) 154 1 chkB_1_d154) (x2c_join _ 155 156 192 (x2c_range_all (fun t => natAxpySp 384 26508 31 (transS1Tab.getD (t % 282) []) (h.getD (t / 282) []) (x2Tab o (t / 282) (t % 282))) 155 1 chkB_1_d155) (x2c_join _ 156 157 192 (x2c_range_all (fun t => natAxpySp 384 26508 31 (transS1Tab.getD (t % 282) []) (h.getD (t / 282) []) (x2Tab o (t / 282) (t % 282))) 156 1 chkB_1_d156) (x2c_join _ 157 158 192 (x2c_range_all (fun t => natAxpySp 384 26508 31 (transS1Tab.getD (t % 282) []) (h.getD (t / 282) []) (x2Tab o (t / 282) (t % 282))) 157 1 chkB_1_d157) (x2c_join _ 158 159 192 (x2c_range_all (fun t => natAxpySp 384 26508 31 (transS1Tab.getD (t % 282) []) (h.getD (t / 282) []) (x2Tab o (t / 282) (t % 282))) 158 1 chkB_1_d158) (x2c_join _ 159 160 192 (x2c_range_all (fun t => natAxpySp 384 26508 31 (transS1Tab.getD (t % 282) []) (h.getD (t / 282) []) (x2Tab o (t / 282) (t % 282))) 159 1 chkB_1_d159) (x2c_join _ 160 161 192 (x2c_range_all (fun t => natAxpySp 384 26508 31 (transS1Tab.getD (t % 282) []) (h.getD (t / 282) []) (x2Tab o (t / 282) (t % 282))) 160 1 chkB_1_d160) (x2c_join _ 161 162 192 (x2c_range_all (fun t => natAxpySp 384 26508 31 (transS1Tab.getD (t % 282) []) (h.getD (t / 282) []) (x2Tab o (t / 282) (t % 282))) 161 1 chkB_1_d161) (x2c_join _ 162 163 192 (x2c_range_all (fun t => natAxpySp 384 26508 31 (transS1Tab.getD (t % 282) []) (h.getD (t / 282) []) (x2Tab o (t / 282) (t % 282))) 162 1 chkB_1_d162) (x2c_join _ 163 164 192 (x2c_range_all (fun t => natAxpySp 384 26508 31 (transS1Tab.getD (t % 282) []) (h.getD (t / 282) []) (x2Tab o (t / 282) (t % 282))) 163 1 chkB_1_d163) (x2c_join _ 164 165 192 (x2c_range_all (fun t => natAxpySp 384 26508 31 (transS1Tab.getD (t % 282) []) (h.getD (t / 282) []) (x2Tab o (t / 282) (t % 282))) 164 1 chkB_1_d164) (x2c_join _ 165 166 192 (x2c_range_all (fun t => natAxpySp 384 26508 31 (transS1Tab.getD (t % 282) []) (h.getD (t / 282) []) (x2Tab o (t / 282) (t % 282))) 165 1 chkB_1_d165) (x2c_join _ 166 167 192 (x2c_range_all (fun t => natAxpySp 384 26508 31 (transS1Tab.getD (t % 282) []) (h.getD (t / 282) []) (x2Tab o (t / 282) (t % 282))) 166 1 chkB_1_d166) (x2c_join _ 167 168 192 (x2c_range_all (fun t => natAxpySp 384 26508 31 (transS1Tab.getD (t % 282) []) (h.getD (t / 282) []) (x2Tab o (t / 282) (t % 282))) 167 1 chkB_1_d167) (x2c_join _ 168 169 192 (x2c_range_all (fun t => natAxpySp 384 26508 31 (transS1Tab.getD (t % 282) []) (h.getD (t / 282) []) (x2Tab o (t / 282) (t % 282))) 168 1 chkB_1_d168) (x2c_join _ 169 170 192 (x2c_range_all (fun t => natAxpySp 384 26508 31 (transS1Tab.getD (t % 282) []) (h.getD (t / 282) []) (x2Tab o (t / 282) (t % 282))) 169 1 chkB_1_d169) (x2c_join _ 170 171 192 (x2c_range_all (fun t => natAxpySp 384 26508 31 (transS1Tab.getD (t % 282) []) (h.getD (t / 282) []) (x2Tab o (t / 282) (t % 282))) 170 1 chkB_1_d170) (x2c_join _ 171 172 192 (x2c_range_all (fun t => natAxpySp 384 26508 31 (transS1Tab.getD (t % 282) []) (h.getD (t / 282) []) (x2Tab o (t / 282) (t % 282))) 171 1 chkB_1_d171) (x2c_join _ 172 173 192 (x2c_range_all (fun t => natAxpySp 384 26508 31 (transS1Tab.getD (t % 282) []) (h.getD (t / 282) []) (x2Tab o (t / 282) (t % 282))) 172 1 chkB_1_d172) (x2c_join _ 173 174 192 (x2c_range_all (fun t => natAxpySp 384 26508 31 (transS1Tab.getD (t % 282) []) (h.getD (t / 282) []) (x2Tab o (t / 282) (t % 282))) 173 1 chkB_1_d173) (x2c_join _ 174 175 192 (x2c_range_all (fun t => natAxpySp 384 26508 31 (transS1Tab.getD (t % 282) []) (h.getD (t / 282) []) (x2Tab o (t / 282) (t % 282))) 174 1 chkB_1_d174) (x2c_join _ 175 176 192 (x2c_range_all (fun t => natAxpySp 384 26508 31 (transS1Tab.getD (t % 282) []) (h.getD (t / 282) []) (x2Tab o (t / 282) (t % 282))) 175 1 chkB_1_d175) (x2c_join _ 176 177 192 (x2c_range_all (fun t => natAxpySp 384 26508 31 (transS1Tab.getD (t % 282) []) (h.getD (t / 282) []) (x2Tab o (t / 282) (t % 282))) 176 1 chkB_1_d176) (x2c_join _ 177 178 192 (x2c_range_all (fun t => natAxpySp 384 26508 31 (transS1Tab.getD (t % 282) []) (h.getD (t / 282) []) (x2Tab o (t / 282) (t % 282))) 177 1 chkB_1_d177) (x2c_join _ 178 179 192 (x2c_range_all (fun t => natAxpySp 384 26508 31 (transS1Tab.getD (t % 282) []) (h.getD (t / 282) []) (x2Tab o (t / 282) (t % 282))) 178 1 chkB_1_d178) (x2c_join _ 179 180 192 (x2c_range_all (fun t => natAxpySp 384 26508 31 (transS1Tab.getD (t % 282) []) (h.getD (t / 282) []) (x2Tab o (t / 282) (t % 282))) 179 1 chkB_1_d179) (x2c_join _ 180 181 192 (x2c_range_all (fun t => natAxpySp 384 26508 31 (transS1Tab.getD (t % 282) []) (h.getD (t / 282) []) (x2Tab o (t / 282) (t % 282))) 180 1 chkB_1_d180) (x2c_join _ 181 182 192 (x2c_range_all (fun t => natAxpySp 384 26508 31 (transS1Tab.getD (t % 282) []) (h.getD (t / 282) []) (x2Tab o (t / 282) (t % 282))) 181 1 chkB_1_d181) (x2c_join _ 182 183 192 (x2c_range_all (fun t => natAxpySp 384 26508 31 (transS1Tab.getD (t % 282) []) (h.getD (t / 282) []) (x2Tab o (t / 282) (t % 282))) 182 1 chkB_1_d182) (x2c_join _ 183 184 192 (x2c_range_all (fun t => natAxpySp 384 26508 31 (transS1Tab.getD (t % 282) []) (h.getD (t / 282) []) (x2Tab o (t / 282) (t % 282))) 183 1 chkB_1_d183) (x2c_join _ 184 185 192 (x2c_range_all (fun t => natAxpySp 384 26508 31 (transS1Tab.getD (t % 282) []) (h.getD (t / 282) []) (x2Tab o (t / 282) (t % 282))) 184 1 chkB_1_d184) (x2c_join _ 185 186 192 (x2c_range_all (fun t => natAxpySp 384 26508 31 (transS1Tab.getD (t % 282) []) (h.getD (t / 282) []) (x2Tab o (t / 282) (t % 282))) 185 1 chkB_1_d185) (x2c_join _ 186 187 192 (x2c_range_all (fun t => natAxpySp 384 26508 31 (transS1Tab.getD (t % 282) []) (h.getD (t / 282) []) (x2Tab o (t / 282) (t % 282))) 186 1 chkB_1_d186) (x2c_join _ 187 188 192 (x2c_range_all (fun t => natAxpySp 384 26508 31 (transS1Tab.getD (t % 282) []) (h.getD (t / 282) []) (x2Tab o (t / 282) (t % 282))) 187 1 chkB_1_d187) (x2c_join _ 188 189 192 (x2c_range_all (fun t => natAxpySp 384 26508 31 (transS1Tab.getD (t % 282) []) (h.getD (t / 282) []) (x2Tab o (t / 282) (t % 282))) 188 1 chkB_1_d188) (x2c_join _ 189 190 192 (x2c_range_all (fun t => natAxpySp 384 26508 31 (transS1Tab.getD (t % 282) []) (h.getD (t / 282) []) (x2Tab o (t / 282) (t % 282))) 189 1 chkB_1_d189) (x2c_join _ 190 191 192 (x2c_range_all (fun t => natAxpySp 384 26508 31 (transS1Tab.getD (t % 282) []) (h.getD (t / 282) []) (x2Tab o (t / 282) (t % 282))) 190 1 chkB_1_d190) (x2c_range_all (fun t => natAxpySp 384 26508 31 (transS1Tab.getD (t % 282) []) (h.getD (t / 282) []) (x2Tab o (t / 282) (t % 282))) 191 1 chkB_1_d191))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))


end ThreeCopyQutritWerner.X2.CoreS1g
