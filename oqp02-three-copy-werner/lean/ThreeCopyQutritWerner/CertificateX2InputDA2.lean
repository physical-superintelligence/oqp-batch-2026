module

public import ThreeCopyQutritWerner.CertificateX2InputTA2x005
public import ThreeCopyQutritWerner.CertificateX2InputTA2x006
public import ThreeCopyQutritWerner.CertificateX2InputTA2x014
public import ThreeCopyQutritWerner.CertificateX2InputTA2x015
public import ThreeCopyQutritWerner.CertificateX2InputTA2x016
public import ThreeCopyQutritWerner.CertificateX2InputTA2x024
public import ThreeCopyQutritWerner.CertificateX2InputTA2x025
public import ThreeCopyQutritWerner.CertificateX2InputTA2x026
public import ThreeCopyQutritWerner.CertificateX2InputTA2x034
public import ThreeCopyQutritWerner.CertificateX2InputTA2x035
public import ThreeCopyQutritWerner.CertificateX2InputTA2x036
public import ThreeCopyQutritWerner.CertificateX2InputTA2x044
public import ThreeCopyQutritWerner.CertificateX2InputTA2x045
public import ThreeCopyQutritWerner.CertificateX2InputTA2x046
public import ThreeCopyQutritWerner.CertificateX2InputTA2x055
public import ThreeCopyQutritWerner.CertificateX2InputTA2x056
public import ThreeCopyQutritWerner.CertificateX2InputTA2x066
public import ThreeCopyQutritWerner.CertificateX2InputTA2x114
public import ThreeCopyQutritWerner.CertificateX2InputTA2x115
public import ThreeCopyQutritWerner.CertificateX2InputTA2x116
public import ThreeCopyQutritWerner.CertificateX2InputTA2x124
public import ThreeCopyQutritWerner.CertificateX2InputTA2x125
public import ThreeCopyQutritWerner.CertificateX2InputTA2x126
public import ThreeCopyQutritWerner.CertificateX2InputTA2x134
public import ThreeCopyQutritWerner.CertificateX2InputTA2x135
public import ThreeCopyQutritWerner.CertificateX2InputTA2x136
public import ThreeCopyQutritWerner.CertificateX2InputTA2x144
public import ThreeCopyQutritWerner.CertificateX2InputTA2x145
public import ThreeCopyQutritWerner.CertificateX2InputTA2x146
public import ThreeCopyQutritWerner.CertificateX2InputTA2x155
public import ThreeCopyQutritWerner.CertificateX2InputTA2x156
public import ThreeCopyQutritWerner.CertificateX2InputTA2x166
public import ThreeCopyQutritWerner.CertificateX2InputTA2x222
public import ThreeCopyQutritWerner.CertificateX2InputTA2x224
public import ThreeCopyQutritWerner.CertificateX2InputTA2x225
public import ThreeCopyQutritWerner.CertificateX2InputTA2x226
public import ThreeCopyQutritWerner.CertificateX2InputTA2x234
public import ThreeCopyQutritWerner.CertificateX2InputTA2x235
public import ThreeCopyQutritWerner.CertificateX2InputTA2x236
public import ThreeCopyQutritWerner.CertificateX2InputTA2x244
public import ThreeCopyQutritWerner.CertificateX2InputTA2x245
public import ThreeCopyQutritWerner.CertificateX2InputTA2x246
public import ThreeCopyQutritWerner.CertificateX2InputTA2x255
public import ThreeCopyQutritWerner.CertificateX2InputTA2x256
public import ThreeCopyQutritWerner.CertificateX2InputTA2x266
public import ThreeCopyQutritWerner.CertificateX2InputTA2x334
public import ThreeCopyQutritWerner.CertificateX2InputTA2x335
public import ThreeCopyQutritWerner.CertificateX2InputTA2x336
public import ThreeCopyQutritWerner.CertificateX2InputTA2x344
public import ThreeCopyQutritWerner.CertificateX2InputTA2x345
public import ThreeCopyQutritWerner.CertificateX2InputTA2x346
public import ThreeCopyQutritWerner.CertificateX2InputTA2x355
public import ThreeCopyQutritWerner.CertificateX2InputTA2x356
public import ThreeCopyQutritWerner.CertificateX2InputTA2x366
public import ThreeCopyQutritWerner.CertificateX2InputTA2x444
public import ThreeCopyQutritWerner.CertificateX2InputTA2x445
public import ThreeCopyQutritWerner.CertificateX2InputTA2x446
public import ThreeCopyQutritWerner.CertificateX2InputTA2x455
public import ThreeCopyQutritWerner.CertificateX2InputTA2x456
public import ThreeCopyQutritWerner.CertificateX2InputTA2x466
public import ThreeCopyQutritWerner.CertificateX2InputTA2x555
public import ThreeCopyQutritWerner.CertificateX2InputTA2x556
public import ThreeCopyQutritWerner.CertificateX2InputTA2x566
public import ThreeCopyQutritWerner.CertificateX2InputTA2x666
public import ThreeCopyQutritWerner.CertificateX2InputZA2

@[expose] public section


/-! The T-table directory of the A pipeline of sector 2, the source forms and the directory specification DirSpecA. -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option exponentiation.threshold 1000000

open scoped Matrix

namespace ThreeCopyQutritWerner.X2.InDA2
open ThreeCopyQutritWerner ThreeCopyQutritWerner.X2

noncomputable def TTaasD : Fin 8 → Fin 8 → Fin 8 → List (List ℕ) := fun a b c =>
    if a.val = 0 ∧ b.val = 0 ∧ c.val = 5 then ThreeCopyQutritWerner.X2.InK2x005.TTa else
    if a.val = 0 ∧ b.val = 0 ∧ c.val = 6 then ThreeCopyQutritWerner.X2.InK2x006.TTa else
    if a.val = 0 ∧ b.val = 1 ∧ c.val = 4 then ThreeCopyQutritWerner.X2.InK2x014.TTa else
    if a.val = 0 ∧ b.val = 1 ∧ c.val = 5 then ThreeCopyQutritWerner.X2.InK2x015.TTa else
    if a.val = 0 ∧ b.val = 1 ∧ c.val = 6 then ThreeCopyQutritWerner.X2.InK2x016.TTa else
    if a.val = 0 ∧ b.val = 2 ∧ c.val = 4 then ThreeCopyQutritWerner.X2.InK2x024.TTa else
    if a.val = 0 ∧ b.val = 2 ∧ c.val = 5 then ThreeCopyQutritWerner.X2.InK2x025.TTa else
    if a.val = 0 ∧ b.val = 2 ∧ c.val = 6 then ThreeCopyQutritWerner.X2.InK2x026.TTa else
    if a.val = 0 ∧ b.val = 3 ∧ c.val = 4 then ThreeCopyQutritWerner.X2.InK2x034.TTa else
    if a.val = 0 ∧ b.val = 3 ∧ c.val = 5 then ThreeCopyQutritWerner.X2.InK2x035.TTa else
    if a.val = 0 ∧ b.val = 3 ∧ c.val = 6 then ThreeCopyQutritWerner.X2.InK2x036.TTa else
    if a.val = 0 ∧ b.val = 4 ∧ c.val = 4 then ThreeCopyQutritWerner.X2.InK2x044.TTa else
    if a.val = 0 ∧ b.val = 4 ∧ c.val = 5 then ThreeCopyQutritWerner.X2.InK2x045.TTa else
    if a.val = 0 ∧ b.val = 4 ∧ c.val = 6 then ThreeCopyQutritWerner.X2.InK2x046.TTa else
    if a.val = 0 ∧ b.val = 5 ∧ c.val = 5 then ThreeCopyQutritWerner.X2.InK2x055.TTa else
    if a.val = 0 ∧ b.val = 5 ∧ c.val = 6 then ThreeCopyQutritWerner.X2.InK2x056.TTa else
    if a.val = 0 ∧ b.val = 6 ∧ c.val = 6 then ThreeCopyQutritWerner.X2.InK2x066.TTa else
    if a.val = 1 ∧ b.val = 1 ∧ c.val = 4 then ThreeCopyQutritWerner.X2.InK2x114.TTa else
    if a.val = 1 ∧ b.val = 1 ∧ c.val = 5 then ThreeCopyQutritWerner.X2.InK2x115.TTa else
    if a.val = 1 ∧ b.val = 1 ∧ c.val = 6 then ThreeCopyQutritWerner.X2.InK2x116.TTa else
    if a.val = 1 ∧ b.val = 2 ∧ c.val = 4 then ThreeCopyQutritWerner.X2.InK2x124.TTa else
    if a.val = 1 ∧ b.val = 2 ∧ c.val = 5 then ThreeCopyQutritWerner.X2.InK2x125.TTa else
    if a.val = 1 ∧ b.val = 2 ∧ c.val = 6 then ThreeCopyQutritWerner.X2.InK2x126.TTa else
    if a.val = 1 ∧ b.val = 3 ∧ c.val = 4 then ThreeCopyQutritWerner.X2.InK2x134.TTa else
    if a.val = 1 ∧ b.val = 3 ∧ c.val = 5 then ThreeCopyQutritWerner.X2.InK2x135.TTa else
    if a.val = 1 ∧ b.val = 3 ∧ c.val = 6 then ThreeCopyQutritWerner.X2.InK2x136.TTa else
    if a.val = 1 ∧ b.val = 4 ∧ c.val = 4 then ThreeCopyQutritWerner.X2.InK2x144.TTa else
    if a.val = 1 ∧ b.val = 4 ∧ c.val = 5 then ThreeCopyQutritWerner.X2.InK2x145.TTa else
    if a.val = 1 ∧ b.val = 4 ∧ c.val = 6 then ThreeCopyQutritWerner.X2.InK2x146.TTa else
    if a.val = 1 ∧ b.val = 5 ∧ c.val = 5 then ThreeCopyQutritWerner.X2.InK2x155.TTa else
    if a.val = 1 ∧ b.val = 5 ∧ c.val = 6 then ThreeCopyQutritWerner.X2.InK2x156.TTa else
    if a.val = 1 ∧ b.val = 6 ∧ c.val = 6 then ThreeCopyQutritWerner.X2.InK2x166.TTa else
    if a.val = 2 ∧ b.val = 2 ∧ c.val = 2 then ThreeCopyQutritWerner.X2.InK2x222.TTa else
    if a.val = 2 ∧ b.val = 2 ∧ c.val = 4 then ThreeCopyQutritWerner.X2.InK2x224.TTa else
    if a.val = 2 ∧ b.val = 2 ∧ c.val = 5 then ThreeCopyQutritWerner.X2.InK2x225.TTa else
    if a.val = 2 ∧ b.val = 2 ∧ c.val = 6 then ThreeCopyQutritWerner.X2.InK2x226.TTa else
    if a.val = 2 ∧ b.val = 3 ∧ c.val = 4 then ThreeCopyQutritWerner.X2.InK2x234.TTa else
    if a.val = 2 ∧ b.val = 3 ∧ c.val = 5 then ThreeCopyQutritWerner.X2.InK2x235.TTa else
    if a.val = 2 ∧ b.val = 3 ∧ c.val = 6 then ThreeCopyQutritWerner.X2.InK2x236.TTa else
    if a.val = 2 ∧ b.val = 4 ∧ c.val = 4 then ThreeCopyQutritWerner.X2.InK2x244.TTa else
    if a.val = 2 ∧ b.val = 4 ∧ c.val = 5 then ThreeCopyQutritWerner.X2.InK2x245.TTa else
    if a.val = 2 ∧ b.val = 4 ∧ c.val = 6 then ThreeCopyQutritWerner.X2.InK2x246.TTa else
    if a.val = 2 ∧ b.val = 5 ∧ c.val = 5 then ThreeCopyQutritWerner.X2.InK2x255.TTa else
    if a.val = 2 ∧ b.val = 5 ∧ c.val = 6 then ThreeCopyQutritWerner.X2.InK2x256.TTa else
    if a.val = 2 ∧ b.val = 6 ∧ c.val = 6 then ThreeCopyQutritWerner.X2.InK2x266.TTa else
    if a.val = 3 ∧ b.val = 3 ∧ c.val = 4 then ThreeCopyQutritWerner.X2.InK2x334.TTa else
    if a.val = 3 ∧ b.val = 3 ∧ c.val = 5 then ThreeCopyQutritWerner.X2.InK2x335.TTa else
    if a.val = 3 ∧ b.val = 3 ∧ c.val = 6 then ThreeCopyQutritWerner.X2.InK2x336.TTa else
    if a.val = 3 ∧ b.val = 4 ∧ c.val = 4 then ThreeCopyQutritWerner.X2.InK2x344.TTa else
    if a.val = 3 ∧ b.val = 4 ∧ c.val = 5 then ThreeCopyQutritWerner.X2.InK2x345.TTa else
    if a.val = 3 ∧ b.val = 4 ∧ c.val = 6 then ThreeCopyQutritWerner.X2.InK2x346.TTa else
    if a.val = 3 ∧ b.val = 5 ∧ c.val = 5 then ThreeCopyQutritWerner.X2.InK2x355.TTa else
    if a.val = 3 ∧ b.val = 5 ∧ c.val = 6 then ThreeCopyQutritWerner.X2.InK2x356.TTa else
    if a.val = 3 ∧ b.val = 6 ∧ c.val = 6 then ThreeCopyQutritWerner.X2.InK2x366.TTa else
    if a.val = 4 ∧ b.val = 4 ∧ c.val = 4 then ThreeCopyQutritWerner.X2.InK2x444.TTa else
    if a.val = 4 ∧ b.val = 4 ∧ c.val = 5 then ThreeCopyQutritWerner.X2.InK2x445.TTa else
    if a.val = 4 ∧ b.val = 4 ∧ c.val = 6 then ThreeCopyQutritWerner.X2.InK2x446.TTa else
    if a.val = 4 ∧ b.val = 5 ∧ c.val = 5 then ThreeCopyQutritWerner.X2.InK2x455.TTa else
    if a.val = 4 ∧ b.val = 5 ∧ c.val = 6 then ThreeCopyQutritWerner.X2.InK2x456.TTa else
    if a.val = 4 ∧ b.val = 6 ∧ c.val = 6 then ThreeCopyQutritWerner.X2.InK2x466.TTa else
    if a.val = 5 ∧ b.val = 5 ∧ c.val = 5 then ThreeCopyQutritWerner.X2.InK2x555.TTa else
    if a.val = 5 ∧ b.val = 5 ∧ c.val = 6 then ThreeCopyQutritWerner.X2.InK2x556.TTa else
    if a.val = 5 ∧ b.val = 6 ∧ c.val = 6 then ThreeCopyQutritWerner.X2.InK2x566.TTa else
    if a.val = 6 ∧ b.val = 6 ∧ c.val = 6 then ThreeCopyQutritWerner.X2.InK2x666.TTa else
    []
noncomputable def TCaasD : Fin 8 → Fin 8 → Fin 8 → List (List ℕ) := fun a b c =>
    if a.val = 0 ∧ b.val = 0 ∧ c.val = 5 then ThreeCopyQutritWerner.X2.InK2x005.TCa else
    if a.val = 0 ∧ b.val = 0 ∧ c.val = 6 then ThreeCopyQutritWerner.X2.InK2x006.TCa else
    if a.val = 0 ∧ b.val = 1 ∧ c.val = 4 then ThreeCopyQutritWerner.X2.InK2x014.TCa else
    if a.val = 0 ∧ b.val = 1 ∧ c.val = 5 then ThreeCopyQutritWerner.X2.InK2x015.TCa else
    if a.val = 0 ∧ b.val = 1 ∧ c.val = 6 then ThreeCopyQutritWerner.X2.InK2x016.TCa else
    if a.val = 0 ∧ b.val = 2 ∧ c.val = 4 then ThreeCopyQutritWerner.X2.InK2x024.TCa else
    if a.val = 0 ∧ b.val = 2 ∧ c.val = 5 then ThreeCopyQutritWerner.X2.InK2x025.TCa else
    if a.val = 0 ∧ b.val = 2 ∧ c.val = 6 then ThreeCopyQutritWerner.X2.InK2x026.TCa else
    if a.val = 0 ∧ b.val = 3 ∧ c.val = 4 then ThreeCopyQutritWerner.X2.InK2x034.TCa else
    if a.val = 0 ∧ b.val = 3 ∧ c.val = 5 then ThreeCopyQutritWerner.X2.InK2x035.TCa else
    if a.val = 0 ∧ b.val = 3 ∧ c.val = 6 then ThreeCopyQutritWerner.X2.InK2x036.TCa else
    if a.val = 0 ∧ b.val = 4 ∧ c.val = 4 then ThreeCopyQutritWerner.X2.InK2x044.TCa else
    if a.val = 0 ∧ b.val = 4 ∧ c.val = 5 then ThreeCopyQutritWerner.X2.InK2x045.TCa else
    if a.val = 0 ∧ b.val = 4 ∧ c.val = 6 then ThreeCopyQutritWerner.X2.InK2x046.TCa else
    if a.val = 0 ∧ b.val = 5 ∧ c.val = 5 then ThreeCopyQutritWerner.X2.InK2x055.TCa else
    if a.val = 0 ∧ b.val = 5 ∧ c.val = 6 then ThreeCopyQutritWerner.X2.InK2x056.TCa else
    if a.val = 0 ∧ b.val = 6 ∧ c.val = 6 then ThreeCopyQutritWerner.X2.InK2x066.TCa else
    if a.val = 1 ∧ b.val = 1 ∧ c.val = 4 then ThreeCopyQutritWerner.X2.InK2x114.TCa else
    if a.val = 1 ∧ b.val = 1 ∧ c.val = 5 then ThreeCopyQutritWerner.X2.InK2x115.TCa else
    if a.val = 1 ∧ b.val = 1 ∧ c.val = 6 then ThreeCopyQutritWerner.X2.InK2x116.TCa else
    if a.val = 1 ∧ b.val = 2 ∧ c.val = 4 then ThreeCopyQutritWerner.X2.InK2x124.TCa else
    if a.val = 1 ∧ b.val = 2 ∧ c.val = 5 then ThreeCopyQutritWerner.X2.InK2x125.TCa else
    if a.val = 1 ∧ b.val = 2 ∧ c.val = 6 then ThreeCopyQutritWerner.X2.InK2x126.TCa else
    if a.val = 1 ∧ b.val = 3 ∧ c.val = 4 then ThreeCopyQutritWerner.X2.InK2x134.TCa else
    if a.val = 1 ∧ b.val = 3 ∧ c.val = 5 then ThreeCopyQutritWerner.X2.InK2x135.TCa else
    if a.val = 1 ∧ b.val = 3 ∧ c.val = 6 then ThreeCopyQutritWerner.X2.InK2x136.TCa else
    if a.val = 1 ∧ b.val = 4 ∧ c.val = 4 then ThreeCopyQutritWerner.X2.InK2x144.TCa else
    if a.val = 1 ∧ b.val = 4 ∧ c.val = 5 then ThreeCopyQutritWerner.X2.InK2x145.TCa else
    if a.val = 1 ∧ b.val = 4 ∧ c.val = 6 then ThreeCopyQutritWerner.X2.InK2x146.TCa else
    if a.val = 1 ∧ b.val = 5 ∧ c.val = 5 then ThreeCopyQutritWerner.X2.InK2x155.TCa else
    if a.val = 1 ∧ b.val = 5 ∧ c.val = 6 then ThreeCopyQutritWerner.X2.InK2x156.TCa else
    if a.val = 1 ∧ b.val = 6 ∧ c.val = 6 then ThreeCopyQutritWerner.X2.InK2x166.TCa else
    if a.val = 2 ∧ b.val = 2 ∧ c.val = 2 then ThreeCopyQutritWerner.X2.InK2x222.TCa else
    if a.val = 2 ∧ b.val = 2 ∧ c.val = 4 then ThreeCopyQutritWerner.X2.InK2x224.TCa else
    if a.val = 2 ∧ b.val = 2 ∧ c.val = 5 then ThreeCopyQutritWerner.X2.InK2x225.TCa else
    if a.val = 2 ∧ b.val = 2 ∧ c.val = 6 then ThreeCopyQutritWerner.X2.InK2x226.TCa else
    if a.val = 2 ∧ b.val = 3 ∧ c.val = 4 then ThreeCopyQutritWerner.X2.InK2x234.TCa else
    if a.val = 2 ∧ b.val = 3 ∧ c.val = 5 then ThreeCopyQutritWerner.X2.InK2x235.TCa else
    if a.val = 2 ∧ b.val = 3 ∧ c.val = 6 then ThreeCopyQutritWerner.X2.InK2x236.TCa else
    if a.val = 2 ∧ b.val = 4 ∧ c.val = 4 then ThreeCopyQutritWerner.X2.InK2x244.TCa else
    if a.val = 2 ∧ b.val = 4 ∧ c.val = 5 then ThreeCopyQutritWerner.X2.InK2x245.TCa else
    if a.val = 2 ∧ b.val = 4 ∧ c.val = 6 then ThreeCopyQutritWerner.X2.InK2x246.TCa else
    if a.val = 2 ∧ b.val = 5 ∧ c.val = 5 then ThreeCopyQutritWerner.X2.InK2x255.TCa else
    if a.val = 2 ∧ b.val = 5 ∧ c.val = 6 then ThreeCopyQutritWerner.X2.InK2x256.TCa else
    if a.val = 2 ∧ b.val = 6 ∧ c.val = 6 then ThreeCopyQutritWerner.X2.InK2x266.TCa else
    if a.val = 3 ∧ b.val = 3 ∧ c.val = 4 then ThreeCopyQutritWerner.X2.InK2x334.TCa else
    if a.val = 3 ∧ b.val = 3 ∧ c.val = 5 then ThreeCopyQutritWerner.X2.InK2x335.TCa else
    if a.val = 3 ∧ b.val = 3 ∧ c.val = 6 then ThreeCopyQutritWerner.X2.InK2x336.TCa else
    if a.val = 3 ∧ b.val = 4 ∧ c.val = 4 then ThreeCopyQutritWerner.X2.InK2x344.TCa else
    if a.val = 3 ∧ b.val = 4 ∧ c.val = 5 then ThreeCopyQutritWerner.X2.InK2x345.TCa else
    if a.val = 3 ∧ b.val = 4 ∧ c.val = 6 then ThreeCopyQutritWerner.X2.InK2x346.TCa else
    if a.val = 3 ∧ b.val = 5 ∧ c.val = 5 then ThreeCopyQutritWerner.X2.InK2x355.TCa else
    if a.val = 3 ∧ b.val = 5 ∧ c.val = 6 then ThreeCopyQutritWerner.X2.InK2x356.TCa else
    if a.val = 3 ∧ b.val = 6 ∧ c.val = 6 then ThreeCopyQutritWerner.X2.InK2x366.TCa else
    if a.val = 4 ∧ b.val = 4 ∧ c.val = 4 then ThreeCopyQutritWerner.X2.InK2x444.TCa else
    if a.val = 4 ∧ b.val = 4 ∧ c.val = 5 then ThreeCopyQutritWerner.X2.InK2x445.TCa else
    if a.val = 4 ∧ b.val = 4 ∧ c.val = 6 then ThreeCopyQutritWerner.X2.InK2x446.TCa else
    if a.val = 4 ∧ b.val = 5 ∧ c.val = 5 then ThreeCopyQutritWerner.X2.InK2x455.TCa else
    if a.val = 4 ∧ b.val = 5 ∧ c.val = 6 then ThreeCopyQutritWerner.X2.InK2x456.TCa else
    if a.val = 4 ∧ b.val = 6 ∧ c.val = 6 then ThreeCopyQutritWerner.X2.InK2x466.TCa else
    if a.val = 5 ∧ b.val = 5 ∧ c.val = 5 then ThreeCopyQutritWerner.X2.InK2x555.TCa else
    if a.val = 5 ∧ b.val = 5 ∧ c.val = 6 then ThreeCopyQutritWerner.X2.InK2x556.TCa else
    if a.val = 5 ∧ b.val = 6 ∧ c.val = 6 then ThreeCopyQutritWerner.X2.InK2x566.TCa else
    if a.val = 6 ∧ b.val = 6 ∧ c.val = 6 then ThreeCopyQutritWerner.X2.InK2x666.TCa else
    []
noncomputable def TTsaaD : Fin 8 → Fin 8 → Fin 8 → List (List ℕ) := fun a b c =>
    if a.val = 0 ∧ b.val = 0 ∧ c.val = 5 then ThreeCopyQutritWerner.X2.InK2x005.TTs else
    if a.val = 0 ∧ b.val = 0 ∧ c.val = 6 then ThreeCopyQutritWerner.X2.InK2x006.TTs else
    if a.val = 0 ∧ b.val = 1 ∧ c.val = 4 then ThreeCopyQutritWerner.X2.InK2x014.TTs else
    if a.val = 0 ∧ b.val = 1 ∧ c.val = 5 then ThreeCopyQutritWerner.X2.InK2x015.TTs else
    if a.val = 0 ∧ b.val = 1 ∧ c.val = 6 then ThreeCopyQutritWerner.X2.InK2x016.TTs else
    if a.val = 0 ∧ b.val = 2 ∧ c.val = 4 then ThreeCopyQutritWerner.X2.InK2x024.TTs else
    if a.val = 0 ∧ b.val = 2 ∧ c.val = 5 then ThreeCopyQutritWerner.X2.InK2x025.TTs else
    if a.val = 0 ∧ b.val = 2 ∧ c.val = 6 then ThreeCopyQutritWerner.X2.InK2x026.TTs else
    if a.val = 0 ∧ b.val = 3 ∧ c.val = 4 then ThreeCopyQutritWerner.X2.InK2x034.TTs else
    if a.val = 0 ∧ b.val = 3 ∧ c.val = 5 then ThreeCopyQutritWerner.X2.InK2x035.TTs else
    if a.val = 0 ∧ b.val = 3 ∧ c.val = 6 then ThreeCopyQutritWerner.X2.InK2x036.TTs else
    if a.val = 0 ∧ b.val = 4 ∧ c.val = 4 then ThreeCopyQutritWerner.X2.InK2x044.TTs else
    if a.val = 0 ∧ b.val = 4 ∧ c.val = 5 then ThreeCopyQutritWerner.X2.InK2x045.TTs else
    if a.val = 0 ∧ b.val = 4 ∧ c.val = 6 then ThreeCopyQutritWerner.X2.InK2x046.TTs else
    if a.val = 0 ∧ b.val = 5 ∧ c.val = 5 then ThreeCopyQutritWerner.X2.InK2x055.TTs else
    if a.val = 0 ∧ b.val = 5 ∧ c.val = 6 then ThreeCopyQutritWerner.X2.InK2x056.TTs else
    if a.val = 0 ∧ b.val = 6 ∧ c.val = 6 then ThreeCopyQutritWerner.X2.InK2x066.TTs else
    if a.val = 1 ∧ b.val = 1 ∧ c.val = 4 then ThreeCopyQutritWerner.X2.InK2x114.TTs else
    if a.val = 1 ∧ b.val = 1 ∧ c.val = 5 then ThreeCopyQutritWerner.X2.InK2x115.TTs else
    if a.val = 1 ∧ b.val = 1 ∧ c.val = 6 then ThreeCopyQutritWerner.X2.InK2x116.TTs else
    if a.val = 1 ∧ b.val = 2 ∧ c.val = 4 then ThreeCopyQutritWerner.X2.InK2x124.TTs else
    if a.val = 1 ∧ b.val = 2 ∧ c.val = 5 then ThreeCopyQutritWerner.X2.InK2x125.TTs else
    if a.val = 1 ∧ b.val = 2 ∧ c.val = 6 then ThreeCopyQutritWerner.X2.InK2x126.TTs else
    if a.val = 1 ∧ b.val = 3 ∧ c.val = 4 then ThreeCopyQutritWerner.X2.InK2x134.TTs else
    if a.val = 1 ∧ b.val = 3 ∧ c.val = 5 then ThreeCopyQutritWerner.X2.InK2x135.TTs else
    if a.val = 1 ∧ b.val = 3 ∧ c.val = 6 then ThreeCopyQutritWerner.X2.InK2x136.TTs else
    if a.val = 1 ∧ b.val = 4 ∧ c.val = 4 then ThreeCopyQutritWerner.X2.InK2x144.TTs else
    if a.val = 1 ∧ b.val = 4 ∧ c.val = 5 then ThreeCopyQutritWerner.X2.InK2x145.TTs else
    if a.val = 1 ∧ b.val = 4 ∧ c.val = 6 then ThreeCopyQutritWerner.X2.InK2x146.TTs else
    if a.val = 1 ∧ b.val = 5 ∧ c.val = 5 then ThreeCopyQutritWerner.X2.InK2x155.TTs else
    if a.val = 1 ∧ b.val = 5 ∧ c.val = 6 then ThreeCopyQutritWerner.X2.InK2x156.TTs else
    if a.val = 1 ∧ b.val = 6 ∧ c.val = 6 then ThreeCopyQutritWerner.X2.InK2x166.TTs else
    if a.val = 2 ∧ b.val = 2 ∧ c.val = 2 then ThreeCopyQutritWerner.X2.InK2x222.TTs else
    if a.val = 2 ∧ b.val = 2 ∧ c.val = 4 then ThreeCopyQutritWerner.X2.InK2x224.TTs else
    if a.val = 2 ∧ b.val = 2 ∧ c.val = 5 then ThreeCopyQutritWerner.X2.InK2x225.TTs else
    if a.val = 2 ∧ b.val = 2 ∧ c.val = 6 then ThreeCopyQutritWerner.X2.InK2x226.TTs else
    if a.val = 2 ∧ b.val = 3 ∧ c.val = 4 then ThreeCopyQutritWerner.X2.InK2x234.TTs else
    if a.val = 2 ∧ b.val = 3 ∧ c.val = 5 then ThreeCopyQutritWerner.X2.InK2x235.TTs else
    if a.val = 2 ∧ b.val = 3 ∧ c.val = 6 then ThreeCopyQutritWerner.X2.InK2x236.TTs else
    if a.val = 2 ∧ b.val = 4 ∧ c.val = 4 then ThreeCopyQutritWerner.X2.InK2x244.TTs else
    if a.val = 2 ∧ b.val = 4 ∧ c.val = 5 then ThreeCopyQutritWerner.X2.InK2x245.TTs else
    if a.val = 2 ∧ b.val = 4 ∧ c.val = 6 then ThreeCopyQutritWerner.X2.InK2x246.TTs else
    if a.val = 2 ∧ b.val = 5 ∧ c.val = 5 then ThreeCopyQutritWerner.X2.InK2x255.TTs else
    if a.val = 2 ∧ b.val = 5 ∧ c.val = 6 then ThreeCopyQutritWerner.X2.InK2x256.TTs else
    if a.val = 2 ∧ b.val = 6 ∧ c.val = 6 then ThreeCopyQutritWerner.X2.InK2x266.TTs else
    if a.val = 3 ∧ b.val = 3 ∧ c.val = 4 then ThreeCopyQutritWerner.X2.InK2x334.TTs else
    if a.val = 3 ∧ b.val = 3 ∧ c.val = 5 then ThreeCopyQutritWerner.X2.InK2x335.TTs else
    if a.val = 3 ∧ b.val = 3 ∧ c.val = 6 then ThreeCopyQutritWerner.X2.InK2x336.TTs else
    if a.val = 3 ∧ b.val = 4 ∧ c.val = 4 then ThreeCopyQutritWerner.X2.InK2x344.TTs else
    if a.val = 3 ∧ b.val = 4 ∧ c.val = 5 then ThreeCopyQutritWerner.X2.InK2x345.TTs else
    if a.val = 3 ∧ b.val = 4 ∧ c.val = 6 then ThreeCopyQutritWerner.X2.InK2x346.TTs else
    if a.val = 3 ∧ b.val = 5 ∧ c.val = 5 then ThreeCopyQutritWerner.X2.InK2x355.TTs else
    if a.val = 3 ∧ b.val = 5 ∧ c.val = 6 then ThreeCopyQutritWerner.X2.InK2x356.TTs else
    if a.val = 3 ∧ b.val = 6 ∧ c.val = 6 then ThreeCopyQutritWerner.X2.InK2x366.TTs else
    if a.val = 4 ∧ b.val = 4 ∧ c.val = 4 then ThreeCopyQutritWerner.X2.InK2x444.TTs else
    if a.val = 4 ∧ b.val = 4 ∧ c.val = 5 then ThreeCopyQutritWerner.X2.InK2x445.TTs else
    if a.val = 4 ∧ b.val = 4 ∧ c.val = 6 then ThreeCopyQutritWerner.X2.InK2x446.TTs else
    if a.val = 4 ∧ b.val = 5 ∧ c.val = 5 then ThreeCopyQutritWerner.X2.InK2x455.TTs else
    if a.val = 4 ∧ b.val = 5 ∧ c.val = 6 then ThreeCopyQutritWerner.X2.InK2x456.TTs else
    if a.val = 4 ∧ b.val = 6 ∧ c.val = 6 then ThreeCopyQutritWerner.X2.InK2x466.TTs else
    if a.val = 5 ∧ b.val = 5 ∧ c.val = 5 then ThreeCopyQutritWerner.X2.InK2x555.TTs else
    if a.val = 5 ∧ b.val = 5 ∧ c.val = 6 then ThreeCopyQutritWerner.X2.InK2x556.TTs else
    if a.val = 5 ∧ b.val = 6 ∧ c.val = 6 then ThreeCopyQutritWerner.X2.InK2x566.TTs else
    if a.val = 6 ∧ b.val = 6 ∧ c.val = 6 then ThreeCopyQutritWerner.X2.InK2x666.TTs else
    []
noncomputable def TCasaD : Fin 8 → Fin 8 → Fin 8 → List (List ℕ) := fun a b c =>
    if a.val = 0 ∧ b.val = 0 ∧ c.val = 5 then ThreeCopyQutritWerner.X2.InK2x005.TCs else
    if a.val = 0 ∧ b.val = 0 ∧ c.val = 6 then ThreeCopyQutritWerner.X2.InK2x006.TCs else
    if a.val = 0 ∧ b.val = 1 ∧ c.val = 4 then ThreeCopyQutritWerner.X2.InK2x014.TCs else
    if a.val = 0 ∧ b.val = 1 ∧ c.val = 5 then ThreeCopyQutritWerner.X2.InK2x015.TCs else
    if a.val = 0 ∧ b.val = 1 ∧ c.val = 6 then ThreeCopyQutritWerner.X2.InK2x016.TCs else
    if a.val = 0 ∧ b.val = 2 ∧ c.val = 4 then ThreeCopyQutritWerner.X2.InK2x024.TCs else
    if a.val = 0 ∧ b.val = 2 ∧ c.val = 5 then ThreeCopyQutritWerner.X2.InK2x025.TCs else
    if a.val = 0 ∧ b.val = 2 ∧ c.val = 6 then ThreeCopyQutritWerner.X2.InK2x026.TCs else
    if a.val = 0 ∧ b.val = 3 ∧ c.val = 4 then ThreeCopyQutritWerner.X2.InK2x034.TCs else
    if a.val = 0 ∧ b.val = 3 ∧ c.val = 5 then ThreeCopyQutritWerner.X2.InK2x035.TCs else
    if a.val = 0 ∧ b.val = 3 ∧ c.val = 6 then ThreeCopyQutritWerner.X2.InK2x036.TCs else
    if a.val = 0 ∧ b.val = 4 ∧ c.val = 4 then ThreeCopyQutritWerner.X2.InK2x044.TCs else
    if a.val = 0 ∧ b.val = 4 ∧ c.val = 5 then ThreeCopyQutritWerner.X2.InK2x045.TCs else
    if a.val = 0 ∧ b.val = 4 ∧ c.val = 6 then ThreeCopyQutritWerner.X2.InK2x046.TCs else
    if a.val = 0 ∧ b.val = 5 ∧ c.val = 5 then ThreeCopyQutritWerner.X2.InK2x055.TCs else
    if a.val = 0 ∧ b.val = 5 ∧ c.val = 6 then ThreeCopyQutritWerner.X2.InK2x056.TCs else
    if a.val = 0 ∧ b.val = 6 ∧ c.val = 6 then ThreeCopyQutritWerner.X2.InK2x066.TCs else
    if a.val = 1 ∧ b.val = 1 ∧ c.val = 4 then ThreeCopyQutritWerner.X2.InK2x114.TCs else
    if a.val = 1 ∧ b.val = 1 ∧ c.val = 5 then ThreeCopyQutritWerner.X2.InK2x115.TCs else
    if a.val = 1 ∧ b.val = 1 ∧ c.val = 6 then ThreeCopyQutritWerner.X2.InK2x116.TCs else
    if a.val = 1 ∧ b.val = 2 ∧ c.val = 4 then ThreeCopyQutritWerner.X2.InK2x124.TCs else
    if a.val = 1 ∧ b.val = 2 ∧ c.val = 5 then ThreeCopyQutritWerner.X2.InK2x125.TCs else
    if a.val = 1 ∧ b.val = 2 ∧ c.val = 6 then ThreeCopyQutritWerner.X2.InK2x126.TCs else
    if a.val = 1 ∧ b.val = 3 ∧ c.val = 4 then ThreeCopyQutritWerner.X2.InK2x134.TCs else
    if a.val = 1 ∧ b.val = 3 ∧ c.val = 5 then ThreeCopyQutritWerner.X2.InK2x135.TCs else
    if a.val = 1 ∧ b.val = 3 ∧ c.val = 6 then ThreeCopyQutritWerner.X2.InK2x136.TCs else
    if a.val = 1 ∧ b.val = 4 ∧ c.val = 4 then ThreeCopyQutritWerner.X2.InK2x144.TCs else
    if a.val = 1 ∧ b.val = 4 ∧ c.val = 5 then ThreeCopyQutritWerner.X2.InK2x145.TCs else
    if a.val = 1 ∧ b.val = 4 ∧ c.val = 6 then ThreeCopyQutritWerner.X2.InK2x146.TCs else
    if a.val = 1 ∧ b.val = 5 ∧ c.val = 5 then ThreeCopyQutritWerner.X2.InK2x155.TCs else
    if a.val = 1 ∧ b.val = 5 ∧ c.val = 6 then ThreeCopyQutritWerner.X2.InK2x156.TCs else
    if a.val = 1 ∧ b.val = 6 ∧ c.val = 6 then ThreeCopyQutritWerner.X2.InK2x166.TCs else
    if a.val = 2 ∧ b.val = 2 ∧ c.val = 2 then ThreeCopyQutritWerner.X2.InK2x222.TCs else
    if a.val = 2 ∧ b.val = 2 ∧ c.val = 4 then ThreeCopyQutritWerner.X2.InK2x224.TCs else
    if a.val = 2 ∧ b.val = 2 ∧ c.val = 5 then ThreeCopyQutritWerner.X2.InK2x225.TCs else
    if a.val = 2 ∧ b.val = 2 ∧ c.val = 6 then ThreeCopyQutritWerner.X2.InK2x226.TCs else
    if a.val = 2 ∧ b.val = 3 ∧ c.val = 4 then ThreeCopyQutritWerner.X2.InK2x234.TCs else
    if a.val = 2 ∧ b.val = 3 ∧ c.val = 5 then ThreeCopyQutritWerner.X2.InK2x235.TCs else
    if a.val = 2 ∧ b.val = 3 ∧ c.val = 6 then ThreeCopyQutritWerner.X2.InK2x236.TCs else
    if a.val = 2 ∧ b.val = 4 ∧ c.val = 4 then ThreeCopyQutritWerner.X2.InK2x244.TCs else
    if a.val = 2 ∧ b.val = 4 ∧ c.val = 5 then ThreeCopyQutritWerner.X2.InK2x245.TCs else
    if a.val = 2 ∧ b.val = 4 ∧ c.val = 6 then ThreeCopyQutritWerner.X2.InK2x246.TCs else
    if a.val = 2 ∧ b.val = 5 ∧ c.val = 5 then ThreeCopyQutritWerner.X2.InK2x255.TCs else
    if a.val = 2 ∧ b.val = 5 ∧ c.val = 6 then ThreeCopyQutritWerner.X2.InK2x256.TCs else
    if a.val = 2 ∧ b.val = 6 ∧ c.val = 6 then ThreeCopyQutritWerner.X2.InK2x266.TCs else
    if a.val = 3 ∧ b.val = 3 ∧ c.val = 4 then ThreeCopyQutritWerner.X2.InK2x334.TCs else
    if a.val = 3 ∧ b.val = 3 ∧ c.val = 5 then ThreeCopyQutritWerner.X2.InK2x335.TCs else
    if a.val = 3 ∧ b.val = 3 ∧ c.val = 6 then ThreeCopyQutritWerner.X2.InK2x336.TCs else
    if a.val = 3 ∧ b.val = 4 ∧ c.val = 4 then ThreeCopyQutritWerner.X2.InK2x344.TCs else
    if a.val = 3 ∧ b.val = 4 ∧ c.val = 5 then ThreeCopyQutritWerner.X2.InK2x345.TCs else
    if a.val = 3 ∧ b.val = 4 ∧ c.val = 6 then ThreeCopyQutritWerner.X2.InK2x346.TCs else
    if a.val = 3 ∧ b.val = 5 ∧ c.val = 5 then ThreeCopyQutritWerner.X2.InK2x355.TCs else
    if a.val = 3 ∧ b.val = 5 ∧ c.val = 6 then ThreeCopyQutritWerner.X2.InK2x356.TCs else
    if a.val = 3 ∧ b.val = 6 ∧ c.val = 6 then ThreeCopyQutritWerner.X2.InK2x366.TCs else
    if a.val = 4 ∧ b.val = 4 ∧ c.val = 4 then ThreeCopyQutritWerner.X2.InK2x444.TCs else
    if a.val = 4 ∧ b.val = 4 ∧ c.val = 5 then ThreeCopyQutritWerner.X2.InK2x445.TCs else
    if a.val = 4 ∧ b.val = 4 ∧ c.val = 6 then ThreeCopyQutritWerner.X2.InK2x446.TCs else
    if a.val = 4 ∧ b.val = 5 ∧ c.val = 5 then ThreeCopyQutritWerner.X2.InK2x455.TCs else
    if a.val = 4 ∧ b.val = 5 ∧ c.val = 6 then ThreeCopyQutritWerner.X2.InK2x456.TCs else
    if a.val = 4 ∧ b.val = 6 ∧ c.val = 6 then ThreeCopyQutritWerner.X2.InK2x466.TCs else
    if a.val = 5 ∧ b.val = 5 ∧ c.val = 5 then ThreeCopyQutritWerner.X2.InK2x555.TCs else
    if a.val = 5 ∧ b.val = 5 ∧ c.val = 6 then ThreeCopyQutritWerner.X2.InK2x556.TCs else
    if a.val = 5 ∧ b.val = 6 ∧ c.val = 6 then ThreeCopyQutritWerner.X2.InK2x566.TCs else
    if a.val = 6 ∧ b.val = 6 ∧ c.val = 6 then ThreeCopyQutritWerner.X2.InK2x666.TCs else
    []
def Zd : Fin 8 → Fin 8 → Fin 8 → Bool := fun a b c => !((a.val == 0 && b.val == 0 && c.val == 5) ||
    (a.val == 0 && b.val == 0 && c.val == 6) ||
    (a.val == 0 && b.val == 1 && c.val == 4) ||
    (a.val == 0 && b.val == 1 && c.val == 5) ||
    (a.val == 0 && b.val == 1 && c.val == 6) ||
    (a.val == 0 && b.val == 2 && c.val == 4) ||
    (a.val == 0 && b.val == 2 && c.val == 5) ||
    (a.val == 0 && b.val == 2 && c.val == 6) ||
    (a.val == 0 && b.val == 3 && c.val == 4) ||
    (a.val == 0 && b.val == 3 && c.val == 5) ||
    (a.val == 0 && b.val == 3 && c.val == 6) ||
    (a.val == 0 && b.val == 4 && c.val == 4) ||
    (a.val == 0 && b.val == 4 && c.val == 5) ||
    (a.val == 0 && b.val == 4 && c.val == 6) ||
    (a.val == 0 && b.val == 5 && c.val == 5) ||
    (a.val == 0 && b.val == 5 && c.val == 6) ||
    (a.val == 0 && b.val == 6 && c.val == 6) ||
    (a.val == 1 && b.val == 1 && c.val == 4) ||
    (a.val == 1 && b.val == 1 && c.val == 5) ||
    (a.val == 1 && b.val == 1 && c.val == 6) ||
    (a.val == 1 && b.val == 2 && c.val == 4) ||
    (a.val == 1 && b.val == 2 && c.val == 5) ||
    (a.val == 1 && b.val == 2 && c.val == 6) ||
    (a.val == 1 && b.val == 3 && c.val == 4) ||
    (a.val == 1 && b.val == 3 && c.val == 5) ||
    (a.val == 1 && b.val == 3 && c.val == 6) ||
    (a.val == 1 && b.val == 4 && c.val == 4) ||
    (a.val == 1 && b.val == 4 && c.val == 5) ||
    (a.val == 1 && b.val == 4 && c.val == 6) ||
    (a.val == 1 && b.val == 5 && c.val == 5) ||
    (a.val == 1 && b.val == 5 && c.val == 6) ||
    (a.val == 1 && b.val == 6 && c.val == 6) ||
    (a.val == 2 && b.val == 2 && c.val == 2) ||
    (a.val == 2 && b.val == 2 && c.val == 4) ||
    (a.val == 2 && b.val == 2 && c.val == 5) ||
    (a.val == 2 && b.val == 2 && c.val == 6) ||
    (a.val == 2 && b.val == 3 && c.val == 4) ||
    (a.val == 2 && b.val == 3 && c.val == 5) ||
    (a.val == 2 && b.val == 3 && c.val == 6) ||
    (a.val == 2 && b.val == 4 && c.val == 4) ||
    (a.val == 2 && b.val == 4 && c.val == 5) ||
    (a.val == 2 && b.val == 4 && c.val == 6) ||
    (a.val == 2 && b.val == 5 && c.val == 5) ||
    (a.val == 2 && b.val == 5 && c.val == 6) ||
    (a.val == 2 && b.val == 6 && c.val == 6) ||
    (a.val == 3 && b.val == 3 && c.val == 4) ||
    (a.val == 3 && b.val == 3 && c.val == 5) ||
    (a.val == 3 && b.val == 3 && c.val == 6) ||
    (a.val == 3 && b.val == 4 && c.val == 4) ||
    (a.val == 3 && b.val == 4 && c.val == 5) ||
    (a.val == 3 && b.val == 4 && c.val == 6) ||
    (a.val == 3 && b.val == 5 && c.val == 5) ||
    (a.val == 3 && b.val == 5 && c.val == 6) ||
    (a.val == 3 && b.val == 6 && c.val == 6) ||
    (a.val == 4 && b.val == 4 && c.val == 4) ||
    (a.val == 4 && b.val == 4 && c.val == 5) ||
    (a.val == 4 && b.val == 4 && c.val == 6) ||
    (a.val == 4 && b.val == 5 && c.val == 5) ||
    (a.val == 4 && b.val == 5 && c.val == 6) ||
    (a.val == 4 && b.val == 6 && c.val == 6) ||
    (a.val == 5 && b.val == 5 && c.val == 5) ||
    (a.val == 5 && b.val == 5 && c.val == 6) ||
    (a.val == 5 && b.val == 6 && c.val == 6) ||
    (a.val == 6 && b.val == 6 && c.val == 6))
def corrKeys : List (x2Key 2) := [⟨54, by decide⟩]
def SrcForm (N : X2Blocks 2) : Prop := (∀ k : x2Key 2, k ∉ corrKeys → N k = x2TrialForm 2 k) ∧ N ⟨54, by decide⟩ = x2CorrForm 2 ⟨54, by decide⟩ 55 ThreeCopyQutritWerner.X2.InK2x146.K2x146k0c ThreeCopyQutritWerner.X2.InK2x146.A2x146k0c

theorem dirSpecA (N : X2Blocks 2) (hN : ∀ k, (N k)ᵀ = N k) (hsrc : SrcForm N) : DirSpecA 2 N TTaasD TCaasD TTsaaD TCasaD Zd := by
  intro t0 t1 t2 h01 h12
  obtain ⟨htr, hc54⟩ := hsrc
  fin_cases t0 <;> fin_cases t1 <;> fin_cases t2 <;>
    first | exact absurd h01 (by decide) | exact absurd h12 (by decide) | skip
  · exact ⟨fun _ => InZA2.z000 N hN , fun h => absurd h (by decide)⟩
  · exact ⟨fun _ => InZA2.z001 N hN , fun h => absurd h (by decide)⟩
  · exact ⟨fun _ => InZA2.z002 N hN , fun h => absurd h (by decide)⟩
  · exact ⟨fun _ => InZA2.z003 N hN (htr ⟨0, by decide⟩ (by decide)), fun h => absurd h (by decide)⟩
  · exact ⟨fun _ => InZA2.z004 N hN (htr ⟨1, by decide⟩ (by decide)), fun h => absurd h (by decide)⟩
  · exact ⟨fun h => absurd h (by decide), fun _ => ThreeCopyQutritWerner.X2.InK2x005.specA N hN (htr ⟨2, by decide⟩ (by decide))⟩
  · exact ⟨fun h => absurd h (by decide), fun _ => ThreeCopyQutritWerner.X2.InK2x006.specA N hN (htr ⟨3, by decide⟩ (by decide))⟩
  · exact ⟨fun _ => InZA2.z007 N, fun h => absurd h (by decide)⟩
  · exact ⟨fun _ => InZA2.z011 N hN (htr ⟨4, by decide⟩ (by decide)), fun h => absurd h (by decide)⟩
  · exact ⟨fun _ => InZA2.z012 N hN (htr ⟨5, by decide⟩ (by decide)), fun h => absurd h (by decide)⟩
  · exact ⟨fun _ => InZA2.z013 N hN (htr ⟨6, by decide⟩ (by decide)), fun h => absurd h (by decide)⟩
  · exact ⟨fun h => absurd h (by decide), fun _ => ThreeCopyQutritWerner.X2.InK2x014.specA N hN (htr ⟨7, by decide⟩ (by decide))⟩
  · exact ⟨fun h => absurd h (by decide), fun _ => ThreeCopyQutritWerner.X2.InK2x015.specA N hN (htr ⟨8, by decide⟩ (by decide))⟩
  · exact ⟨fun h => absurd h (by decide), fun _ => ThreeCopyQutritWerner.X2.InK2x016.specA N hN (htr ⟨9, by decide⟩ (by decide))⟩
  · exact ⟨fun _ => InZA2.z017 N, fun h => absurd h (by decide)⟩
  · exact ⟨fun _ => InZA2.z022 N hN (htr ⟨10, by decide⟩ (by decide)), fun h => absurd h (by decide)⟩
  · exact ⟨fun _ => InZA2.z023 N hN (htr ⟨11, by decide⟩ (by decide)), fun h => absurd h (by decide)⟩
  · exact ⟨fun h => absurd h (by decide), fun _ => ThreeCopyQutritWerner.X2.InK2x024.specA N hN (htr ⟨12, by decide⟩ (by decide))⟩
  · exact ⟨fun h => absurd h (by decide), fun _ => ThreeCopyQutritWerner.X2.InK2x025.specA N hN (htr ⟨13, by decide⟩ (by decide))⟩
  · exact ⟨fun h => absurd h (by decide), fun _ => ThreeCopyQutritWerner.X2.InK2x026.specA N hN (htr ⟨14, by decide⟩ (by decide))⟩
  · exact ⟨fun _ => InZA2.z027 N, fun h => absurd h (by decide)⟩
  · exact ⟨fun _ => InZA2.z033 N hN (htr ⟨15, by decide⟩ (by decide)), fun h => absurd h (by decide)⟩
  · exact ⟨fun h => absurd h (by decide), fun _ => ThreeCopyQutritWerner.X2.InK2x034.specA N hN (htr ⟨16, by decide⟩ (by decide))⟩
  · exact ⟨fun h => absurd h (by decide), fun _ => ThreeCopyQutritWerner.X2.InK2x035.specA N hN (htr ⟨17, by decide⟩ (by decide))⟩
  · exact ⟨fun h => absurd h (by decide), fun _ => ThreeCopyQutritWerner.X2.InK2x036.specA N hN (htr ⟨18, by decide⟩ (by decide))⟩
  · exact ⟨fun _ => InZA2.z037 N, fun h => absurd h (by decide)⟩
  · exact ⟨fun h => absurd h (by decide), fun _ => ThreeCopyQutritWerner.X2.InK2x044.specA N hN (htr ⟨19, by decide⟩ (by decide)) (htr ⟨20, by decide⟩ (by decide))⟩
  · exact ⟨fun h => absurd h (by decide), fun _ => ThreeCopyQutritWerner.X2.InK2x045.specA N hN (htr ⟨21, by decide⟩ (by decide))⟩
  · exact ⟨fun h => absurd h (by decide), fun _ => ThreeCopyQutritWerner.X2.InK2x046.specA N hN (htr ⟨22, by decide⟩ (by decide))⟩
  · exact ⟨fun _ => InZA2.z047 N, fun h => absurd h (by decide)⟩
  · exact ⟨fun h => absurd h (by decide), fun _ => ThreeCopyQutritWerner.X2.InK2x055.specA N hN (htr ⟨23, by decide⟩ (by decide)) (htr ⟨24, by decide⟩ (by decide))⟩
  · exact ⟨fun h => absurd h (by decide), fun _ => ThreeCopyQutritWerner.X2.InK2x056.specA N hN (htr ⟨25, by decide⟩ (by decide))⟩
  · exact ⟨fun _ => InZA2.z057 N, fun h => absurd h (by decide)⟩
  · exact ⟨fun h => absurd h (by decide), fun _ => ThreeCopyQutritWerner.X2.InK2x066.specA N hN (htr ⟨26, by decide⟩ (by decide)) (htr ⟨27, by decide⟩ (by decide))⟩
  · exact ⟨fun _ => InZA2.z067 N, fun h => absurd h (by decide)⟩
  · exact ⟨fun _ => InZA2.z077 N, fun h => absurd h (by decide)⟩
  · exact ⟨fun _ => InZA2.z111 N hN (htr ⟨28, by decide⟩ (by decide)) (htr ⟨29, by decide⟩ (by decide)), fun h => absurd h (by decide)⟩
  · exact ⟨fun _ => InZA2.z112 N hN (htr ⟨30, by decide⟩ (by decide)) (htr ⟨31, by decide⟩ (by decide)), fun h => absurd h (by decide)⟩
  · exact ⟨fun _ => InZA2.z113 N hN (htr ⟨32, by decide⟩ (by decide)) (htr ⟨33, by decide⟩ (by decide)), fun h => absurd h (by decide)⟩
  · exact ⟨fun h => absurd h (by decide), fun _ => ThreeCopyQutritWerner.X2.InK2x114.specA N hN (htr ⟨34, by decide⟩ (by decide)) (htr ⟨35, by decide⟩ (by decide))⟩
  · exact ⟨fun h => absurd h (by decide), fun _ => ThreeCopyQutritWerner.X2.InK2x115.specA N hN (htr ⟨36, by decide⟩ (by decide)) (htr ⟨37, by decide⟩ (by decide))⟩
  · exact ⟨fun h => absurd h (by decide), fun _ => ThreeCopyQutritWerner.X2.InK2x116.specA N hN (htr ⟨38, by decide⟩ (by decide)) (htr ⟨39, by decide⟩ (by decide))⟩
  · exact ⟨fun _ => InZA2.z117 N, fun h => absurd h (by decide)⟩
  · exact ⟨fun _ => InZA2.z122 N hN (htr ⟨40, by decide⟩ (by decide)) (htr ⟨41, by decide⟩ (by decide)), fun h => absurd h (by decide)⟩
  · exact ⟨fun _ => InZA2.z123 N hN (htr ⟨42, by decide⟩ (by decide)), fun h => absurd h (by decide)⟩
  · exact ⟨fun h => absurd h (by decide), fun _ => ThreeCopyQutritWerner.X2.InK2x124.specA N hN (htr ⟨43, by decide⟩ (by decide))⟩
  · exact ⟨fun h => absurd h (by decide), fun _ => ThreeCopyQutritWerner.X2.InK2x125.specA N hN (htr ⟨44, by decide⟩ (by decide))⟩
  · exact ⟨fun h => absurd h (by decide), fun _ => ThreeCopyQutritWerner.X2.InK2x126.specA N hN (htr ⟨45, by decide⟩ (by decide))⟩
  · exact ⟨fun _ => InZA2.z127 N, fun h => absurd h (by decide)⟩
  · exact ⟨fun _ => InZA2.z133 N hN (htr ⟨46, by decide⟩ (by decide)) (htr ⟨47, by decide⟩ (by decide)), fun h => absurd h (by decide)⟩
  · exact ⟨fun h => absurd h (by decide), fun _ => ThreeCopyQutritWerner.X2.InK2x134.specA N hN (htr ⟨48, by decide⟩ (by decide))⟩
  · exact ⟨fun h => absurd h (by decide), fun _ => ThreeCopyQutritWerner.X2.InK2x135.specA N hN (htr ⟨49, by decide⟩ (by decide))⟩
  · exact ⟨fun h => absurd h (by decide), fun _ => ThreeCopyQutritWerner.X2.InK2x136.specA N hN (htr ⟨50, by decide⟩ (by decide))⟩
  · exact ⟨fun _ => InZA2.z137 N, fun h => absurd h (by decide)⟩
  · exact ⟨fun h => absurd h (by decide), fun _ => ThreeCopyQutritWerner.X2.InK2x144.specA N hN (htr ⟨51, by decide⟩ (by decide)) (htr ⟨52, by decide⟩ (by decide))⟩
  · exact ⟨fun h => absurd h (by decide), fun _ => ThreeCopyQutritWerner.X2.InK2x145.specA N hN (htr ⟨53, by decide⟩ (by decide))⟩
  · exact ⟨fun h => absurd h (by decide), fun _ => ThreeCopyQutritWerner.X2.InK2x146.specA N hN hc54⟩
  · exact ⟨fun _ => InZA2.z147 N, fun h => absurd h (by decide)⟩
  · exact ⟨fun h => absurd h (by decide), fun _ => ThreeCopyQutritWerner.X2.InK2x155.specA N hN (htr ⟨55, by decide⟩ (by decide)) (htr ⟨56, by decide⟩ (by decide))⟩
  · exact ⟨fun h => absurd h (by decide), fun _ => ThreeCopyQutritWerner.X2.InK2x156.specA N hN (htr ⟨57, by decide⟩ (by decide))⟩
  · exact ⟨fun _ => InZA2.z157 N, fun h => absurd h (by decide)⟩
  · exact ⟨fun h => absurd h (by decide), fun _ => ThreeCopyQutritWerner.X2.InK2x166.specA N hN (htr ⟨58, by decide⟩ (by decide)) (htr ⟨59, by decide⟩ (by decide))⟩
  · exact ⟨fun _ => InZA2.z167 N, fun h => absurd h (by decide)⟩
  · exact ⟨fun _ => InZA2.z177 N, fun h => absurd h (by decide)⟩
  · exact ⟨fun h => absurd h (by decide), fun _ => ThreeCopyQutritWerner.X2.InK2x222.specA N hN (htr ⟨60, by decide⟩ (by decide)) (htr ⟨61, by decide⟩ (by decide))⟩
  · exact ⟨fun _ => InZA2.z223 N hN (htr ⟨62, by decide⟩ (by decide)) (htr ⟨63, by decide⟩ (by decide)), fun h => absurd h (by decide)⟩
  · exact ⟨fun h => absurd h (by decide), fun _ => ThreeCopyQutritWerner.X2.InK2x224.specA N hN (htr ⟨64, by decide⟩ (by decide)) (htr ⟨65, by decide⟩ (by decide))⟩
  · exact ⟨fun h => absurd h (by decide), fun _ => ThreeCopyQutritWerner.X2.InK2x225.specA N hN (htr ⟨66, by decide⟩ (by decide)) (htr ⟨67, by decide⟩ (by decide))⟩
  · exact ⟨fun h => absurd h (by decide), fun _ => ThreeCopyQutritWerner.X2.InK2x226.specA N hN (htr ⟨68, by decide⟩ (by decide)) (htr ⟨69, by decide⟩ (by decide))⟩
  · exact ⟨fun _ => InZA2.z227 N, fun h => absurd h (by decide)⟩
  · exact ⟨fun _ => InZA2.z233 N hN (htr ⟨70, by decide⟩ (by decide)) (htr ⟨71, by decide⟩ (by decide)), fun h => absurd h (by decide)⟩
  · exact ⟨fun h => absurd h (by decide), fun _ => ThreeCopyQutritWerner.X2.InK2x234.specA N hN (htr ⟨72, by decide⟩ (by decide))⟩
  · exact ⟨fun h => absurd h (by decide), fun _ => ThreeCopyQutritWerner.X2.InK2x235.specA N hN (htr ⟨73, by decide⟩ (by decide))⟩
  · exact ⟨fun h => absurd h (by decide), fun _ => ThreeCopyQutritWerner.X2.InK2x236.specA N hN (htr ⟨74, by decide⟩ (by decide))⟩
  · exact ⟨fun _ => InZA2.z237 N, fun h => absurd h (by decide)⟩
  · exact ⟨fun h => absurd h (by decide), fun _ => ThreeCopyQutritWerner.X2.InK2x244.specA N hN (htr ⟨75, by decide⟩ (by decide)) (htr ⟨76, by decide⟩ (by decide))⟩
  · exact ⟨fun h => absurd h (by decide), fun _ => ThreeCopyQutritWerner.X2.InK2x245.specA N hN (htr ⟨77, by decide⟩ (by decide))⟩
  · exact ⟨fun h => absurd h (by decide), fun _ => ThreeCopyQutritWerner.X2.InK2x246.specA N hN (htr ⟨78, by decide⟩ (by decide))⟩
  · exact ⟨fun _ => InZA2.z247 N, fun h => absurd h (by decide)⟩
  · exact ⟨fun h => absurd h (by decide), fun _ => ThreeCopyQutritWerner.X2.InK2x255.specA N hN (htr ⟨79, by decide⟩ (by decide)) (htr ⟨80, by decide⟩ (by decide))⟩
  · exact ⟨fun h => absurd h (by decide), fun _ => ThreeCopyQutritWerner.X2.InK2x256.specA N hN (htr ⟨81, by decide⟩ (by decide))⟩
  · exact ⟨fun _ => InZA2.z257 N, fun h => absurd h (by decide)⟩
  · exact ⟨fun h => absurd h (by decide), fun _ => ThreeCopyQutritWerner.X2.InK2x266.specA N hN (htr ⟨82, by decide⟩ (by decide)) (htr ⟨83, by decide⟩ (by decide))⟩
  · exact ⟨fun _ => InZA2.z267 N, fun h => absurd h (by decide)⟩
  · exact ⟨fun _ => InZA2.z277 N, fun h => absurd h (by decide)⟩
  · exact ⟨fun _ => InZA2.z333 N hN (htr ⟨84, by decide⟩ (by decide)) (htr ⟨85, by decide⟩ (by decide)), fun h => absurd h (by decide)⟩
  · exact ⟨fun h => absurd h (by decide), fun _ => ThreeCopyQutritWerner.X2.InK2x334.specA N hN (htr ⟨86, by decide⟩ (by decide)) (htr ⟨87, by decide⟩ (by decide))⟩
  · exact ⟨fun h => absurd h (by decide), fun _ => ThreeCopyQutritWerner.X2.InK2x335.specA N hN (htr ⟨88, by decide⟩ (by decide)) (htr ⟨89, by decide⟩ (by decide))⟩
  · exact ⟨fun h => absurd h (by decide), fun _ => ThreeCopyQutritWerner.X2.InK2x336.specA N hN (htr ⟨90, by decide⟩ (by decide)) (htr ⟨91, by decide⟩ (by decide))⟩
  · exact ⟨fun _ => InZA2.z337 N, fun h => absurd h (by decide)⟩
  · exact ⟨fun h => absurd h (by decide), fun _ => ThreeCopyQutritWerner.X2.InK2x344.specA N hN (htr ⟨92, by decide⟩ (by decide)) (htr ⟨93, by decide⟩ (by decide))⟩
  · exact ⟨fun h => absurd h (by decide), fun _ => ThreeCopyQutritWerner.X2.InK2x345.specA N hN (htr ⟨94, by decide⟩ (by decide))⟩
  · exact ⟨fun h => absurd h (by decide), fun _ => ThreeCopyQutritWerner.X2.InK2x346.specA N hN (htr ⟨95, by decide⟩ (by decide))⟩
  · exact ⟨fun _ => InZA2.z347 N, fun h => absurd h (by decide)⟩
  · exact ⟨fun h => absurd h (by decide), fun _ => ThreeCopyQutritWerner.X2.InK2x355.specA N hN (htr ⟨96, by decide⟩ (by decide)) (htr ⟨97, by decide⟩ (by decide))⟩
  · exact ⟨fun h => absurd h (by decide), fun _ => ThreeCopyQutritWerner.X2.InK2x356.specA N hN (htr ⟨98, by decide⟩ (by decide))⟩
  · exact ⟨fun _ => InZA2.z357 N, fun h => absurd h (by decide)⟩
  · exact ⟨fun h => absurd h (by decide), fun _ => ThreeCopyQutritWerner.X2.InK2x366.specA N hN (htr ⟨99, by decide⟩ (by decide)) (htr ⟨100, by decide⟩ (by decide))⟩
  · exact ⟨fun _ => InZA2.z367 N, fun h => absurd h (by decide)⟩
  · exact ⟨fun _ => InZA2.z377 N, fun h => absurd h (by decide)⟩
  · exact ⟨fun h => absurd h (by decide), fun _ => ThreeCopyQutritWerner.X2.InK2x444.specA N hN (htr ⟨101, by decide⟩ (by decide)) (htr ⟨102, by decide⟩ (by decide)) (htr ⟨103, by decide⟩ (by decide))⟩
  · exact ⟨fun h => absurd h (by decide), fun _ => ThreeCopyQutritWerner.X2.InK2x445.specA N hN (htr ⟨104, by decide⟩ (by decide)) (htr ⟨105, by decide⟩ (by decide))⟩
  · exact ⟨fun h => absurd h (by decide), fun _ => ThreeCopyQutritWerner.X2.InK2x446.specA N hN (htr ⟨106, by decide⟩ (by decide)) (htr ⟨107, by decide⟩ (by decide))⟩
  · exact ⟨fun _ => InZA2.z447 N, fun h => absurd h (by decide)⟩
  · exact ⟨fun h => absurd h (by decide), fun _ => ThreeCopyQutritWerner.X2.InK2x455.specA N hN (htr ⟨108, by decide⟩ (by decide)) (htr ⟨109, by decide⟩ (by decide))⟩
  · exact ⟨fun h => absurd h (by decide), fun _ => ThreeCopyQutritWerner.X2.InK2x456.specA N hN (htr ⟨110, by decide⟩ (by decide))⟩
  · exact ⟨fun _ => InZA2.z457 N, fun h => absurd h (by decide)⟩
  · exact ⟨fun h => absurd h (by decide), fun _ => ThreeCopyQutritWerner.X2.InK2x466.specA N hN (htr ⟨111, by decide⟩ (by decide)) (htr ⟨112, by decide⟩ (by decide))⟩
  · exact ⟨fun _ => InZA2.z467 N, fun h => absurd h (by decide)⟩
  · exact ⟨fun _ => InZA2.z477 N, fun h => absurd h (by decide)⟩
  · exact ⟨fun h => absurd h (by decide), fun _ => ThreeCopyQutritWerner.X2.InK2x555.specA N hN (htr ⟨113, by decide⟩ (by decide)) (htr ⟨114, by decide⟩ (by decide)) (htr ⟨115, by decide⟩ (by decide))⟩
  · exact ⟨fun h => absurd h (by decide), fun _ => ThreeCopyQutritWerner.X2.InK2x556.specA N hN (htr ⟨116, by decide⟩ (by decide)) (htr ⟨117, by decide⟩ (by decide))⟩
  · exact ⟨fun _ => InZA2.z557 N, fun h => absurd h (by decide)⟩
  · exact ⟨fun h => absurd h (by decide), fun _ => ThreeCopyQutritWerner.X2.InK2x566.specA N hN (htr ⟨118, by decide⟩ (by decide)) (htr ⟨119, by decide⟩ (by decide))⟩
  · exact ⟨fun _ => InZA2.z567 N, fun h => absurd h (by decide)⟩
  · exact ⟨fun _ => InZA2.z577 N, fun h => absurd h (by decide)⟩
  · exact ⟨fun h => absurd h (by decide), fun _ => ThreeCopyQutritWerner.X2.InK2x666.specA N hN (htr ⟨120, by decide⟩ (by decide)) (htr ⟨121, by decide⟩ (by decide)) (htr ⟨122, by decide⟩ (by decide))⟩
  · exact ⟨fun _ => InZA2.z667 N, fun h => absurd h (by decide)⟩
  · exact ⟨fun _ => InZA2.z677 N, fun h => absurd h (by decide)⟩
  · exact ⟨fun _ => InZA2.z777 N, fun h => absurd h (by decide)⟩

end ThreeCopyQutritWerner.X2.InDA2
