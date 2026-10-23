module

public import ThreeCopyQutritWerner.CertificateX2InputTS2x005
public import ThreeCopyQutritWerner.CertificateX2InputTS2x006
public import ThreeCopyQutritWerner.CertificateX2InputTS2x014
public import ThreeCopyQutritWerner.CertificateX2InputTS2x015
public import ThreeCopyQutritWerner.CertificateX2InputTS2x016
public import ThreeCopyQutritWerner.CertificateX2InputTS2x024
public import ThreeCopyQutritWerner.CertificateX2InputTS2x025
public import ThreeCopyQutritWerner.CertificateX2InputTS2x026
public import ThreeCopyQutritWerner.CertificateX2InputTS2x034
public import ThreeCopyQutritWerner.CertificateX2InputTS2x035
public import ThreeCopyQutritWerner.CertificateX2InputTS2x036
public import ThreeCopyQutritWerner.CertificateX2InputTS2x044
public import ThreeCopyQutritWerner.CertificateX2InputTS2x045
public import ThreeCopyQutritWerner.CertificateX2InputTS2x046
public import ThreeCopyQutritWerner.CertificateX2InputTS2x055
public import ThreeCopyQutritWerner.CertificateX2InputTS2x056
public import ThreeCopyQutritWerner.CertificateX2InputTS2x066
public import ThreeCopyQutritWerner.CertificateX2InputTS2x114
public import ThreeCopyQutritWerner.CertificateX2InputTS2x115
public import ThreeCopyQutritWerner.CertificateX2InputTS2x116
public import ThreeCopyQutritWerner.CertificateX2InputTS2x124
public import ThreeCopyQutritWerner.CertificateX2InputTS2x125
public import ThreeCopyQutritWerner.CertificateX2InputTS2x126
public import ThreeCopyQutritWerner.CertificateX2InputTS2x134
public import ThreeCopyQutritWerner.CertificateX2InputTS2x135
public import ThreeCopyQutritWerner.CertificateX2InputTS2x136
public import ThreeCopyQutritWerner.CertificateX2InputTS2x144
public import ThreeCopyQutritWerner.CertificateX2InputTS2x145
public import ThreeCopyQutritWerner.CertificateX2InputTS2x146
public import ThreeCopyQutritWerner.CertificateX2InputTS2x155
public import ThreeCopyQutritWerner.CertificateX2InputTS2x156
public import ThreeCopyQutritWerner.CertificateX2InputTS2x166
public import ThreeCopyQutritWerner.CertificateX2InputTS2x222
public import ThreeCopyQutritWerner.CertificateX2InputTS2x224
public import ThreeCopyQutritWerner.CertificateX2InputTS2x225
public import ThreeCopyQutritWerner.CertificateX2InputTS2x226
public import ThreeCopyQutritWerner.CertificateX2InputTS2x234
public import ThreeCopyQutritWerner.CertificateX2InputTS2x235
public import ThreeCopyQutritWerner.CertificateX2InputTS2x236
public import ThreeCopyQutritWerner.CertificateX2InputTS2x244
public import ThreeCopyQutritWerner.CertificateX2InputTS2x245
public import ThreeCopyQutritWerner.CertificateX2InputTS2x246
public import ThreeCopyQutritWerner.CertificateX2InputTS2x255
public import ThreeCopyQutritWerner.CertificateX2InputTS2x256
public import ThreeCopyQutritWerner.CertificateX2InputTS2x266
public import ThreeCopyQutritWerner.CertificateX2InputTS2x334
public import ThreeCopyQutritWerner.CertificateX2InputTS2x335
public import ThreeCopyQutritWerner.CertificateX2InputTS2x336
public import ThreeCopyQutritWerner.CertificateX2InputTS2x344
public import ThreeCopyQutritWerner.CertificateX2InputTS2x345
public import ThreeCopyQutritWerner.CertificateX2InputTS2x346
public import ThreeCopyQutritWerner.CertificateX2InputTS2x355
public import ThreeCopyQutritWerner.CertificateX2InputTS2x356
public import ThreeCopyQutritWerner.CertificateX2InputTS2x366
public import ThreeCopyQutritWerner.CertificateX2InputTS2x444
public import ThreeCopyQutritWerner.CertificateX2InputTS2x445
public import ThreeCopyQutritWerner.CertificateX2InputTS2x446
public import ThreeCopyQutritWerner.CertificateX2InputTS2x455
public import ThreeCopyQutritWerner.CertificateX2InputTS2x456
public import ThreeCopyQutritWerner.CertificateX2InputTS2x466
public import ThreeCopyQutritWerner.CertificateX2InputTS2x555
public import ThreeCopyQutritWerner.CertificateX2InputTS2x556
public import ThreeCopyQutritWerner.CertificateX2InputTS2x566
public import ThreeCopyQutritWerner.CertificateX2InputTS2x666
public import ThreeCopyQutritWerner.CertificateX2InputZS2

@[expose] public section


/-! The T-table directory of the S pipeline of sector 2, the source forms SrcForm2 and the directory specification DirSpecS. -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option exponentiation.threshold 1000000

open scoped Matrix

namespace ThreeCopyQutritWerner.X2.InDS2
open ThreeCopyQutritWerner ThreeCopyQutritWerner.X2

noncomputable def TTd : Fin 8 → Fin 8 → Fin 8 → List (List ℕ) := fun a b c =>
    if a.val = 0 ∧ b.val = 0 ∧ c.val = 5 then ThreeCopyQutritWerner.X2.InK2x005.TT else
    if a.val = 0 ∧ b.val = 0 ∧ c.val = 6 then ThreeCopyQutritWerner.X2.InK2x006.TT else
    if a.val = 0 ∧ b.val = 1 ∧ c.val = 4 then ThreeCopyQutritWerner.X2.InK2x014.TT else
    if a.val = 0 ∧ b.val = 1 ∧ c.val = 5 then ThreeCopyQutritWerner.X2.InK2x015.TT else
    if a.val = 0 ∧ b.val = 1 ∧ c.val = 6 then ThreeCopyQutritWerner.X2.InK2x016.TT else
    if a.val = 0 ∧ b.val = 2 ∧ c.val = 4 then ThreeCopyQutritWerner.X2.InK2x024.TT else
    if a.val = 0 ∧ b.val = 2 ∧ c.val = 5 then ThreeCopyQutritWerner.X2.InK2x025.TT else
    if a.val = 0 ∧ b.val = 2 ∧ c.val = 6 then ThreeCopyQutritWerner.X2.InK2x026.TT else
    if a.val = 0 ∧ b.val = 3 ∧ c.val = 4 then ThreeCopyQutritWerner.X2.InK2x034.TT else
    if a.val = 0 ∧ b.val = 3 ∧ c.val = 5 then ThreeCopyQutritWerner.X2.InK2x035.TT else
    if a.val = 0 ∧ b.val = 3 ∧ c.val = 6 then ThreeCopyQutritWerner.X2.InK2x036.TT else
    if a.val = 0 ∧ b.val = 4 ∧ c.val = 4 then ThreeCopyQutritWerner.X2.InK2x044.TT else
    if a.val = 0 ∧ b.val = 4 ∧ c.val = 5 then ThreeCopyQutritWerner.X2.InK2x045.TT else
    if a.val = 0 ∧ b.val = 4 ∧ c.val = 6 then ThreeCopyQutritWerner.X2.InK2x046.TT else
    if a.val = 0 ∧ b.val = 5 ∧ c.val = 5 then ThreeCopyQutritWerner.X2.InK2x055.TT else
    if a.val = 0 ∧ b.val = 5 ∧ c.val = 6 then ThreeCopyQutritWerner.X2.InK2x056.TT else
    if a.val = 0 ∧ b.val = 6 ∧ c.val = 6 then ThreeCopyQutritWerner.X2.InK2x066.TT else
    if a.val = 1 ∧ b.val = 1 ∧ c.val = 4 then ThreeCopyQutritWerner.X2.InK2x114.TT else
    if a.val = 1 ∧ b.val = 1 ∧ c.val = 5 then ThreeCopyQutritWerner.X2.InK2x115.TT else
    if a.val = 1 ∧ b.val = 1 ∧ c.val = 6 then ThreeCopyQutritWerner.X2.InK2x116.TT else
    if a.val = 1 ∧ b.val = 2 ∧ c.val = 4 then ThreeCopyQutritWerner.X2.InK2x124.TT else
    if a.val = 1 ∧ b.val = 2 ∧ c.val = 5 then ThreeCopyQutritWerner.X2.InK2x125.TT else
    if a.val = 1 ∧ b.val = 2 ∧ c.val = 6 then ThreeCopyQutritWerner.X2.InK2x126.TT else
    if a.val = 1 ∧ b.val = 3 ∧ c.val = 4 then ThreeCopyQutritWerner.X2.InK2x134.TT else
    if a.val = 1 ∧ b.val = 3 ∧ c.val = 5 then ThreeCopyQutritWerner.X2.InK2x135.TT else
    if a.val = 1 ∧ b.val = 3 ∧ c.val = 6 then ThreeCopyQutritWerner.X2.InK2x136.TT else
    if a.val = 1 ∧ b.val = 4 ∧ c.val = 4 then ThreeCopyQutritWerner.X2.InK2x144.TT else
    if a.val = 1 ∧ b.val = 4 ∧ c.val = 5 then ThreeCopyQutritWerner.X2.InK2x145.TT else
    if a.val = 1 ∧ b.val = 4 ∧ c.val = 6 then ThreeCopyQutritWerner.X2.InK2x146.TT else
    if a.val = 1 ∧ b.val = 5 ∧ c.val = 5 then ThreeCopyQutritWerner.X2.InK2x155.TT else
    if a.val = 1 ∧ b.val = 5 ∧ c.val = 6 then ThreeCopyQutritWerner.X2.InK2x156.TT else
    if a.val = 1 ∧ b.val = 6 ∧ c.val = 6 then ThreeCopyQutritWerner.X2.InK2x166.TT else
    if a.val = 2 ∧ b.val = 2 ∧ c.val = 2 then ThreeCopyQutritWerner.X2.InK2x222.TT else
    if a.val = 2 ∧ b.val = 2 ∧ c.val = 4 then ThreeCopyQutritWerner.X2.InK2x224.TT else
    if a.val = 2 ∧ b.val = 2 ∧ c.val = 5 then ThreeCopyQutritWerner.X2.InK2x225.TT else
    if a.val = 2 ∧ b.val = 2 ∧ c.val = 6 then ThreeCopyQutritWerner.X2.InK2x226.TT else
    if a.val = 2 ∧ b.val = 3 ∧ c.val = 4 then ThreeCopyQutritWerner.X2.InK2x234.TT else
    if a.val = 2 ∧ b.val = 3 ∧ c.val = 5 then ThreeCopyQutritWerner.X2.InK2x235.TT else
    if a.val = 2 ∧ b.val = 3 ∧ c.val = 6 then ThreeCopyQutritWerner.X2.InK2x236.TT else
    if a.val = 2 ∧ b.val = 4 ∧ c.val = 4 then ThreeCopyQutritWerner.X2.InK2x244.TT else
    if a.val = 2 ∧ b.val = 4 ∧ c.val = 5 then ThreeCopyQutritWerner.X2.InK2x245.TT else
    if a.val = 2 ∧ b.val = 4 ∧ c.val = 6 then ThreeCopyQutritWerner.X2.InK2x246.TT else
    if a.val = 2 ∧ b.val = 5 ∧ c.val = 5 then ThreeCopyQutritWerner.X2.InK2x255.TT else
    if a.val = 2 ∧ b.val = 5 ∧ c.val = 6 then ThreeCopyQutritWerner.X2.InK2x256.TT else
    if a.val = 2 ∧ b.val = 6 ∧ c.val = 6 then ThreeCopyQutritWerner.X2.InK2x266.TT else
    if a.val = 3 ∧ b.val = 3 ∧ c.val = 4 then ThreeCopyQutritWerner.X2.InK2x334.TT else
    if a.val = 3 ∧ b.val = 3 ∧ c.val = 5 then ThreeCopyQutritWerner.X2.InK2x335.TT else
    if a.val = 3 ∧ b.val = 3 ∧ c.val = 6 then ThreeCopyQutritWerner.X2.InK2x336.TT else
    if a.val = 3 ∧ b.val = 4 ∧ c.val = 4 then ThreeCopyQutritWerner.X2.InK2x344.TT else
    if a.val = 3 ∧ b.val = 4 ∧ c.val = 5 then ThreeCopyQutritWerner.X2.InK2x345.TT else
    if a.val = 3 ∧ b.val = 4 ∧ c.val = 6 then ThreeCopyQutritWerner.X2.InK2x346.TT else
    if a.val = 3 ∧ b.val = 5 ∧ c.val = 5 then ThreeCopyQutritWerner.X2.InK2x355.TT else
    if a.val = 3 ∧ b.val = 5 ∧ c.val = 6 then ThreeCopyQutritWerner.X2.InK2x356.TT else
    if a.val = 3 ∧ b.val = 6 ∧ c.val = 6 then ThreeCopyQutritWerner.X2.InK2x366.TT else
    if a.val = 4 ∧ b.val = 4 ∧ c.val = 4 then ThreeCopyQutritWerner.X2.InK2x444.TT else
    if a.val = 4 ∧ b.val = 4 ∧ c.val = 5 then ThreeCopyQutritWerner.X2.InK2x445.TT else
    if a.val = 4 ∧ b.val = 4 ∧ c.val = 6 then ThreeCopyQutritWerner.X2.InK2x446.TT else
    if a.val = 4 ∧ b.val = 5 ∧ c.val = 5 then ThreeCopyQutritWerner.X2.InK2x455.TT else
    if a.val = 4 ∧ b.val = 5 ∧ c.val = 6 then ThreeCopyQutritWerner.X2.InK2x456.TT else
    if a.val = 4 ∧ b.val = 6 ∧ c.val = 6 then ThreeCopyQutritWerner.X2.InK2x466.TT else
    if a.val = 5 ∧ b.val = 5 ∧ c.val = 5 then ThreeCopyQutritWerner.X2.InK2x555.TT else
    if a.val = 5 ∧ b.val = 5 ∧ c.val = 6 then ThreeCopyQutritWerner.X2.InK2x556.TT else
    if a.val = 5 ∧ b.val = 6 ∧ c.val = 6 then ThreeCopyQutritWerner.X2.InK2x566.TT else
    if a.val = 6 ∧ b.val = 6 ∧ c.val = 6 then ThreeCopyQutritWerner.X2.InK2x666.TT else
    []
noncomputable def TCd : Fin 8 → Fin 8 → Fin 8 → List (List ℕ) := fun a b c =>
    if a.val = 0 ∧ b.val = 0 ∧ c.val = 5 then ThreeCopyQutritWerner.X2.InK2x005.TT else
    if a.val = 0 ∧ b.val = 0 ∧ c.val = 6 then ThreeCopyQutritWerner.X2.InK2x006.TT else
    if a.val = 0 ∧ b.val = 1 ∧ c.val = 4 then ThreeCopyQutritWerner.X2.InK2x014.TC else
    if a.val = 0 ∧ b.val = 1 ∧ c.val = 5 then ThreeCopyQutritWerner.X2.InK2x015.TC else
    if a.val = 0 ∧ b.val = 1 ∧ c.val = 6 then ThreeCopyQutritWerner.X2.InK2x016.TC else
    if a.val = 0 ∧ b.val = 2 ∧ c.val = 4 then ThreeCopyQutritWerner.X2.InK2x024.TC else
    if a.val = 0 ∧ b.val = 2 ∧ c.val = 5 then ThreeCopyQutritWerner.X2.InK2x025.TC else
    if a.val = 0 ∧ b.val = 2 ∧ c.val = 6 then ThreeCopyQutritWerner.X2.InK2x026.TC else
    if a.val = 0 ∧ b.val = 3 ∧ c.val = 4 then ThreeCopyQutritWerner.X2.InK2x034.TC else
    if a.val = 0 ∧ b.val = 3 ∧ c.val = 5 then ThreeCopyQutritWerner.X2.InK2x035.TC else
    if a.val = 0 ∧ b.val = 3 ∧ c.val = 6 then ThreeCopyQutritWerner.X2.InK2x036.TC else
    if a.val = 0 ∧ b.val = 4 ∧ c.val = 4 then ThreeCopyQutritWerner.X2.InK2x044.TC else
    if a.val = 0 ∧ b.val = 4 ∧ c.val = 5 then ThreeCopyQutritWerner.X2.InK2x045.TC else
    if a.val = 0 ∧ b.val = 4 ∧ c.val = 6 then ThreeCopyQutritWerner.X2.InK2x046.TC else
    if a.val = 0 ∧ b.val = 5 ∧ c.val = 5 then ThreeCopyQutritWerner.X2.InK2x055.TC else
    if a.val = 0 ∧ b.val = 5 ∧ c.val = 6 then ThreeCopyQutritWerner.X2.InK2x056.TC else
    if a.val = 0 ∧ b.val = 6 ∧ c.val = 6 then ThreeCopyQutritWerner.X2.InK2x066.TC else
    if a.val = 1 ∧ b.val = 1 ∧ c.val = 4 then ThreeCopyQutritWerner.X2.InK2x114.TT else
    if a.val = 1 ∧ b.val = 1 ∧ c.val = 5 then ThreeCopyQutritWerner.X2.InK2x115.TT else
    if a.val = 1 ∧ b.val = 1 ∧ c.val = 6 then ThreeCopyQutritWerner.X2.InK2x116.TT else
    if a.val = 1 ∧ b.val = 2 ∧ c.val = 4 then ThreeCopyQutritWerner.X2.InK2x124.TC else
    if a.val = 1 ∧ b.val = 2 ∧ c.val = 5 then ThreeCopyQutritWerner.X2.InK2x125.TC else
    if a.val = 1 ∧ b.val = 2 ∧ c.val = 6 then ThreeCopyQutritWerner.X2.InK2x126.TC else
    if a.val = 1 ∧ b.val = 3 ∧ c.val = 4 then ThreeCopyQutritWerner.X2.InK2x134.TC else
    if a.val = 1 ∧ b.val = 3 ∧ c.val = 5 then ThreeCopyQutritWerner.X2.InK2x135.TC else
    if a.val = 1 ∧ b.val = 3 ∧ c.val = 6 then ThreeCopyQutritWerner.X2.InK2x136.TC else
    if a.val = 1 ∧ b.val = 4 ∧ c.val = 4 then ThreeCopyQutritWerner.X2.InK2x144.TC else
    if a.val = 1 ∧ b.val = 4 ∧ c.val = 5 then ThreeCopyQutritWerner.X2.InK2x145.TC else
    if a.val = 1 ∧ b.val = 4 ∧ c.val = 6 then ThreeCopyQutritWerner.X2.InK2x146.TC else
    if a.val = 1 ∧ b.val = 5 ∧ c.val = 5 then ThreeCopyQutritWerner.X2.InK2x155.TC else
    if a.val = 1 ∧ b.val = 5 ∧ c.val = 6 then ThreeCopyQutritWerner.X2.InK2x156.TC else
    if a.val = 1 ∧ b.val = 6 ∧ c.val = 6 then ThreeCopyQutritWerner.X2.InK2x166.TC else
    if a.val = 2 ∧ b.val = 2 ∧ c.val = 2 then ThreeCopyQutritWerner.X2.InK2x222.TT else
    if a.val = 2 ∧ b.val = 2 ∧ c.val = 4 then ThreeCopyQutritWerner.X2.InK2x224.TT else
    if a.val = 2 ∧ b.val = 2 ∧ c.val = 5 then ThreeCopyQutritWerner.X2.InK2x225.TT else
    if a.val = 2 ∧ b.val = 2 ∧ c.val = 6 then ThreeCopyQutritWerner.X2.InK2x226.TT else
    if a.val = 2 ∧ b.val = 3 ∧ c.val = 4 then ThreeCopyQutritWerner.X2.InK2x234.TC else
    if a.val = 2 ∧ b.val = 3 ∧ c.val = 5 then ThreeCopyQutritWerner.X2.InK2x235.TC else
    if a.val = 2 ∧ b.val = 3 ∧ c.val = 6 then ThreeCopyQutritWerner.X2.InK2x236.TC else
    if a.val = 2 ∧ b.val = 4 ∧ c.val = 4 then ThreeCopyQutritWerner.X2.InK2x244.TC else
    if a.val = 2 ∧ b.val = 4 ∧ c.val = 5 then ThreeCopyQutritWerner.X2.InK2x245.TC else
    if a.val = 2 ∧ b.val = 4 ∧ c.val = 6 then ThreeCopyQutritWerner.X2.InK2x246.TC else
    if a.val = 2 ∧ b.val = 5 ∧ c.val = 5 then ThreeCopyQutritWerner.X2.InK2x255.TC else
    if a.val = 2 ∧ b.val = 5 ∧ c.val = 6 then ThreeCopyQutritWerner.X2.InK2x256.TC else
    if a.val = 2 ∧ b.val = 6 ∧ c.val = 6 then ThreeCopyQutritWerner.X2.InK2x266.TC else
    if a.val = 3 ∧ b.val = 3 ∧ c.val = 4 then ThreeCopyQutritWerner.X2.InK2x334.TT else
    if a.val = 3 ∧ b.val = 3 ∧ c.val = 5 then ThreeCopyQutritWerner.X2.InK2x335.TT else
    if a.val = 3 ∧ b.val = 3 ∧ c.val = 6 then ThreeCopyQutritWerner.X2.InK2x336.TT else
    if a.val = 3 ∧ b.val = 4 ∧ c.val = 4 then ThreeCopyQutritWerner.X2.InK2x344.TC else
    if a.val = 3 ∧ b.val = 4 ∧ c.val = 5 then ThreeCopyQutritWerner.X2.InK2x345.TC else
    if a.val = 3 ∧ b.val = 4 ∧ c.val = 6 then ThreeCopyQutritWerner.X2.InK2x346.TC else
    if a.val = 3 ∧ b.val = 5 ∧ c.val = 5 then ThreeCopyQutritWerner.X2.InK2x355.TC else
    if a.val = 3 ∧ b.val = 5 ∧ c.val = 6 then ThreeCopyQutritWerner.X2.InK2x356.TC else
    if a.val = 3 ∧ b.val = 6 ∧ c.val = 6 then ThreeCopyQutritWerner.X2.InK2x366.TC else
    if a.val = 4 ∧ b.val = 4 ∧ c.val = 4 then ThreeCopyQutritWerner.X2.InK2x444.TT else
    if a.val = 4 ∧ b.val = 4 ∧ c.val = 5 then ThreeCopyQutritWerner.X2.InK2x445.TT else
    if a.val = 4 ∧ b.val = 4 ∧ c.val = 6 then ThreeCopyQutritWerner.X2.InK2x446.TT else
    if a.val = 4 ∧ b.val = 5 ∧ c.val = 5 then ThreeCopyQutritWerner.X2.InK2x455.TC else
    if a.val = 4 ∧ b.val = 5 ∧ c.val = 6 then ThreeCopyQutritWerner.X2.InK2x456.TC else
    if a.val = 4 ∧ b.val = 6 ∧ c.val = 6 then ThreeCopyQutritWerner.X2.InK2x466.TC else
    if a.val = 5 ∧ b.val = 5 ∧ c.val = 5 then ThreeCopyQutritWerner.X2.InK2x555.TT else
    if a.val = 5 ∧ b.val = 5 ∧ c.val = 6 then ThreeCopyQutritWerner.X2.InK2x556.TT else
    if a.val = 5 ∧ b.val = 6 ∧ c.val = 6 then ThreeCopyQutritWerner.X2.InK2x566.TC else
    if a.val = 6 ∧ b.val = 6 ∧ c.val = 6 then ThreeCopyQutritWerner.X2.InK2x666.TT else
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

/-- Source forms of sector 2: the trial block on every uncorrected key, the light corrected form on the corrected keys. -/
def corrKeys : List (x2Key 2) := [⟨54, by decide⟩]
def SrcForm (N : X2Blocks 2) : Prop := (∀ k : x2Key 2, k ∉ corrKeys → N k = x2TrialForm 2 k) ∧ N ⟨54, by decide⟩ = x2CorrForm 2 ⟨54, by decide⟩ 55 ThreeCopyQutritWerner.X2.InK2x146.K2x146k0c ThreeCopyQutritWerner.X2.InK2x146.A2x146k0c

theorem dirSpec (N : X2Blocks 2) (hN : ∀ k, (N k)ᵀ = N k) (hsrc : SrcForm N) : DirSpecS 2 N TTd TCd Zd := by
  intro t0 t1 t2 h01 h12
  obtain ⟨htr, hc54⟩ := hsrc
  fin_cases t0 <;> fin_cases t1 <;> fin_cases t2 <;>
    first | exact absurd h01 (by decide) | exact absurd h12 (by decide) | skip
  · exact ⟨fun _ => InZS2.z000 N hN , fun h => absurd h (by decide)⟩
  · exact ⟨fun _ => InZS2.z001 N hN , fun h => absurd h (by decide)⟩
  · exact ⟨fun _ => InZS2.z002 N hN , fun h => absurd h (by decide)⟩
  · exact ⟨fun _ => InZS2.z003 N hN (htr ⟨0, by decide⟩ (by decide)), fun h => absurd h (by decide)⟩
  · exact ⟨fun _ => InZS2.z004 N hN (htr ⟨1, by decide⟩ (by decide)), fun h => absurd h (by decide)⟩
  · exact ⟨fun h => absurd h (by decide), fun _ => ThreeCopyQutritWerner.X2.InK2x005.spec N hN (htr ⟨2, by decide⟩ (by decide))⟩
  · exact ⟨fun h => absurd h (by decide), fun _ => ThreeCopyQutritWerner.X2.InK2x006.spec N hN (htr ⟨3, by decide⟩ (by decide))⟩
  · exact ⟨fun _ => InZS2.z007 N, fun h => absurd h (by decide)⟩
  · exact ⟨fun _ => InZS2.z011 N hN (htr ⟨4, by decide⟩ (by decide)), fun h => absurd h (by decide)⟩
  · exact ⟨fun _ => InZS2.z012 N hN (htr ⟨5, by decide⟩ (by decide)), fun h => absurd h (by decide)⟩
  · exact ⟨fun _ => InZS2.z013 N hN (htr ⟨6, by decide⟩ (by decide)), fun h => absurd h (by decide)⟩
  · exact ⟨fun h => absurd h (by decide), fun _ => ThreeCopyQutritWerner.X2.InK2x014.spec N hN (htr ⟨7, by decide⟩ (by decide))⟩
  · exact ⟨fun h => absurd h (by decide), fun _ => ThreeCopyQutritWerner.X2.InK2x015.spec N hN (htr ⟨8, by decide⟩ (by decide))⟩
  · exact ⟨fun h => absurd h (by decide), fun _ => ThreeCopyQutritWerner.X2.InK2x016.spec N hN (htr ⟨9, by decide⟩ (by decide))⟩
  · exact ⟨fun _ => InZS2.z017 N, fun h => absurd h (by decide)⟩
  · exact ⟨fun _ => InZS2.z022 N hN (htr ⟨10, by decide⟩ (by decide)), fun h => absurd h (by decide)⟩
  · exact ⟨fun _ => InZS2.z023 N hN (htr ⟨11, by decide⟩ (by decide)), fun h => absurd h (by decide)⟩
  · exact ⟨fun h => absurd h (by decide), fun _ => ThreeCopyQutritWerner.X2.InK2x024.spec N hN (htr ⟨12, by decide⟩ (by decide))⟩
  · exact ⟨fun h => absurd h (by decide), fun _ => ThreeCopyQutritWerner.X2.InK2x025.spec N hN (htr ⟨13, by decide⟩ (by decide))⟩
  · exact ⟨fun h => absurd h (by decide), fun _ => ThreeCopyQutritWerner.X2.InK2x026.spec N hN (htr ⟨14, by decide⟩ (by decide))⟩
  · exact ⟨fun _ => InZS2.z027 N, fun h => absurd h (by decide)⟩
  · exact ⟨fun _ => InZS2.z033 N hN (htr ⟨15, by decide⟩ (by decide)), fun h => absurd h (by decide)⟩
  · exact ⟨fun h => absurd h (by decide), fun _ => ThreeCopyQutritWerner.X2.InK2x034.spec N hN (htr ⟨16, by decide⟩ (by decide))⟩
  · exact ⟨fun h => absurd h (by decide), fun _ => ThreeCopyQutritWerner.X2.InK2x035.spec N hN (htr ⟨17, by decide⟩ (by decide))⟩
  · exact ⟨fun h => absurd h (by decide), fun _ => ThreeCopyQutritWerner.X2.InK2x036.spec N hN (htr ⟨18, by decide⟩ (by decide))⟩
  · exact ⟨fun _ => InZS2.z037 N, fun h => absurd h (by decide)⟩
  · exact ⟨fun h => absurd h (by decide), fun _ => ThreeCopyQutritWerner.X2.InK2x044.spec N hN (htr ⟨19, by decide⟩ (by decide)) (htr ⟨20, by decide⟩ (by decide))⟩
  · exact ⟨fun h => absurd h (by decide), fun _ => ThreeCopyQutritWerner.X2.InK2x045.spec N hN (htr ⟨21, by decide⟩ (by decide))⟩
  · exact ⟨fun h => absurd h (by decide), fun _ => ThreeCopyQutritWerner.X2.InK2x046.spec N hN (htr ⟨22, by decide⟩ (by decide))⟩
  · exact ⟨fun _ => InZS2.z047 N, fun h => absurd h (by decide)⟩
  · exact ⟨fun h => absurd h (by decide), fun _ => ThreeCopyQutritWerner.X2.InK2x055.spec N hN (htr ⟨23, by decide⟩ (by decide)) (htr ⟨24, by decide⟩ (by decide))⟩
  · exact ⟨fun h => absurd h (by decide), fun _ => ThreeCopyQutritWerner.X2.InK2x056.spec N hN (htr ⟨25, by decide⟩ (by decide))⟩
  · exact ⟨fun _ => InZS2.z057 N, fun h => absurd h (by decide)⟩
  · exact ⟨fun h => absurd h (by decide), fun _ => ThreeCopyQutritWerner.X2.InK2x066.spec N hN (htr ⟨26, by decide⟩ (by decide)) (htr ⟨27, by decide⟩ (by decide))⟩
  · exact ⟨fun _ => InZS2.z067 N, fun h => absurd h (by decide)⟩
  · exact ⟨fun _ => InZS2.z077 N, fun h => absurd h (by decide)⟩
  · exact ⟨fun _ => InZS2.z111 N hN (htr ⟨28, by decide⟩ (by decide)) (htr ⟨29, by decide⟩ (by decide)), fun h => absurd h (by decide)⟩
  · exact ⟨fun _ => InZS2.z112 N hN (htr ⟨30, by decide⟩ (by decide)) (htr ⟨31, by decide⟩ (by decide)), fun h => absurd h (by decide)⟩
  · exact ⟨fun _ => InZS2.z113 N hN (htr ⟨32, by decide⟩ (by decide)) (htr ⟨33, by decide⟩ (by decide)), fun h => absurd h (by decide)⟩
  · exact ⟨fun h => absurd h (by decide), fun _ => ThreeCopyQutritWerner.X2.InK2x114.spec N hN (htr ⟨34, by decide⟩ (by decide)) (htr ⟨35, by decide⟩ (by decide))⟩
  · exact ⟨fun h => absurd h (by decide), fun _ => ThreeCopyQutritWerner.X2.InK2x115.spec N hN (htr ⟨36, by decide⟩ (by decide)) (htr ⟨37, by decide⟩ (by decide))⟩
  · exact ⟨fun h => absurd h (by decide), fun _ => ThreeCopyQutritWerner.X2.InK2x116.spec N hN (htr ⟨38, by decide⟩ (by decide)) (htr ⟨39, by decide⟩ (by decide))⟩
  · exact ⟨fun _ => InZS2.z117 N, fun h => absurd h (by decide)⟩
  · exact ⟨fun _ => InZS2.z122 N hN (htr ⟨40, by decide⟩ (by decide)) (htr ⟨41, by decide⟩ (by decide)), fun h => absurd h (by decide)⟩
  · exact ⟨fun _ => InZS2.z123 N hN (htr ⟨42, by decide⟩ (by decide)), fun h => absurd h (by decide)⟩
  · exact ⟨fun h => absurd h (by decide), fun _ => ThreeCopyQutritWerner.X2.InK2x124.spec N hN (htr ⟨43, by decide⟩ (by decide))⟩
  · exact ⟨fun h => absurd h (by decide), fun _ => ThreeCopyQutritWerner.X2.InK2x125.spec N hN (htr ⟨44, by decide⟩ (by decide))⟩
  · exact ⟨fun h => absurd h (by decide), fun _ => ThreeCopyQutritWerner.X2.InK2x126.spec N hN (htr ⟨45, by decide⟩ (by decide))⟩
  · exact ⟨fun _ => InZS2.z127 N, fun h => absurd h (by decide)⟩
  · exact ⟨fun _ => InZS2.z133 N hN (htr ⟨46, by decide⟩ (by decide)) (htr ⟨47, by decide⟩ (by decide)), fun h => absurd h (by decide)⟩
  · exact ⟨fun h => absurd h (by decide), fun _ => ThreeCopyQutritWerner.X2.InK2x134.spec N hN (htr ⟨48, by decide⟩ (by decide))⟩
  · exact ⟨fun h => absurd h (by decide), fun _ => ThreeCopyQutritWerner.X2.InK2x135.spec N hN (htr ⟨49, by decide⟩ (by decide))⟩
  · exact ⟨fun h => absurd h (by decide), fun _ => ThreeCopyQutritWerner.X2.InK2x136.spec N hN (htr ⟨50, by decide⟩ (by decide))⟩
  · exact ⟨fun _ => InZS2.z137 N, fun h => absurd h (by decide)⟩
  · exact ⟨fun h => absurd h (by decide), fun _ => ThreeCopyQutritWerner.X2.InK2x144.spec N hN (htr ⟨51, by decide⟩ (by decide)) (htr ⟨52, by decide⟩ (by decide))⟩
  · exact ⟨fun h => absurd h (by decide), fun _ => ThreeCopyQutritWerner.X2.InK2x145.spec N hN (htr ⟨53, by decide⟩ (by decide))⟩
  · exact ⟨fun h => absurd h (by decide), fun _ => ThreeCopyQutritWerner.X2.InK2x146.spec N hN hc54⟩
  · exact ⟨fun _ => InZS2.z147 N, fun h => absurd h (by decide)⟩
  · exact ⟨fun h => absurd h (by decide), fun _ => ThreeCopyQutritWerner.X2.InK2x155.spec N hN (htr ⟨55, by decide⟩ (by decide)) (htr ⟨56, by decide⟩ (by decide))⟩
  · exact ⟨fun h => absurd h (by decide), fun _ => ThreeCopyQutritWerner.X2.InK2x156.spec N hN (htr ⟨57, by decide⟩ (by decide))⟩
  · exact ⟨fun _ => InZS2.z157 N, fun h => absurd h (by decide)⟩
  · exact ⟨fun h => absurd h (by decide), fun _ => ThreeCopyQutritWerner.X2.InK2x166.spec N hN (htr ⟨58, by decide⟩ (by decide)) (htr ⟨59, by decide⟩ (by decide))⟩
  · exact ⟨fun _ => InZS2.z167 N, fun h => absurd h (by decide)⟩
  · exact ⟨fun _ => InZS2.z177 N, fun h => absurd h (by decide)⟩
  · exact ⟨fun h => absurd h (by decide), fun _ => ThreeCopyQutritWerner.X2.InK2x222.spec N hN (htr ⟨60, by decide⟩ (by decide)) (htr ⟨61, by decide⟩ (by decide))⟩
  · exact ⟨fun _ => InZS2.z223 N hN (htr ⟨62, by decide⟩ (by decide)) (htr ⟨63, by decide⟩ (by decide)), fun h => absurd h (by decide)⟩
  · exact ⟨fun h => absurd h (by decide), fun _ => ThreeCopyQutritWerner.X2.InK2x224.spec N hN (htr ⟨64, by decide⟩ (by decide)) (htr ⟨65, by decide⟩ (by decide))⟩
  · exact ⟨fun h => absurd h (by decide), fun _ => ThreeCopyQutritWerner.X2.InK2x225.spec N hN (htr ⟨66, by decide⟩ (by decide)) (htr ⟨67, by decide⟩ (by decide))⟩
  · exact ⟨fun h => absurd h (by decide), fun _ => ThreeCopyQutritWerner.X2.InK2x226.spec N hN (htr ⟨68, by decide⟩ (by decide)) (htr ⟨69, by decide⟩ (by decide))⟩
  · exact ⟨fun _ => InZS2.z227 N, fun h => absurd h (by decide)⟩
  · exact ⟨fun _ => InZS2.z233 N hN (htr ⟨70, by decide⟩ (by decide)) (htr ⟨71, by decide⟩ (by decide)), fun h => absurd h (by decide)⟩
  · exact ⟨fun h => absurd h (by decide), fun _ => ThreeCopyQutritWerner.X2.InK2x234.spec N hN (htr ⟨72, by decide⟩ (by decide))⟩
  · exact ⟨fun h => absurd h (by decide), fun _ => ThreeCopyQutritWerner.X2.InK2x235.spec N hN (htr ⟨73, by decide⟩ (by decide))⟩
  · exact ⟨fun h => absurd h (by decide), fun _ => ThreeCopyQutritWerner.X2.InK2x236.spec N hN (htr ⟨74, by decide⟩ (by decide))⟩
  · exact ⟨fun _ => InZS2.z237 N, fun h => absurd h (by decide)⟩
  · exact ⟨fun h => absurd h (by decide), fun _ => ThreeCopyQutritWerner.X2.InK2x244.spec N hN (htr ⟨75, by decide⟩ (by decide)) (htr ⟨76, by decide⟩ (by decide))⟩
  · exact ⟨fun h => absurd h (by decide), fun _ => ThreeCopyQutritWerner.X2.InK2x245.spec N hN (htr ⟨77, by decide⟩ (by decide))⟩
  · exact ⟨fun h => absurd h (by decide), fun _ => ThreeCopyQutritWerner.X2.InK2x246.spec N hN (htr ⟨78, by decide⟩ (by decide))⟩
  · exact ⟨fun _ => InZS2.z247 N, fun h => absurd h (by decide)⟩
  · exact ⟨fun h => absurd h (by decide), fun _ => ThreeCopyQutritWerner.X2.InK2x255.spec N hN (htr ⟨79, by decide⟩ (by decide)) (htr ⟨80, by decide⟩ (by decide))⟩
  · exact ⟨fun h => absurd h (by decide), fun _ => ThreeCopyQutritWerner.X2.InK2x256.spec N hN (htr ⟨81, by decide⟩ (by decide))⟩
  · exact ⟨fun _ => InZS2.z257 N, fun h => absurd h (by decide)⟩
  · exact ⟨fun h => absurd h (by decide), fun _ => ThreeCopyQutritWerner.X2.InK2x266.spec N hN (htr ⟨82, by decide⟩ (by decide)) (htr ⟨83, by decide⟩ (by decide))⟩
  · exact ⟨fun _ => InZS2.z267 N, fun h => absurd h (by decide)⟩
  · exact ⟨fun _ => InZS2.z277 N, fun h => absurd h (by decide)⟩
  · exact ⟨fun _ => InZS2.z333 N hN (htr ⟨84, by decide⟩ (by decide)) (htr ⟨85, by decide⟩ (by decide)), fun h => absurd h (by decide)⟩
  · exact ⟨fun h => absurd h (by decide), fun _ => ThreeCopyQutritWerner.X2.InK2x334.spec N hN (htr ⟨86, by decide⟩ (by decide)) (htr ⟨87, by decide⟩ (by decide))⟩
  · exact ⟨fun h => absurd h (by decide), fun _ => ThreeCopyQutritWerner.X2.InK2x335.spec N hN (htr ⟨88, by decide⟩ (by decide)) (htr ⟨89, by decide⟩ (by decide))⟩
  · exact ⟨fun h => absurd h (by decide), fun _ => ThreeCopyQutritWerner.X2.InK2x336.spec N hN (htr ⟨90, by decide⟩ (by decide)) (htr ⟨91, by decide⟩ (by decide))⟩
  · exact ⟨fun _ => InZS2.z337 N, fun h => absurd h (by decide)⟩
  · exact ⟨fun h => absurd h (by decide), fun _ => ThreeCopyQutritWerner.X2.InK2x344.spec N hN (htr ⟨92, by decide⟩ (by decide)) (htr ⟨93, by decide⟩ (by decide))⟩
  · exact ⟨fun h => absurd h (by decide), fun _ => ThreeCopyQutritWerner.X2.InK2x345.spec N hN (htr ⟨94, by decide⟩ (by decide))⟩
  · exact ⟨fun h => absurd h (by decide), fun _ => ThreeCopyQutritWerner.X2.InK2x346.spec N hN (htr ⟨95, by decide⟩ (by decide))⟩
  · exact ⟨fun _ => InZS2.z347 N, fun h => absurd h (by decide)⟩
  · exact ⟨fun h => absurd h (by decide), fun _ => ThreeCopyQutritWerner.X2.InK2x355.spec N hN (htr ⟨96, by decide⟩ (by decide)) (htr ⟨97, by decide⟩ (by decide))⟩
  · exact ⟨fun h => absurd h (by decide), fun _ => ThreeCopyQutritWerner.X2.InK2x356.spec N hN (htr ⟨98, by decide⟩ (by decide))⟩
  · exact ⟨fun _ => InZS2.z357 N, fun h => absurd h (by decide)⟩
  · exact ⟨fun h => absurd h (by decide), fun _ => ThreeCopyQutritWerner.X2.InK2x366.spec N hN (htr ⟨99, by decide⟩ (by decide)) (htr ⟨100, by decide⟩ (by decide))⟩
  · exact ⟨fun _ => InZS2.z367 N, fun h => absurd h (by decide)⟩
  · exact ⟨fun _ => InZS2.z377 N, fun h => absurd h (by decide)⟩
  · exact ⟨fun h => absurd h (by decide), fun _ => ThreeCopyQutritWerner.X2.InK2x444.spec N hN (htr ⟨101, by decide⟩ (by decide)) (htr ⟨102, by decide⟩ (by decide)) (htr ⟨103, by decide⟩ (by decide))⟩
  · exact ⟨fun h => absurd h (by decide), fun _ => ThreeCopyQutritWerner.X2.InK2x445.spec N hN (htr ⟨104, by decide⟩ (by decide)) (htr ⟨105, by decide⟩ (by decide))⟩
  · exact ⟨fun h => absurd h (by decide), fun _ => ThreeCopyQutritWerner.X2.InK2x446.spec N hN (htr ⟨106, by decide⟩ (by decide)) (htr ⟨107, by decide⟩ (by decide))⟩
  · exact ⟨fun _ => InZS2.z447 N, fun h => absurd h (by decide)⟩
  · exact ⟨fun h => absurd h (by decide), fun _ => ThreeCopyQutritWerner.X2.InK2x455.spec N hN (htr ⟨108, by decide⟩ (by decide)) (htr ⟨109, by decide⟩ (by decide))⟩
  · exact ⟨fun h => absurd h (by decide), fun _ => ThreeCopyQutritWerner.X2.InK2x456.spec N hN (htr ⟨110, by decide⟩ (by decide))⟩
  · exact ⟨fun _ => InZS2.z457 N, fun h => absurd h (by decide)⟩
  · exact ⟨fun h => absurd h (by decide), fun _ => ThreeCopyQutritWerner.X2.InK2x466.spec N hN (htr ⟨111, by decide⟩ (by decide)) (htr ⟨112, by decide⟩ (by decide))⟩
  · exact ⟨fun _ => InZS2.z467 N, fun h => absurd h (by decide)⟩
  · exact ⟨fun _ => InZS2.z477 N, fun h => absurd h (by decide)⟩
  · exact ⟨fun h => absurd h (by decide), fun _ => ThreeCopyQutritWerner.X2.InK2x555.spec N hN (htr ⟨113, by decide⟩ (by decide)) (htr ⟨114, by decide⟩ (by decide)) (htr ⟨115, by decide⟩ (by decide))⟩
  · exact ⟨fun h => absurd h (by decide), fun _ => ThreeCopyQutritWerner.X2.InK2x556.spec N hN (htr ⟨116, by decide⟩ (by decide)) (htr ⟨117, by decide⟩ (by decide))⟩
  · exact ⟨fun _ => InZS2.z557 N, fun h => absurd h (by decide)⟩
  · exact ⟨fun h => absurd h (by decide), fun _ => ThreeCopyQutritWerner.X2.InK2x566.spec N hN (htr ⟨118, by decide⟩ (by decide)) (htr ⟨119, by decide⟩ (by decide))⟩
  · exact ⟨fun _ => InZS2.z567 N, fun h => absurd h (by decide)⟩
  · exact ⟨fun _ => InZS2.z577 N, fun h => absurd h (by decide)⟩
  · exact ⟨fun h => absurd h (by decide), fun _ => ThreeCopyQutritWerner.X2.InK2x666.spec N hN (htr ⟨120, by decide⟩ (by decide)) (htr ⟨121, by decide⟩ (by decide)) (htr ⟨122, by decide⟩ (by decide))⟩
  · exact ⟨fun _ => InZS2.z667 N, fun h => absurd h (by decide)⟩
  · exact ⟨fun _ => InZS2.z677 N, fun h => absurd h (by decide)⟩
  · exact ⟨fun _ => InZS2.z777 N, fun h => absurd h (by decide)⟩

end ThreeCopyQutritWerner.X2.InDS2
