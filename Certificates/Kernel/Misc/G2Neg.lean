module

public import Certificates.Data.Kernel.Misc.G23
public import Certificates.Kernel.Misc.G23Data
public import Certificates.Kernel.Misc.G24Data
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 100000

namespace CFSG.KD.Misc.G2Neg

open CFSG.KC.Ord CFSG.KC.Misc.G24 CFSG.KC.Misc.G23

theorem g23_blow_wrong : notB (g23K CFSG.KD.Misc.G23.cA CFSG.KD.Misc.G23.cB
    (Nat.xor CFSG.KD.Misc.G23.Ab 1) CFSG.KD.Misc.G23.Bb CFSG.KD.Misc.G23.Rc CFSG.KD.Misc.G23.Pc
    CFSG.KD.Misc.G23.six) = true := by quickRfl

theorem g23_six_wrong : notB (g23K CFSG.KD.Misc.G23.cA CFSG.KD.Misc.G23.cB CFSG.KD.Misc.G23.Ab
    CFSG.KD.Misc.G23.Bb CFSG.KD.Misc.G23.Rc CFSG.KD.Misc.G23.Pc []) = true := by quickRfl

theorem g24F4_blow_wrong : notB (g24F4K CFSG.KD.Misc.G24.GR (0 :: CFSG.KD.Misc.G24.Gb.tail)
    CFSG.KD.Misc.G24.RS CFSG.KD.Misc.G24.PS CFSG.KD.Misc.G24.XS CFSG.KD.Misc.G24.YS
    CFSG.KD.Misc.G24.XL CFSG.KD.Misc.G24.YL) = true := by quickRfl

theorem g24F3_cube_wrong : notB (g24F3K CFSG.KD.Misc.G24.LR CFSG.KD.Misc.G24.Lb
    CFSG.KD.Misc.G24.Lb CFSG.KD.Misc.G24.RS CFSG.KD.Misc.G24.PS) = true := by quickRfl

end CFSG.KD.Misc.G2Neg
