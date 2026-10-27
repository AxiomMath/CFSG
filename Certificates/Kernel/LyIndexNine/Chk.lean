module

public import Certificates.Kernel.LyIndexNine.Enum
public import Certificates.Kernel.Sporadic.OddCore.PEnumGlue
public import CFSG.Sporadic.Ly.IndexNineInputs
import CFSG.Certificates.Kernel.Common.Harness
public import CFSG.Sporadic.SmallOddCore.LocalSpec
public import CFSG.ThirdParty.QiuzhenCFSG.Theory.AutAlternating
public import Mathlib

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelLy9

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KS.PEnum CFSG.Sporadic.Ly

theorem ly_hd : bAnd(gensK lyGensA 11 4 LYE.k LYE.G, bAnd(Nat.beq LYE.cnt 128,
    penumHdK (pidn 11 4) LYE.cnt 128 LYE.T LYE.PL)) = true := by quickRfl

theorem ly_sl : penumSlK 11 4 (mask 4) (11 * 4) false LYE.G LYE.GI LYE.k LYE.cnt LYE.T LYE.PL
    LYE.POS LYE.SRT LYE.SRI 0 128 = true := by quickRfl

theorem ly_inv8 : lyUInvariantCheck 8 lyO8 () = true := by decide +kernel

theorem ly_inv2 : lyUInvariantCheck 2 lyBlockC () = true := by decide +kernel

theorem ly_inv1 : lyUInvariantCheck 1 lyD () = true := by decide +kernel

theorem ly_split : lySplitCheck () = true := by decide +kernel

end CertificateChecks.KernelLy9

end
