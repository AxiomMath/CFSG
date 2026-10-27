module

public import Certificates.Data.Kernel.LocalQT.Cov
public import Certificates.Kernel.LocalQT.Cov.D4101
public import Certificates.Kernel.Sporadic.RawGen
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.M22CoverCheck
import CFSG.Certificates.Kernel.Common.Harness
public import CFSG.Certificates.NativeSchreierCard

set_option maxRecDepth 400000

#ks_chars CFSG.KD.LQT.C4101.CT CFSG.QuasithinUnique.Ch1.M22Cover.covText

public section

namespace CFSG.KD.LQT.C4101

open CFSG.KC.LQT.Cov

theorem kC : covK 22 228952723507329932679484465855724 81506110577382089737470578414133 CT.chars H
    128 [189] = true := by quickRfl

end CFSG.KD.LQT.C4101

end
