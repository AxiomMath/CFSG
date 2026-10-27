module

public import Certificates.Kernel.M3BFib.FibData
public import Certificates.Data.Kernel.M3BFib.RootClaim
public import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.MonsterThreeBChecks

public section

namespace CFSG.KC.M3BF

open CFSG.KD.M3BF
open CFSG.HardMathSupport.Timmesfeld.SporadicBalance.ThreeBNF (rootClaims)

theorem m3br_roots : rootChkF [oneK, t1, t2, t3] rootClaims = true := by decide +kernel

end CFSG.KC.M3BF

end
