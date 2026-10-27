module

public import CFSG.Certificates.Kernel.M3BSyl.Syl
public import Certificates.Kernel.M3BSyl.Gens
public import Certificates.Kernel.M3BSyl.Walks
public import Certificates.Kernel.M3BSyl.Roots

public section

namespace CFSG.KC.M3BS

open CFSG.HardMathSupport.Timmesfeld.SporadicBalance.ThreeBNF


theorem m3bs_sylFact : SylFact :=
  sylFact_of_checks m3bs_let m3bs_gen m3bs_t m3bs_tw m3bs_pc m3bs_u m3bs_wv m3bs_wu m3bs_ko m3bs_for
    m3bs_r3 m3bs_r9

end CFSG.KC.M3BS

end
