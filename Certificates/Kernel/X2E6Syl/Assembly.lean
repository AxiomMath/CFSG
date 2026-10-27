module

public import CFSG.Certificates.Kernel.X2E6SylGlue
public import Certificates.Kernel.X2E6Syl.ChecksQ

public section

namespace CFSG.KD.X2E6Syl

open CFSG.LocalAnalysis.GLTheoremA.KD264Lie.X2E6

theorem x2e6WeylCore :
    X2E6WeylCore :=
  CFSG.KC.X2E6Syl.x2e6WeylCore_of_checks ch880001_q ch880001_fam ch880001_fix

end CFSG.KD.X2E6Syl

end
