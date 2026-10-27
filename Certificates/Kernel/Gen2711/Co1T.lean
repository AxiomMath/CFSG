module

public import Certificates.Kernel.TcGen.F2
public import Certificates.Data.Inputs2711eCo1
public import Certificates.Data.Kernel.GenWf
public import Certificates.Data.Kernel.OpsMcertT
import CFSG.Certificates.Kernel.Common.Harness

set_option maxRecDepth 400000

public section

namespace CertificateChecks.KernelTc

open CFSG.LocalAnalysis.GLTheoremB.MovingAround.Inputs2711e CFSG.AGLEmbedding.R3
open CFSG.KC.OpsK CFSG.KC.OpsMT

theorem gen271103T_K : seedsT (opsF2K 24) C1A.M C1B.M co1GenData.nregs co1GenData.prog
    co1GenData.facts 0 1 = true := by
  quickRfl

theorem gen271103T_D : (genWf 5 co1GenData && pcWf co1Pcs &&
    (nonzeroTriples 5).all fun v => co1Mod.indep.any fun q =>
      q.1 == v.1 && q.2.1 == v.2.1 && q.2.2.1 == v.2.2) = true := by
  decide +kernel

end CertificateChecks.KernelTc

end
