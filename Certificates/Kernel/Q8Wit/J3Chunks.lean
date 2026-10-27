module

public import Certificates.Data.TwinPerpSmSp1WitJ3
public import Certificates.Data.Kernel.PGrp
public import Certificates.Kernel.Census.J3.Text
public import CFSG.Certificates.Kernel.Common.Eval
public meta import Certificates.Data.TwinPerpSmSp1WitJ3
public meta import Certificates.Kernel.Misc.WordChunks
meta import CFSG.Certificates.Kernel.Common.Eval

public section

namespace CertificateChecks.KernelQ8W.J3

meta def jcStep : CFSG.KC.Eval.Step := fun _ =>
  return CFSG.KC.WordChunks.chunkVals Certificates.TwinPerpSmSp1.j3Wit.cW

end CertificateChecks.KernelQ8W.J3

end

#kc_eval CertificateChecks.KernelQ8W.J3 JC CertificateChecks.KernelQ8W.J3.jcStep

public section

namespace CertificateChecks.KernelQ8W.J3

@[expose] noncomputable def JD (j : Nat) : Nat :=
  CFSG.KC.PGrp.posWordK 6156 13 CertificateChecks.KernelCensus.J3S.F (JC.W.getD j [])

end CertificateChecks.KernelQ8W.J3

end
