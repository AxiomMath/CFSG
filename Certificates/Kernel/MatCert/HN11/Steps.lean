module

public import Certificates.Data.Kernel.LocalQT.Sec
public import CFSG.Certificates.Kernel.LocalQT.Steps
import Certificates.Kernel.LocalQT.Cmd
import all CFSG.Blueprint.NativeSporadic
public meta import Certificates.Kernel.LocalComp.FactsVMeta
public meta import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.FongSporBigData7
public import Certificates.Kernel.LocalComp.FactsVMeta

public meta section

namespace CertificateChecks.KernelMC.HN11

open CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.FongSporLocal

def ext : CFSG.SectionRank.Native.Data :=
  CFSG.KC.LocalComp.FactsVMeta.extData hn_11_claims.nregs hn_11_claims.prog hn_11_claims.facts

end CertificateChecks.KernelMC.HN11

end

set_option maxRecDepth 100000

#lqt_sr_elem CFSG.KD.MC.HN11 CertificateChecks.KernelMC.HN11.ext 5 133
  CFSG.Blueprint.NativeSporadic.HNSeed1 CFSG.Blueprint.NativeSporadic.HNSeed2
