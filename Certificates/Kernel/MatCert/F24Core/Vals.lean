module

public import Certificates.Data.Kernel.LocalQT.Sec
public import CFSG.Certificates.Kernel.LocalQT.Steps
import Certificates.Kernel.LocalQT.CmdF
import all CFSG.Blueprint.NativeSporadic
public meta import Certificates.Kernel.LocalComp.FactsVMeta
public meta import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanD2CoreFi24SevenData
public meta import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanD2CoreDefs
public import Certificates.Kernel.LocalComp.FactsVMeta

public meta section

namespace CertificateChecks.KernelMC.F24C

open CFSG.AGLEmbedding.R3

def ext : CFSG.SectionRank.Native.Data :=
  CFSG.KC.LocalComp.FactsVMeta.extData CoreFi247.nregs CoreFi247.prog CoreFi247.spec.facts

end CertificateChecks.KernelMC.F24C

end

set_option maxRecDepth 100000

#lqt_sr_vals CFSG.KD.MC.F24C CertificateChecks.KernelMC.F24C.ext 781
  CFSG.Blueprint.NativeSporadic.Fi24primeSeed1 CFSG.Blueprint.NativeSporadic.Fi24primeSeed2
