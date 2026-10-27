module

public import Certificates.Kernel.Sporadic.OddCore.PEnumCmd
public import Certificates.Kernel.Sporadic.OddCore.PEnumGlue
public import Certificates.Kernel.LocalComp.L34Para.Data
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34FactsSylowCertInputs
meta import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34FactsSylowCertInputs
public import CFSG.Certificates.CosetTableShort
public import CFSG.GroupTheory.LocalCores.Fitting
public import CFSG.Open.Defs
meta import CFSG.Certificates.CosetTableShort
meta import CFSG.GroupTheory.LocalCores.Fitting
meta import CFSG.LocalAnalysis.ComponentClassification.PSL3FourInvolutions
meta import CFSG.Open.Defs

namespace CertificateChecks.KernelLC.L34Syl3

open CFSG.ComponentClassification.GrSLit.L34Facts

meta def u1M : Array (Array Nat) := wordTabs wU₁

meta def u2M : Array (Array Nat) := wordTabs wU₂

meta def id42 : Array Nat := CFSG.PSL3Four.Native.idTab 42

end CertificateChecks.KernelLC.L34Syl3

public section

set_option maxRecDepth 400000

#kpenum CertificateChecks.KernelLC.L34SyU1 42 6 false CertificateChecks.KernelLC.L34Syl3.u1M
  CertificateChecks.KernelLC.L34Syl3.u1M CertificateChecks.KernelLC.L34Syl3.id42 16
#kpenum CertificateChecks.KernelLC.L34SyU2 42 6 false CertificateChecks.KernelLC.L34Syl3.u2M
  CertificateChecks.KernelLC.L34Syl3.u2M CertificateChecks.KernelLC.L34Syl3.id42 16

end
