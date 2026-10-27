module

public import Certificates.Kernel.Sporadic.RawGen
public import Certificates.Data.CFSGNative.McL.Data
public import CFSG.Sporadic.Recognition.McLMultiplierInputs
public import CFSG.Certificates.CosetTableCompactColumns
public import CFSG.Certificates.CosetTableShort
public import CFSG.GroupTheory.LocalCores.Fitting
public import CFSG.Open.Defs

public section

set_option maxRecDepth 400000

#ks_chars CertificateChecks.KernelMcLMult.SA CFSG.Sporadic.McL.Native.seedA
#ks_chars CertificateChecks.KernelMcLMult.SB CFSG.Sporadic.McL.Native.seedB
#ks_chars CertificateChecks.KernelMcLMult.TA CFSG.Sporadic.Recognition.McLMultiplier.mclAText
#ks_chars CertificateChecks.KernelMcLMult.TB CFSG.Sporadic.Recognition.McLMultiplier.mclBText

end
