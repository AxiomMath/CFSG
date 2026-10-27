module

public import Certificates.Kernel.Misc.CharsFn
public import Certificates.Data.CFSGNative.J1Sylow.Certificate

public section

set_option maxRecDepth 1000000

#ks_chars_fn CertificateChecks.KernelJ1Syl.TW CFSG.Sporadic.J1.Sylow.Native.tWordsStr
#ks_chars_fn CertificateChecks.KernelJ1Syl.NW CFSG.Sporadic.J1.Sylow.Native.nWordsStr

end
