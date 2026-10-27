module

public import Certificates.Kernel.Sporadic.RawGen
public import Certificates.Kernel.Misc.Perm.HexCmd
public import CFSG.RankThree.Native.HSMcLFiveData
public import CFSG.Sporadic.Recognition.McLASFiveData
public meta import CFSG.RankThree.Native.HSMcLFiveData
public meta import CFSG.Sporadic.Recognition.McLASFiveData
public meta import CFSG.RankThree.Native.HSMcLSmallData
public import CFSG.RankThree.Native.HSMcLSmallData

public section

set_option maxRecDepth 400000

#ks_chars CertificateChecks.KernelMcLAS.FV CFSG.RankThree.Native.mcl275FiveHex
#kmisc_hexflat CertificateChecks.KernelMcLAS.FV CFSG.RankThree.Native.mcl275FiveHex 3 275 9 71
#ks_chars CertificateChecks.KernelMcLAS.FP CFSG.Sporadic.Recognition.McLAS.fivePowHex
#kmisc_hexflat CertificateChecks.KernelMcLAS.FP CFSG.Sporadic.Recognition.McLAS.fivePowHex 3 275 9 1

end
