module

public import Certificates.Kernel.Sporadic.RawGen
public import Certificates.Kernel.Misc.Perm.HexCmd
public import CFSG.Monster.B.Fischer.InducedData
meta import CFSG.Monster.B.Fischer.InducedData

public section

set_option maxRecDepth 400000

#ks_chars CertificateChecks.KernelMonB.ITr CFSG.Monster.B.Fischer.indTransGenHex
#kmisc_hexflat CertificateChecks.KernelMonB.ITr CFSG.Monster.B.Fischer.indTransGenHex 3 3510 12 10

end
