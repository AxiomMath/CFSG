module

public import Certificates.Kernel.Misc.Perm.HexCmd
public meta import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Rows.G24ModelMatch
public import CFSG.Assembly.Defs

public section

namespace CertificateChecks.KernelG24.Match27211

meta def srcM : Array (Array Nat) := CFSG.EvenSporadicStandard.G24Model.pgArrs

end CertificateChecks.KernelG24.Match27211

#kmisc_packarrs CertificateChecks.KernelG24.Match27211.PG CertificateChecks.KernelG24.Match27211.srcM 11

end
