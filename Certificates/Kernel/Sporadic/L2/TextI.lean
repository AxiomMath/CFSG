module

public import Certificates.Kernel.Sporadic.RawGen
public import Certificates.Kernel.Misc.Perm.HexCmd
public import Certificates.Data.SuzLevelTwoPins
meta import Certificates.Data.SuzLevelTwoPins
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

#ks_chars CertificateChecks.KernelSpor.L2SI CFSG.Sporadic.SuzRecog.LevelTwoPins.stepIHex
#kmisc_hexflat CertificateChecks.KernelSpor.L2SI CFSG.Sporadic.SuzRecog.LevelTwoPins.stepIHex
  5 98 20 1501

end
