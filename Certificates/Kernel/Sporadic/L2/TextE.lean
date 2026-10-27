module

public import Certificates.Kernel.Sporadic.RawGen
public import Certificates.Kernel.Misc.Perm.HexCmd
public import Certificates.Data.SuzLevelTwoPins
meta import Certificates.Data.SuzLevelTwoPins
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

#ks_chars CertificateChecks.KernelSpor.L2EM CFSG.Sporadic.SuzRecog.LevelTwoPins.emapHex
#kmisc_hexflat CertificateChecks.KernelSpor.L2EM CFSG.Sporadic.SuzRecog.LevelTwoPins.emapHex
  5 36 20 2835

end
