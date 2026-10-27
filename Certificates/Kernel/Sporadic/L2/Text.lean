module

public import Certificates.Kernel.Sporadic.RawGen
public import Certificates.Kernel.Misc.Perm.HexCmd
public import Certificates.Data.SuzLevelTwoPins
public import Certificates.Data.SuzLevelTwoInputs
meta import Certificates.Data.SuzLevelTwoPins
meta import Certificates.Data.SuzLevelTwoInputs
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

#ks_chars CertificateChecks.KernelSpor.L2TA CFSG.Sporadic.SuzRecog.LevelTwoPins.aTreeHex
#kmisc_hexflat CertificateChecks.KernelSpor.L2TA CFSG.Sporadic.SuzRecog.LevelTwoPins.aTreeHex
  3 2835 12 2
#ks_chars CertificateChecks.KernelSpor.L2TW CFSG.Sporadic.SuzRecog.LevelTwoPins.wTreeHex
#kmisc_hexflat CertificateChecks.KernelSpor.L2TW CFSG.Sporadic.SuzRecog.LevelTwoPins.wTreeHex
  3 162 12 2
#ks_chars CertificateChecks.KernelSpor.L2SP CFSG.Sporadic.SuzRecog.LevelTwoPins.spanHex
#kmisc_hexflat CertificateChecks.KernelSpor.L2SP CFSG.Sporadic.SuzRecog.LevelTwoPins.spanHex
  3 2997 12 2
#ks_chars CertificateChecks.KernelSpor.L2EL CFSG.Sporadic.SuzRecog.LevelTwoPins.eltHex
#kmisc_hexflat CertificateChecks.KernelSpor.L2EL CFSG.Sporadic.SuzRecog.LevelTwoPins.eltHex
  3 1782 11 21
#ks_chars CertificateChecks.KernelSpor.L2NP CFSG.Sporadic.SuzRecog.LevelTwoPins.nbPHex
#kmisc_hexflat CertificateChecks.KernelSpor.L2NP CFSG.Sporadic.SuzRecog.LevelTwoPins.nbPHex
  3 36 12 3
#ks_chars CertificateChecks.KernelSpor.L2NQ CFSG.Sporadic.SuzRecog.LevelTwoPins.nbQHex
#kmisc_hexflat CertificateChecks.KernelSpor.L2NQ CFSG.Sporadic.SuzRecog.LevelTwoPins.nbQHex
  3 315 12 4
#ks_chars CertificateChecks.KernelSpor.L2TR CFSG.Sporadic.SuzRecog.LevelTwoPins.triHex
#kmisc_hexflat CertificateChecks.KernelSpor.L2TR CFSG.Sporadic.SuzRecog.LevelTwoPins.triHex
  3 180 12 4
#ks_chars CertificateChecks.KernelSpor.L2TI CFSG.Sporadic.SuzRecog.LevelTwoPins.triIdxHex
#kmisc_hexflat CertificateChecks.KernelSpor.L2TI CFSG.Sporadic.SuzRecog.LevelTwoPins.triIdxHex
  3 324 12 1
#ks_chars CertificateChecks.KernelSpor.L2XS CFSG.Sporadic.SuzRecog.LevelTwoData.xStrongHex
#kmisc_hexflat CertificateChecks.KernelSpor.L2XS CFSG.Sporadic.SuzRecog.LevelTwoData.xStrongHex
  3 1782 11 9

end
