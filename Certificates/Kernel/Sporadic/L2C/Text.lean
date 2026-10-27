module

public import Certificates.Kernel.Sporadic.RawGen
public import Certificates.Kernel.Misc.Perm.HexCmd
public import Certificates.Data.SuzLevelTwoCoverInputs
meta import Certificates.Data.SuzLevelTwoCoverInputs
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

#ks_chars CertificateChecks.KernelSpor.L2CV CFSG.Sporadic.SuzRecog.LevelTwoCoverData.voltStr
#kmisc_hexflat CertificateChecks.KernelSpor.L2CV CFSG.Sporadic.SuzRecog.LevelTwoCoverData.voltStr
  1 36 2 2835

#ks_chars CertificateChecks.KernelSpor.L2CS CFSG.Sporadic.SuzRecog.LevelTwoCoverData.liftStr
#kmisc_hexflat CertificateChecks.KernelSpor.L2CS CFSG.Sporadic.SuzRecog.LevelTwoCoverData.liftStr
  1 2997 2 2

end
