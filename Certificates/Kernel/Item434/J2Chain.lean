module

public import Certificates.Data.Item434SporGenJ2HSMcL
public import Certificates.Kernel.Sporadic.RawGen
public import Certificates.Kernel.Misc.Perm.HexCmd
public meta import Certificates.Data.Item434SporGenJ2HSMcL
import CFSG.Certificates.Kernel.Common.Harness

public section

namespace CertificateChecks.KernelItem434

meta def j2BaseM : Array Nat := #[0, 3, 1, 2]

meta def j2EM : Array (Array Nat) :=
  #[CFSG.RankThree.PartTwo.Sec4.Sporadic.J2.zArr, CFSG.RankThree.PartTwo.Sec4.Sporadic.J2.xArr]

end CertificateChecks.KernelItem434

end

set_option maxRecDepth 400000

#ks_rawchain CertificateChecks.KernelItem434.J2C 315 9 64
  CFSG.RankThree.PartTwo.Sec4.Item434SporGen.j2GenS CertificateChecks.KernelItem434.j2BaseM 3
  CFSG.RankThree.PartTwo.Sec4.Item434SporGen.j2Words

#kmisc_packarrs CertificateChecks.KernelItem434.J2E CertificateChecks.KernelItem434.j2EM 9
