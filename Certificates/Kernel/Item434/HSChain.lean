module

public import Certificates.Data.Item434SporGenJ2HSMcL
public import Certificates.Kernel.Sporadic.RawGen
public import Certificates.Kernel.Misc.Perm.HexCmd
public meta import Certificates.Data.Item434SporGenJ2HSMcL
import CFSG.Certificates.Kernel.Common.Harness

public section

namespace CertificateChecks.KernelItem434

meta def hsBaseM : Array Nat := #[0, 2, 1, 3, 4]

meta def hsEM : Array (Array Nat) :=
  #[CFSG.RankThree.PartTwo.Sec4.Item434SporGen.hsE1, CFSG.RankThree.PartTwo.Sec4.Item434SporGen.hsE2]

end CertificateChecks.KernelItem434

end

set_option maxRecDepth 400000

#ks_rawchain CertificateChecks.KernelItem434.HSC 100 7 100
  CFSG.RankThree.PartTwo.Sec4.Item434SporGen.hsGenS CertificateChecks.KernelItem434.hsBaseM 3
  CFSG.RankThree.PartTwo.Sec4.Item434SporGen.hsWords

#kmisc_packarrs CertificateChecks.KernelItem434.HSE CertificateChecks.KernelItem434.hsEM 7
