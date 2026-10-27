module

public import Certificates.Data.Item434SporGenMathieu
public import Certificates.Kernel.Sporadic.RawGen
public import Certificates.Kernel.Misc.Perm.HexCmd
public meta import Certificates.Data.Item434SporGenMathieu
import CFSG.Certificates.Kernel.Common.Harness

public section

namespace CertificateChecks.KernelItem434

meta def m22BaseM : Array Nat := #[0, 2, 3, 1, 4]

meta def m22EM : Array (Array Nat) :=
  #[CFSG.RankThree.PartTwo.Sec4.Item434SporGen.m22GenA,
    CFSG.RankThree.PartTwo.Sec4.Item434SporGen.m22GenB,
    CFSG.RankThree.PartTwo.Sec4.Item434SporGen.m22E1, CFSG.RankThree.PartTwo.Sec4.Item434SporGen.m22E2]

end CertificateChecks.KernelItem434

end

set_option maxRecDepth 400000

#ks_rawchain CertificateChecks.KernelItem434.M22C 22 5 22
  CFSG.RankThree.PartTwo.Sec4.Item434SporGen.m22GenS CertificateChecks.KernelItem434.m22BaseM 4
  CFSG.RankThree.PartTwo.Sec4.Item434SporGen.m22Words

#kmisc_packarrs CertificateChecks.KernelItem434.M22E CertificateChecks.KernelItem434.m22EM 5
