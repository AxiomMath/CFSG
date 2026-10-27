module

public import Certificates.Kernel.Sporadic.RawGen
public import Certificates.Kernel.Misc.Perm.HexCmd
public import CFSG.RankThree.Native.HSMcLSmallCheckInputs
meta import CFSG.RankThree.Native.HSMcLSmallCheckInputs
meta import CFSG.RankThree.Native.HSMcLSmallData
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelHS100

@[expose] def hcWords : List (List Int) := CFSG.RankThree.Native.hs100Words.toList.drop 2

end CertificateChecks.KernelHS100

#ks_chars CertificateChecks.KernelHS100.HP CFSG.RankThree.Native.hs100Hex
#kmisc_hexflat CertificateChecks.KernelHS100.HP CFSG.RankThree.Native.hs100Hex 3 100 7 16

#ks_rawchain CertificateChecks.KernelHS100.HC 100 7 100 CFSG.RankThree.Native.hs100StrongArrs
  CFSG.RankThree.Native.hs100BaseArr 2 CertificateChecks.KernelHS100.hcWords

namespace CertificateChecks.KernelHS100

open CFSG.KC.Enum CFSG.KS

theorem HC.perm : allN 15 (fun j => permOK 100 7 (mask 7) (100 * 7) (HC.S j) (HC.SI j)) = true := by
  quickRfl

theorem HC.FS : allN 15 (fun j => Nat.beq (HP.F j) (HC.S j)) = true := by quickRfl

end CertificateChecks.KernelHS100

end
