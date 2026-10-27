module

public import Certificates.Kernel.Sporadic.RawGen
public import CFSG.RankThree.Native.HSMcLSmallCheckInputs
public import Certificates.Data.Kernel.Misc.HexFlat
import Certificates.Kernel.Misc.Perm.HexCmd
import CFSG.Certificates.Kernel.Common.Harness
meta import CFSG.RankThree.Native.HSMcLSmallCheckInputs

set_option maxRecDepth 400000

@[expose] public section

namespace CertificateChecks.KernelMisc.HS100

@[expose] def d1 : List (List Int) := CFSG.RankThree.Native.hs100Words.toList.drop 2

end CertificateChecks.KernelMisc.HS100

end

#ks_chars CertificateChecks.KernelMisc.HS100.HX CFSG.RankThree.Native.hs100Hex
#kmisc_hexflat CertificateChecks.KernelMisc.HS100.HX CFSG.RankThree.Native.hs100Hex 3 100 7 16

#ks_rawchain CertificateChecks.KernelMisc.HS100.C 100 7 100 CFSG.RankThree.Native.hs100StrongArrs
  CFSG.RankThree.Native.hs100BaseArr 2 CertificateChecks.KernelMisc.HS100.d1

public section

namespace CertificateChecks.KernelMisc.HS100

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw

theorem cperm : allN 15 (fun j => permOK 100 7 (mask 7) (100 * 7) (C.S j) (C.SI j)) = true := by
  quickRfl

theorem cFS : allN 15 (fun j => Nat.beq (HX.F j) (C.S j)) = true := by quickRfl

end CertificateChecks.KernelMisc.HS100

end
