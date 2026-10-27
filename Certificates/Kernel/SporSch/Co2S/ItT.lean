module

public import Certificates.Kernel.SporSch.HN.GenNTree
public import Certificates.Kernel.SporSch.Co2S.ItChain
public import Certificates.Data.Kernel.Spor.Prim
public import Certificates.Data.Kernel.SporSch.FixK
public import CFSG.Sporadic.Co2Schreier.Arrays
meta import CFSG.Sporadic.Co2Schreier.Arrays
meta import Certificates.Kernel.Sporadic.RawGen
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSporSch.Co2tGen

open CFSG.KS.RawGen CFSG.Sporadic.Co2Schreier

meta def dP : List Nat := dArrs.toList.map (pack 12)

meta def dIP : List Nat := dArrs.toList.map fun a => pack 12 (inv 2300 a)

meta def tP : List Nat := [pack 12 tArr]

end CertificateChecks.KernelSporSch.Co2tGen

#kss_ntree CertificateChecks.KernelSporSch.Co2tD CertificateChecks.KernelSporSch.Co2tGen.dP
#kss_ntree CertificateChecks.KernelSporSch.Co2tDI CertificateChecks.KernelSporSch.Co2tGen.dIP
#kss_ntree CertificateChecks.KernelSporSch.Co2tT CertificateChecks.KernelSporSch.Co2tGen.tP

namespace CertificateChecks.KernelSporSch.Co2t

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KS.SporSch CFSG.KS.SporSch.Co2SFix
open CFSG.Sporadic.Co2Schreier CertificateChecks.KernelSporSch

theorem len : localRec.dWords.length = 2 := by decide

theorem wd0 : wordEqK 2300 12 (mask 12) (pidn 2300 12) Co2ItC.S Co2ItC.SI 2
    (localRec.dWords.getD 0 []) (Co2tD 0) = true := by quickRfl

theorem wd1 : wordEqK 2300 12 (mask 12) (pidn 2300 12) Co2ItC.S Co2ItC.SI 2
    (localRec.dWords.getD 1 []) (Co2tD 1) = true := by quickRfl

theorem pd : allN 2 (fun j => permOK 2300 12 (mask 12) (2300 * 12) (Co2tD j) (Co2tDI j)) = true := by
  quickRfl

theorem wt : wordEqK 2300 12 (mask 12) (pidn 2300 12) Co2tD Co2tDI 2 localRec.dCenterWord
    (Co2tT 0) = true := by quickRfl

theorem fx : fixK 2300 12 (Co2tT 0) co2ItNat = true := by quickRfl

end CertificateChecks.KernelSporSch.Co2t

end
