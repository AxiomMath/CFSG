module

public import Certificates.Kernel.HSStd.PumpU3Data
public import Certificates.Kernel.LocalComp.L39Chains
public import Certificates.Data.Kernel.BfsPinBase
public import Certificates.Data.Kernel.LocalComp.ExcDeriv
import CFSG.Certificates.Kernel.Common.Harness

set_option maxRecDepth 400000

public section

namespace CertificateChecks.KernelHSStd.PumpU3

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KC.BfsPin CertificateChecks.KernelLC.L39
open CFSG.EvenSporadicStandard.HSStd.PumpTC7
open CFSG.KC.LocalComp.ExcDeriv (fixCntK)

@[expose] noncomputable def uSK : List Nat := (List.range 729).map UK

@[expose] noncomputable def g7P : Nat := wordK 182 8 (mask 8) (pidn 182 8) LT.S LT.SI [1, 2, 1, 1]

@[expose] noncomputable def g7Pow : Nat :=
  pcomp 182 8 (mask 8) g7P (pcomp 182 8 (mask 8) g7P (pcomp 182 8 (mask 8) g7P
    (pcomp 182 8 (mask 8) g7P (pcomp 182 8 (mask 8) g7P (pcomp 182 8 (mask 8) g7P g7P)))))

theorem sz : szOK 182 8 = true := by quickRfl

theorem permLT : allN 7 (fun j => permOK 182 8 (mask 8) (182 * 8) (LT.S j) (LT.SI j)) = true := by
  quickRfl

theorem gU : allN 6 (fun j => wordEqK 182 8 (mask 8) (pidn 182 8) LT.S LT.SI 7 (uWords.getD j [])
    (U.G j)) = true := by quickRfl

theorem gPerm : allN 6 (fun k => permOK 182 8 (mask 8) (182 * 8) (U.G k)
    (pinvS 182 8 (mask 8) (U.G k))) = true := by quickRfl

theorem nums : (Nat.beq U.ng 6 && Nat.beq U.N 729) = true := by quickRfl

theorem kU : keysSK 182 8 tKeys U.N U.T uSK = true := by quickRfl

theorem fixU : allN U.N (fun i => Nat.beq (U.T i) (pidn 182 8) ||
    Nat.beq (fixCntK 8 (mask 8) (U.T i) 182) 2 || Nat.beq (fixCntK 8 (mask 8) (U.T i) 182) 20) =
    true := by quickRfl

theorem g7w : wordEqK 182 8 (mask 8) (pidn 182 8) LT.S LT.SI 7 [1, 2, 1, 1] g7P = true := by
  quickRfl

theorem g7ok : (permOK 182 8 (mask 8) (182 * 8) g7P (pinvS 182 8 (mask 8) g7P) &&
    Nat.beq g7Pow (pidn 182 8) && Nat.beq (fixCntK 8 (mask 8) g7P 182) 0) = true := by quickRfl

end CertificateChecks.KernelHSStd.PumpU3

end
