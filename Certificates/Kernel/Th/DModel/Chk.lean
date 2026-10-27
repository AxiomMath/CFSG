module

public import Certificates.Kernel.Th.DModel.Defs
import CFSG.Certificates.Kernel.Common.Harness
import Certificates.Kernel.Sporadic.ON.Gen
public import Certificates.Data.Kernel.Spor.BaseEq

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelTh.DModel

open CFSG.KC.Enum CFSG.KS CFSG.KS.Prim CFSG.KS.Raw CFSG.KC.BfsPin CFSG.KC.L34K
open CFSG.KS.PEnum CFSG.KS.BaseEq CertificateChecks.KernelTh CertificateChecks.KernelTh.AutD
open CFSG.Sporadic.Th.Recog
open CFSG.KLie.CT (andB orB notB)

theorem k_orb : allN 12 (fun r => andB (Nat.beq (ok r) 6) (andB (Nat.ble (oc r) 144)
    (andB (allN 6 fun j => andB (Nat.beq (oG r j) (L j)) (Nat.beq (oGI r j) (LI j)))
    (andB (penumHdK (oX r) (oc r) 3456 (oT r) (oPL r))
      (penumSlK 51 6 (mask 6) (51 * 6) true (oG r) (oGI r) (ok r) (oc r) (oT r) (oPL r) (oPOS r)
        (oSRT r) (oSRI r) 0 144))))) = true := by
  quickRfl

theorem k_wit : allN 12 (fun r => Nat.beq (kerK (oX r) (primeWit.getD r ([], 0)).1)
    (tgtK (primeWit.getD r ([], 0)).2)) = true := by
  quickRfl

theorem k_rd : allL (rdC ++ [duSix]) (fun w => Nat.beq (wK L LI w) (pidn 51 6)) = true := by
  quickRfl

theorem k_tc : allN 6 (fun j => Nat.beq (pc (pc (L j) (L 5)) (LI j))
    (Bool.rec (motive := fun _ => Nat) (L 5) (LI 5) (Nat.beq j 4))) = true := by
  quickRfl

theorem k_sq : Nat.beq (cntN 3456 sqD) 164 = true := by
  quickRfl

theorem kNegSq : notB (Nat.beq (cntN 3456 sqD) 163) = true := by
  quickRfl

theorem kNegWit : notB (Nat.beq (kerK (oX 0) (primeWit.getD 0 ([], 0)).1) (tgtK 1)) = true := by
  quickRfl

theorem kNegTc : notB (Nat.beq (pc (pc (L 0) (L 5)) (LI 0)) (LI 5)) = true := by
  quickRfl

theorem kNegCov : allN 11 (fun r => allN (oc (r + 1)) fun q =>
    notB (Nat.beq (oT (r + 1) q) (L 0))) = true := by
  quickRfl

end CertificateChecks.KernelTh.DModel

#kon_slices CertificateChecks.KernelTh.DModel.cSl 0 9
#kon_join CertificateChecks.KernelTh.DModel.cAll CertificateChecks.KernelTh.DModel.cSl 9

end
