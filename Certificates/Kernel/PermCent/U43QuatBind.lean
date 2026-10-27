module

public import Certificates.Kernel.PermCent.U43QuatP

set_option maxRecDepth 400000

public section

namespace CertificateChecks.KernelPermCent.U43Quat

open CFSG.ComponentClassification.HarrisLit.P1.U43.Cover CFSG.ComponentClassification.HarrisLit.P1.U43.Quat
  CFSG.EvenSporadicStandard.M24Std.CU43 CFSG.KC.Enum CFSG.KS CFSG.KS.Prim CFSG.KC.QuatK
  CertificateChecks.KernelPermCent.U43P1

theorem bindsQ :
    ((List.range 17).all (fun j => canonK 820 10 (mask 10) (820 * 10) (QP j)) &&
      listOKK 820 10 deltaArr.toList (QP 15) && listOKK 820 10 phiArr.toList (QP 16) &&
      matOK repIn.1 repIn.2 rF && isId (pc (QP 6) (QP 14)) && Nat.beq (pc rF rF) eP &&
      Nat.beq (pc w0F w0F) eP && Nat.beq (pc w0F rF) (pc rF w0F) &&
      (l1F.drop 2).all (fun x => Nat.beq (pc x x) rF) &&
      (List.range 6).all (fun j =>
        Nat.beq (pc (pc (CgIn.T (cfgIdx.getD j 0)) (sF 2)) (gamF j)) (pc (gamF j) (QP 5)))) =
      true ∧ quatEls.length = 14 ∧ cfgIdx.length = 6 := by
  decide +kernel

end CertificateChecks.KernelPermCent.U43Quat

end
