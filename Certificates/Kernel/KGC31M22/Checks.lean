module

public import Certificates.Kernel.KGC31M22.Defs
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000
namespace CertificateChecks.KernelKGC31M22

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KC.KGC31P CFSG.KS.SporSch.MOC
open CFSG.Quasithin.KGC31.M22 CertificateChecks.KernelSporSch

theorem kOrd5 : pord 22 5 5 X5 = true := by quickRfl
theorem kOrd7 : pord 22 5 7 X7 = true := by quickRfl
theorem kOrd11 : pord 22 5 11 X11 = true := by quickRfl

theorem kN : Nat.beq D.c 1155 = true := by quickRfl

theorem kEb : (pebasis 22 5 hexP && pebasis 22 5 duadP && pebasis 22 5 e8P) = true := by quickRfl

theorem kGens : ((List.range 2).all (fun j => Nat.beq (CHX.S j) (pw (hexGenW.getD j []))) &&
    (List.range 2).all (fun j => Nat.beq (CDU.S j) (pw (duadGenW.getD j [])))) = true := by
  quickRfl

theorem kOrd : (Nat.beq (ordK CHX.LR 4) 5760 && Nat.beq (ordK CDU.LR 3) 960) = true := by quickRfl

theorem kDuad : duadP.all (fun b =>
    Nat.beq (pcountProducts 22 5 (Nat.beq b) (trPL 22 5 CDU.LR CDU.TR 3) (pidn 22 5)) 1) = true := by
  quickRfl

theorem kMasks : (((hexGenW.map pw).zip hexMasks).all (fun p => pmasksOK 22 5 hexP p.1 p.2) &&
    ((duadGenW.map pw).zip duadMasks).all (fun p => pmasksOK 22 5 duadP p.1 p.2)) = true := by
  quickRfl

theorem kTR : ((trPL 22 5 M22C1.LR M22C1.TR 3).all (fun L => L.all fun t =>
      permOK 22 5 (mask 5) (22 * 5) t (pinv 22 5 t)) &&
    (trPL 22 5 CDU.LR CDU.TR 3).all (fun L => L.all fun t =>
      permOK 22 5 (mask 5) (22 * 5) t (pinv 22 5 t))) = true := by quickRfl

end CertificateChecks.KernelKGC31M22

end
