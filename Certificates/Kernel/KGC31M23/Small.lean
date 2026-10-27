module

public import Certificates.Kernel.KGC31M23.CosDefs
public import Certificates.Kernel.KGC31M23.ChainData
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelKGC31M23

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KC.KGC31P CFSG.KS.SporSch.MOC
open CFSG.Quasithin.KGC31.M23 CertificateChecks.KernelSporSch

theorem kOrd : (pord 23 5 5 X5 && pord 23 5 7 X7 && pord 23 5 11 X11 && pord 23 5 23 X23) = true := by
  quickRfl

theorem kGens : ((List.range 2).all (fun j => Nat.beq (CW.S j) (pw (wGenW.getD j []))) &&
    (List.range 2).all (fun j => Nat.beq (CT.S j) (pw (tGenW.getD j []))) &&
    (List.range 2).all (fun j => Nat.beq (CE.S j) (pw (eGenW.getD j [])))) = true := by quickRfl

theorem kOrdC : (Nat.beq (ordK CW.LR 5) 40320 && Nat.beq (ordK CT.LR 3) 960 &&
    Nat.beq (ordK CE.LR 3) 1344) = true := by quickRfl

theorem kTRW : (trPL 23 5 CW.LR CW.TR 5).all (fun L => L.all fun t =>
    permOK 23 5 (mask 5) (23 * 5) t (pinv 23 5 t)) = true := by quickRfl

theorem kMasks : (((wGenW.map pw).zip wMasks).all (fun p => pmasksOK 23 5 wP p.1 p.2) &&
    ((tGenW.map pw).zip tMasks).all (fun p => pmasksOK 23 5 tP p.1 p.2) &&
    ((eGenW.map pw).zip eMasks).all (fun p => pmasksOK 23 5 eP p.1 p.2)) = true := by quickRfl

theorem kFixG : (tGenW.map pw).all (pfix triT) = true := by quickRfl

theorem kFixSet : (pfixSet wP hexH && pfixSet tP triT) = true := by quickRfl

theorem kHex : Nat.beq (pcountProducts 23 5 (pfix hexH) (trPL 23 5 CW.LR CW.TR 5) (pidn 23 5)) 16 =
    true := by quickRfl

theorem kSIn : (sP.zip sInW).all (fun p => Nat.beq p.1 (pmask 23 5 wP p.2)) = true := by quickRfl

theorem kCos : (pcosetOK 23 5 B0 wP (wCosetW.map pw) && pcosetOK 23 5 B0 tP (tCosetW.map pw) &&
    pcosetOK 23 5 B0 eP (eCosetW.map pw)) = true := by quickRfl

end CertificateChecks.KernelKGC31M23

end
