module

public import Certificates.Kernel.KGC31M23.CosDefs
import CFSG.Certificates.Kernel.Common.Harness
public import CFSG.Quasithin.Vol2.KGFactC31CosetCheck

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelKGC31M23

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KC.KGC31P CFSG.KS.SporSch.MOC
open CFSG.Quasithin.KGC31.M23 CertificateChecks.KernelSporSch

theorem kTR : (trPL 23 5 M23C1.LR M23C1.TR 4).all (fun L => L.all fun t =>
    permOK 23 5 (mask 5) (23 * 5) t (pinv 23 5 t)) = true := by quickRfl

theorem kEb : (pebasis 23 5 wP && pebasis 23 5 tP && pebasis 23 5 eP && pebasis 23 5 sP) = true := by
  quickRfl

theorem kZ : Nat.beq (pcj 23 5 Z (pinv 23 5 Z) (pw [1])) B0 = true := by quickRfl

theorem kRW : (List.range 15).all (fun m => pnormAll 23 5 wP (rW m) (pinv 23 5 (rW m))) = true := by
  quickRfl

theorem kNT : (List.range 15).all (fun m => conjOK tP (nTP m) (rT m) && pfix triT (nTP m)) =
    true := by quickRfl

theorem kNE : (List.range 7).all (fun m => conjOK eP (nEP m) (rE m)) = true := by quickRfl

theorem kCm : (Nat.beq (CB.countP (pcommAll 23 5 wP)) 16 &&
    Nat.beq (CB.countP (pcommAll 23 5 tP)) 16 &&
    Nat.beq (CB.countP (pcommAll 23 5 eP)) 8 &&
    Nat.beq (CB.countP (pcommAll 23 5 sP)) 16) = true := by quickRfl

theorem kNW : Nat.beq (CB.countP fun c => pnormAll 23 5 wP c (pinv 23 5 c)) 2688 = true := by
  quickRfl

theorem kNU : Nat.beq (CB.countP fT) 64 = true := by quickRfl

theorem kNEc : Nat.beq (CB.countP fun c => pnormAll 23 5 eP c (pinv 23 5 c)) 192 = true := by
  quickRfl

end CertificateChecks.KernelKGC31M23

end
