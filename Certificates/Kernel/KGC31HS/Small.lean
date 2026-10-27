module

public import Certificates.Kernel.KGC31HS.Defs
public import Certificates.Kernel.KGC31HS.CosData
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelKGC31HS

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KC.KGC31P CFSG.KC.Child3
open CFSG.KS.SporSch.MOC CFSG.KS.M11
open CFSG.Quasithin.KGC31.HS CertificateChecks.KernelHS100

theorem kInv : (invEqK 100 7 (mask 7) (100 * 7) (HP.F 0) (pinvS 100 7 (mask 7) (HP.F 0)) &&
    invEqK 100 7 (mask 7) (100 * 7) (pinvS 100 7 (mask 7) (HP.F 0)) (HP.F 0) &&
    invEqK 100 7 (mask 7) (100 * 7) (HP.F 1) (pinvS 100 7 (mask 7) (HP.F 1)) &&
    invEqK 100 7 (mask 7) (100 * 7) (pinvS 100 7 (mask 7) (HP.F 1)) (HP.F 1) &&
    invEqK 100 7 (mask 7) (100 * 7) (FV.F 2) (pinvS 100 7 (mask 7) (FV.F 2)) &&
    invEqK 100 7 (mask 7) (100 * 7) (pinvS 100 7 (mask 7) (FV.F 2)) (FV.F 2) &&
    invEqK 100 7 (mask 7) (100 * 7) (FV.F 4) (pinvS 100 7 (mask 7) (FV.F 4)) &&
    invEqK 100 7 (mask 7) (100 * 7) (pinvS 100 7 (mask 7) (FV.F 4)) (FV.F 4) &&
    invEqK 100 7 (mask 7) (100 * 7) (FV.F 25) (pinvS 100 7 (mask 7) (FV.F 25)) &&
    invEqK 100 7 (mask 7) (100 * 7) (pinvS 100 7 (mask 7) (FV.F 25)) (FV.F 25)) = true := by
  quickRfl

theorem kN : Nat.beq RH.N 21175 = true := by quickRfl

theorem kCS : RH.CS = [5775, 15400] := by decide +kernel

theorem kOff : offOK RH.CS RH.OFF RH.N = true := by quickRfl

theorem kOff0 : RH.OFF = [0, 5775] := by decide +kernel

theorem kGP : (Nat.beq (RH.GP 0) (HP.F 0) && Nat.beq (RH.GP 1) (HP.F 1) &&
    Nat.beq (RH.GIP 0) (pinvS 100 7 (mask 7) (HP.F 0)) &&
    Nat.beq (RH.GIP 1) (pinvS 100 7 (mask 7) (HP.F 1))) = true := by quickRfl

theorem kGc : (canonK 100 7 (mask 7) (100 * 7) (RH.GP 0) && canonK 100 7 (mask 7) (100 * 7) (RH.GIP 0) &&
    canonK 100 7 (mask 7) (100 * 7) (RH.GP 1) && canonK 100 7 (mask 7) (100 * 7) (RH.GIP 1)) =
    true := by quickRfl

theorem kRep : (Nat.beq (RH.E 0) (HP.F 0) && Nat.beq (RH.E 5775) RB) = true := by quickRfl

theorem kOrd7 : pord 100 7 7 X7 = true := by quickRfl

theorem kOrd11 : pord 100 7 11 X11 = true := by quickRfl

theorem kGens : ((List.range 2).all (fun j => Nat.beq (CCA.S j) (pw (caGenW.getD j []))) &&
    (List.range 3).all (fun j => Nat.beq (CCR.S j) (pw (crGenW.getD j []))) &&
    (List.range 3).all (fun j => Nat.beq (CT0.S j) (pw (t0GenW.getD j []))) &&
    (List.range 2).all (fun j => Nat.beq (CM16.S j) (pw (m16GenW.getD j []))) &&
    (List.range 2).all (fun j => Nat.beq (CN8.S j) (pw (n8GenW.getD j []))) &&
    (List.range 3).all (fun j => Nat.beq (CQ.S j) (pw (qGenW.getD j [])))) = true := by quickRfl

theorem kOrdC : (Nat.beq (ordK CCA.LR 3) 7680 && Nat.beq (ordK CCR.LR 4) 2880 &&
    Nat.beq (ordK CT0.LR 2) 512 && Nat.beq (ordK CM16.LR 4) 5760 &&
    Nat.beq (ordK CN8.LR 3) 10752 && Nat.beq (ordK CQ.LR 1) 64) = true := by quickRfl

theorem kSI : ((List.range 2).all (fun j => permOK 100 7 (mask 7) (100 * 7) (CM16.S j) (CM16.SI j)) &&
    (List.range 2).all (fun j => permOK 100 7 (mask 7) (100 * 7) (CN8.S j) (CN8.SI j))) = true := by
  quickRfl

theorem kComm : ((caGenW.map pw).all (fun g => Nat.beq (pc 100 7 (HP.F 0) g) (pc 100 7 g (HP.F 0))) &&
    (crGenW.map pw).all (fun g => Nat.beq (pc 100 7 RB g) (pc 100 7 g RB))) = true := by quickRfl

theorem kTR : ((trPL 100 7 CCA.LR CCA.TR 3).all (fun L => L.all fun t =>
      permOK 100 7 (mask 7) (100 * 7) t (pinv 100 7 t)) &&
    (trPL 100 7 CT0.LR CT0.TR 2).all (fun L => L.all fun t =>
      permOK 100 7 (mask 7) (100 * 7) t (pinv 100 7 t))) = true := by quickRfl

theorem kEb : (pebasis 100 7 u16P && pebasis 100 7 u8P) = true := by quickRfl

theorem kCos : (pcosetOK 100 7 (HP.F 0) u16P r16P && pcosetOK 100 7 (HP.F 0) u8P r8P) = true := by
  quickRfl

theorem kMasks : (((m16GenW.map pw).zip m16Masks).all (fun p => pmasksOK 100 7 u16P p.1 p.2) &&
    ((n8GenW.map pw).zip n8Masks).all (fun p => pmasksOK 100 7 u8P p.1 p.2)) = true := by quickRfl

theorem kU16 : allN u16InM16.length (fun i => bAnd(lettersK 2 (u16InM16.getD i []),
    Nat.beq (wordK 100 7 (mask 7) (pidn 100 7) CM16.S CM16.SI (u16InM16.getD i []))
      (pw (u16W.getD i [])))) = true := by quickRfl

theorem kPerf : (List.range 2).all (fun j => bAnd(lettersK 2 ((n8PerfW.getD j []).getD 0 []),
    bAnd(lettersK 2 ((n8PerfW.getD j []).getD 1 []),
    Nat.beq (pw (n8GenW.getD j []))
      (pc 100 7 (pc 100 7 (pc 100 7
        (wordK 100 7 (mask 7) (pidn 100 7) CN8.S CN8.SI ((n8PerfW.getD j []).getD 0 []))
        (wordK 100 7 (mask 7) (pidn 100 7) CN8.S CN8.SI ((n8PerfW.getD j []).getD 1 [])))
        (pinv 100 7 (wordK 100 7 (mask 7) (pidn 100 7) CN8.S CN8.SI ((n8PerfW.getD j []).getD 0 []))))
        (pinv 100 7 (wordK 100 7 (mask 7) (pidn 100 7) CN8.S CN8.SI ((n8PerfW.getD j []).getD 1 [])))))))
    = true := by quickRfl

theorem kQ : (qP.all (pcommAll 100 7 u8P) && qP.all (fun g => pcommAll 100 7 qP g) &&
    (List.range 3).all (fun i => Nat.beq (pc 100 7 (qP.getD i (pidn 100 7)) (qP.getD i (pidn 100 7)))
      (pmask 100 7 u8P (qSq.getD i 0)))) = true := by quickRfl

theorem kSum : (Nat.beq ((List.range 15).map K16).sum 11520 &&
    Nat.beq ((List.range 7).map K8).sum 10752) = true := by quickRfl

end CertificateChecks.KernelKGC31HS

end
