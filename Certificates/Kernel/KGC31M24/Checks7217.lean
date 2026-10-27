module

public import Certificates.Kernel.KGC31M24.Defs7217
import CFSG.Certificates.Kernel.Common.Harness
public import Certificates.Kernel.KGC31M24.Data7217

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelKGC31M24

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KC.KGC31P CFSG.KS.SporSch.MOC
open CFSG.Quasithin.KGC31.M24 CertificateChecks.KernelSporSch CertificateChecks.KernelSporSch.M24OC

theorem kEb : (pebasis 24 5 oP && pebasis 24 5 sP && pebasis 24 5 s16P && pebasis 24 5 s32P &&
    pebasis 24 5 r2P && pebasis 24 5 u4P && pebasis 24 5 u5P && pebasis 24 5 u6P &&
    pebasis 24 5 tP && pebasis 24 5 etP) = true := by quickRfl

theorem kG3 : (sP.all (pcommAll 24 5 s16P) && sP.all (pcommAll 24 5 s32P) &&
    (cAll d4P r2P).all (pcommAll 24 5 u4P) && (cAll d6P tP).all (pcommAll 24 5 u6P) &&
    (qGenW.map pw).all (fun g => pcommAll 24 5 u5P g)) = true := by quickRfl

theorem kG5 : (((moGenW.map pw).zip moMasks).all (fun p => pmasksOK 24 5 oP p.1 p.2) &&
    ((nsGenW.map pw).zip nsMasks).all (fun p => pmasksOK 24 5 sP p.1 p.2) &&
    pmasksOK 24 5 sP y5P y5Masks && (njP.zip njMasks).all (fun p => pmasksOK 24 5 sP p.1 p.2) &&
    ((nqGenW.map pw).zip nqMasks).all (fun p => pmasksOK 24 5 u5P p.1 p.2) &&
    pmasksOK 24 5 u5P y7P y7Masks && (mjP.zip mjMasks).all (fun p => pmasksOK 24 5 u5P p.1 p.2) &&
    ((ntGenW.map pw).zip ntMasks).all (fun p => pmasksOK 24 5 tP p.1 p.2) &&
    pmasksOK 24 5 tP qtP qtMasks && (kqP.zip kqMasks).all (fun p => pmasksOK 24 5 tP p.1 p.2) &&
    pord 24 5 5 y5P && pord 24 5 7 y7P) = true := by quickRfl

theorem kCb0 : (((CFSG.Sporadic.Schreier.m24CentWords2.map
      (abWordK 24 5 (mask 5) (pidn 24 5) (M24Q.S 0) (M24Q.SI 0) (M24Q.S 1) (M24Q.SI 1))).zip
      cb0Masks).all (fun p => pmasksOK 24 5 r2P p.1 p.2) &&
    CFSG.Sporadic.Schreier.m24CentWords2.all abOK) = true := by quickRfl

theorem kG6 : (etP.all (pcommAll 24 5 u5P) && pblocksOK 5 tets y5P && njP.all (pblocksOK 5 tets) &&
    sP.all (pfixesBlocks 5 tets)) = true := by quickRfl

theorem kG7 : (!(pinSpan 24 5 tP qtP) && pinSpan 24 5 tP (pc 24 5 qtP qtP) &&
    kqP.all (fun k => pinSpan 24 5 tP (pc 24 5 (pcj 24 5 k (pinv 24 5 k) qtP) (pinv 24 5 qtP))) &&
    pcosetOK 24 5 b0P r2P rsP) = true := by quickRfl

theorem kGens : ((List.range 2).all (fun j => Nat.beq (CMO.S j) (pw (moGenW.getD j []))) &&
    (List.range 2).all (fun j => Nat.beq (CNS.S j) (pw (nsGenW.getD j []))) &&
    (List.range 3).all (fun j => Nat.beq (CLS.S j) (wcj (njW.getD j []) y5W)) &&
    (List.range 2).all (fun j => Nat.beq (CNQ.S j) (pw (nqGenW.getD j []))) &&
    (List.range 3).all (fun j => Nat.beq (CLQ.S j) (wcj (mjW.getD j []) y7W)) &&
    (List.range 2).all (fun j => Nat.beq (CNT.S j) (pw (ntGenW.getD j []))) &&
    (List.range 2).all (fun j => Nat.beq (CKQ.S j) (pw (kqGenW.getD j [])))) = true := by quickRfl

theorem kOrd : (Nat.beq (ordK CMO.LR 5) 322560 && Nat.beq (ordK CNS.LR 6) 138240 &&
    Nat.beq (ordK CLS.LR 5) 69120 && Nat.beq (ordK CNQ.LR 5) 21504 &&
    Nat.beq (ordK CLQ.LR 5) 10752 && Nat.beq (ordK CNT.LR 5) 64512 &&
    Nat.beq (ordK CKQ.LR 5) 21504) = true := by quickRfl

theorem kSift : (sW.all (fun w => canonK 24 5 (mask 5) (24 * 5) (pw w) &&
      siftK 24 5 (mask 5) (24 * 5) (pidn 24 5) CLS.LR CLS.TRI CLS.BP 5 0 (pw w)) &&
    etW.all (fun w => canonK 24 5 (mask 5) (24 * 5) (pw w) &&
      siftK 24 5 (mask 5) (24 * 5) (pidn 24 5) CLQ.LR CLQ.TRI CLQ.BP 5 0 (pw w))) = true := by
  quickRfl

theorem kTR : ((trPL 24 5 M24C2.LR M24C2.TR 4).all (fun L => L.all fun t =>
      permOK 24 5 (mask 5) (24 * 5) t (pinv 24 5 t)) &&
    (trPL 24 5 M24C1.LR M24C1.TR 3).all (fun L => L.all fun t =>
      permOK 24 5 (mask 5) (24 * 5) t (pinv 24 5 t)) &&
    (trPL 24 5 CLQ.LR CLQ.TR 5).all (fun L => L.all fun t =>
      permOK 24 5 (mask 5) (24 * 5) t (pinv 24 5 t)) &&
    (trPL 24 5 CLS.LR CLS.TR 5).all (fun L => L.all fun t =>
      permOK 24 5 (mask 5) (24 * 5) t (pinv 24 5 t))) = true := by quickRfl

end CertificateChecks.KernelKGC31M24

end
