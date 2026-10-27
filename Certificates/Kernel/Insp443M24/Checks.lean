module

public import Certificates.Kernel.Insp443M24.Defs
import CFSG.Certificates.Kernel.Common.Harness
public import Certificates.Kernel.Insp443M24.Data

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelInsp443M24

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KC.KGC31P CFSG.KS.SporSch.MOC
open CFSG.Quasithin.KGC31.M24 CFSG.SectionRank.QTK.Insp443.M24 CertificateChecks.KernelSporSch
open CertificateChecks.KernelKGC31M24

theorem ch725001g1 : (cAll gP tP).all (pinSpan 24 5 etP) = true := by quickRfl

theorem ch725001g2 : (pebasis 24 5 sixP && sixP.all (pinSpan 24 5 etP) &&
    canonK 24 5 (mask 5) (24 * 5) lP &&
    siftK 24 5 (mask 5) (24 * 5) (pidn 24 5) CLQ.LR CLQ.TRI CLQ.BP 5 0 lP) = true := by quickRfl

theorem ch725001g3 : (pord 24 5 7 xP && Nat.beq (pc 24 5 b0P xP) (pc 24 5 xP b0P) &&
    cjP.all (fun c => Nat.beq (pc 24 5 b0P c) (pc 24 5 c b0P)) &&
    (List.range 3).all (fun j => Nat.beq (CCB.S j) (wcj (cjW.getD j []) xW)) &&
    Nat.beq (ordK CCB.LR 4) 21504) = true := by quickRfl

theorem ch725001g4 : (pmasksOK 24 5 etP nP nMasks &&
    lqP.all (fun g => pinSpan 24 5 etP (pc 24 5 (pcj 24 5 g (pinv 24 5 g) nP) (pinv 24 5 nP))) &&
    pebasis 24 5 (u5P ++ cAll nP u5P) && u5P.all (pinSpan 24 5 etP) &&
    ((nqGenW.map pw).zip nqEtMasks).all (fun p => pmasksOK 24 5 etP p.1 p.2) &&
    pmasksOK 24 5 etP y7P y7EtMasks &&
    ((mjW.map pw).zip mjEtMasks).all (fun p => pmasksOK 24 5 etP p.1 p.2)) = true := by quickRfl

end CertificateChecks.KernelInsp443M24
