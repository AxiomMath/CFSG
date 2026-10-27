module

public import Certificates.Kernel.Th.AutD.Defs
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelTh.AutD

open CFSG.KC.Enum CFSG.KS CFSG.KS.Prim CFSG.KS.Raw CFSG.KC.BfsPin CFSG.KC.L34K
open CFSG.KS.PEnum CertificateChecks.KernelTh.AutDG CFSG.Sporadic.Th.Recog
open CFSG.KLie.CT (fget andB orB notB)

theorem k_enum : bAnd(gensK letArr 51 6 ADE.k ADE.G, bAnd(Nat.beq ADE.cnt 3456,
    bAnd(penumHdK (pidn 51 6) ADE.cnt 3456 ADE.T ADE.PL,
    bAnd(Nat.beq AOA.k 6, bAnd(Nat.beq AOB.k 6,
    bAnd(allN 6 (fun j => bAnd(Nat.beq (AOA.G j) (L j), bAnd(Nat.beq (AOA.GI j) (LI j),
      bAnd(Nat.beq (AOB.G j) (L j), Nat.beq (AOB.GI j) (LI j))))),
    bAnd(Nat.beq AOA.cnt 144, bAnd(Nat.beq AOB.cnt 144,
    bAnd(penumHdK (H 0) AOA.cnt 3456 AOA.T AOA.PL,
    bAnd(penumHdK X1 AOB.cnt 3456 AOB.T AOB.PL,
    bAnd(penumSlK 51 6 (mask 6) (51 * 6) true AOA.G AOA.GI AOA.k AOA.cnt AOA.T AOA.PL AOA.POS
      AOA.SRT AOA.SRI 0 144,
      penumSlK 51 6 (mask 6) (51 * 6) true AOB.G AOB.GI AOB.k AOB.cnt AOB.T AOB.PL AOB.POS
        AOB.SRT AOB.SRI 0 144))))))))))) = true := by
  quickRfl

theorem k_let : allN 6 (fun j => andB (canonK 51 6 (mask 6) (51 * 6) (LI j))
    (andB (Nat.beq (pc (L j) (LI j)) (pidn 51 6)) (Nat.beq (pc (LI j) (L j)) (pidn 51 6)))) =
    true := by
  quickRfl

theorem k_pi : allN 9 (fun k => andB (bindArrK (piArr.push iotaTab)[k]! 51 6 (PI k))
    (andB (canonK 51 6 (mask 6) (51 * 6) (PI k)) (andB (canonK 51 6 (mask 6) (51 * 6) (PII k))
    (andB (Nat.beq (pc (PI k) (PII k)) (pidn 51 6)) (Nat.beq (pc (PII k) (PI k)) (pidn 51 6)))))) =
    true := by
  quickRfl

theorem k_pic : allN 8 (fun k => andB (allN 6 fun j =>
      Nat.beq (pc (pc (PII k) (L j)) (PI k)) (wK L LI ((wYList.getD k []).getD j [])))
    (andB (Nat.beq (pc (pc (PI k) (L 0)) (PII k)) (L 0))
      (Nat.beq (pc (pc (PI k) (L 5)) (PII k)) (L 5)))) = true := by
  quickRfl

theorem k_iota : allN 6 (fun j => Nat.beq (pc (pc (PI 8) (L j)) (PII 8))
    (Bool.rec (motive := fun _ => Nat) (L j) (LI 5) (Nat.beq j 5))) = true := by
  quickRfl

theorem k_part : allN 4 (fun t =>
    strictB (wK L LI (mWord ([Twist.id, .f1, .f3, .f13].getD t .id))) fun m =>
    strictB (wK L LI (FreeGroup.invRev (mWord ([Twist.id, .f1, .f3, .f13].getD t .id)))) fun mi =>
      allN 6 fun j => Nat.beq (pc (pc (PI t) (L j)) (PII t))
        (pc (pc (PI 8) (pc (pc (PI (Nat.add 4 t)) (pc (pc mi (L j)) m)) (PII (Nat.add 4 t))))
          (PII 8))) = true := by
  quickRfl

theorem k_hgen : andB (allN 6 fun j => Nat.beq (wK (g2 (H 0) (H 1)) (g2 (HI 0) (HI 1))
      (lW (Fin.ofNat 6 j))) (L j))
    (andB (ord24K (H 0)) (andB (testK (H 0) (HI 0) (H 1) (HI 1))
      (andB (canonK 51 6 (mask 6) (51 * 6) (H 0)) (andB (canonK 51 6 (mask 6) (51 * 6) (H 1))
        (andB (Nat.beq (pc (H 0) (HI 0)) (pidn 51 6)) (andB (Nat.beq (pc (HI 0) (H 0)) (pidn 51 6))
          (andB (Nat.beq (pc (H 1) (HI 1)) (pidn 51 6)) (andB (Nat.beq (pc (X1) (X1I)) (pidn 51 6))
            (Nat.beq (pc (X1I) (X1)) (pidn 51 6)))))))))) = true := by
  quickRfl

end CertificateChecks.KernelTh.AutD

end
