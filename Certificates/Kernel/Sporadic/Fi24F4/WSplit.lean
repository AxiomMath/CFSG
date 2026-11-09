module

public import Certificates.Kernel.Sporadic.Fi24F4.WC
public import Certificates.Kernel.Sporadic.Fi24Kit.Split

public section

namespace CFSG.KD.Fi24F4.Ck

open CFSG.KC CFSG.KC.LceS CFSG.KC.Fi24F4W
open CFSG.KC.Fi24FixP (fixS)

theorem coverOK_of3 {NW : Nat → Nat → Nat} {NT : Nat → Nat} {cs : List Nat} {t : Bool}
    {c0 c1 c2 : List Nat} {q0 : Nat} {E : List Nat} {X Y0 Y1 Y2 : Nat}
    (hb : fixS (rPl NW NT cs t) = X)
    (h0 : fixS (CFSG.KC.Fi24Kit.walkP NW c0) = Y0)
    (h1 : fixS (CFSG.KC.Fi24Kit.walkP NW c1) = Y1)
    (h2 : fixS (CFSG.KC.Fi24Kit.walkP NW c2) = Y2)
    (h : letB (Nat.land Y0 (Nat.land Y1 (Nat.land Y2 X)))
      (fun A => Nat.beq (Nat.land A (bitsL (q0 :: E))) A) = true) :
    coverOK NW NT cs t [c0, c1, c2] q0 E = true := by
  unfold coverOK
  show letB (Nat.land (fixS (CFSG.KC.Fi24Kit.walkP NW c0)) (Nat.land (fixS (CFSG.KC.Fi24Kit.walkP NW c1)) (Nat.land (fixS (CFSG.KC.Fi24Kit.walkP NW c2)) (fixS (rPl NW NT cs t)))))
    (fun A => Nat.beq (Nat.land A (bitsL (q0 :: E))) A) = true
  rw [hb, h0, h1, h2]
  exact h

theorem coverOK_of5 {NW : Nat → Nat → Nat} {NT : Nat → Nat} {cs : List Nat} {t : Bool}
    {c0 c1 c2 c3 c4 : List Nat} {q0 : Nat} {E : List Nat} {X Y0 Y1 Y2 Y3 Y4 : Nat}
    (hb : fixS (rPl NW NT cs t) = X)
    (h0 : fixS (CFSG.KC.Fi24Kit.walkP NW c0) = Y0)
    (h1 : fixS (CFSG.KC.Fi24Kit.walkP NW c1) = Y1)
    (h2 : fixS (CFSG.KC.Fi24Kit.walkP NW c2) = Y2)
    (h3 : fixS (CFSG.KC.Fi24Kit.walkP NW c3) = Y3)
    (h4 : fixS (CFSG.KC.Fi24Kit.walkP NW c4) = Y4)
    (h : letB (Nat.land Y0 (Nat.land Y1 (Nat.land Y2 (Nat.land Y3 (Nat.land Y4 X)))))
      (fun A => Nat.beq (Nat.land A (bitsL (q0 :: E))) A) = true) :
    coverOK NW NT cs t [c0, c1, c2, c3, c4] q0 E = true := by
  unfold coverOK
  show letB (Nat.land (fixS (CFSG.KC.Fi24Kit.walkP NW c0)) (Nat.land (fixS (CFSG.KC.Fi24Kit.walkP NW c1)) (Nat.land (fixS (CFSG.KC.Fi24Kit.walkP NW c2)) (Nat.land (fixS (CFSG.KC.Fi24Kit.walkP NW c3)) (Nat.land (fixS (CFSG.KC.Fi24Kit.walkP NW c4)) (fixS (rPl NW NT cs t)))))))
    (fun A => Nat.beq (Nat.land A (bitsL (q0 :: E))) A) = true
  rw [hb, h0, h1, h2, h3, h4]
  exact h

end CFSG.KD.Fi24F4.Ck

end
