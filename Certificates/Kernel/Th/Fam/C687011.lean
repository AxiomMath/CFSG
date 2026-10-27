module

public import Certificates.Kernel.Th.Fam.C687008
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 100000

namespace CertificateChecks.KernelTh.Fam.F11

open CFSG.KC.Th.Expr CFSG.Sporadic.Th.Recog

@[expose] noncomputable def bq (e f : TE) : Bool := Nat.beq (e.pk thK) (f.pk thK)

@[expose] noncomputable def cm (e f : TE) : Bool := bq (.mul e f) (.mul f e)

@[expose] def cT : TE := wjT 2
@[expose] def dT : TE := wjT 3
@[expose] def eT : TE := wjT 4
@[expose] def sT : TE := wjT 5
@[expose] def tT : TE := wjT 6
@[expose] def uT : TE := wjT 7
@[expose] def uiT : TE := .pow uT 3
@[expose] def x1T : TE := .pow (.mul cT dT) 2
@[expose] def w1T : TE := .mul dT eT
@[expose] def w1iT : TE := .mul eT dT
@[expose] def y1T : TE := .mul (.mul w1T x1T) w1iT
@[expose] def x2T : TE := .mul (.mul uT x1T) uiT
@[expose] def w2T : TE := .mul (.mul uT w1T) uiT
@[expose] def e0T : TE := .mul (.mul dT cT) dT
@[expose] def e1T : TE := .mul (.mul uT e0T) uiT

@[expose] def e8N (n : Nat) : TE :=
  .mul (.mul (.pow .a (n % 2)) (.pow e0T (n / 2 % 2))) (.pow e1T (n / 4))

@[expose] def preN (n : Nat) : TE :=
  .mul (.mul (.pow w1T (n / 6)) (.pow w2T (n / 2 % 3))) (.pow dT (n % 2))

@[expose] def neL : List TE :=
  [cT, .mul (.mul (.mul (.mul dT eT) uT) dT) uiT, .mul (.mul (.mul (.mul dT eT) uT) dT) uT,
    .mul (.mul (.mul dT uT) dT) uT, .mul (.mul (.mul dT uT) dT) uiT]

@[expose] def ceL : List TE :=
  [.one, sT, .pow sT 6, .pow sT 2, .mul sT (.pow tT 2), .pow sT 5, .mul (.pow sT 6) (.pow tT 2)]

@[expose] def ceiL : List TE :=
  [.one, .pow sT 6, sT, .pow sT 5, .mul tT (.pow sT 6), .pow sT 2, .mul tT sT]

@[expose] def cnL : List TE :=
  [.mul (.mul (.mul dT eT) uT) dT, sT, .pow sT 2, .pow sT 3, .mul (.mul (.mul dT eT) dT) tT,
    .mul (.mul sT (.mul (.mul dT eT) dT)) sT]

@[expose] def cniL : List TE :=
  [.mul (.mul (.mul dT uiT) eT) dT, .pow sT 6, .pow sT 5, .pow sT 4,
    .mul (.pow tT 2) (.mul (.mul dT eT) dT), .mul (.mul (.pow sT 6) (.mul (.mul dT eT) dT)) (.pow sT 6)]

@[expose] def tg0 (i : Fin 5) : Nat := [3, 4, 5, 6, 7].getD i.val 0

@[expose] def tg1 (i : Fin 5) : Nat := [5, 2, 3, 3, 2].getD i.val 0

@[expose] noncomputable def pkR : Bool :=
  bq (.mul y1T x1T) (.mul (.pow x1T 3) y1T) && bq (.mul w1T y1T) (.mul (.mul y1T x1T) w1T) &&
    cm x1T x2T && cm x1T w2T && cm w1T x2T && cm w1T w2T

@[expose] noncomputable def pkE : Bool :=
  cm e0T e1T &&
    (List.finRange 8).all fun l =>
      (List.finRange l).all fun l' => bq (e8N l.val) (e8N l'.val) == false

@[expose] noncomputable def pkN : Bool :=
  (List.finRange 5).all fun i =>
    cm (neL.getD i.val .one) tT &&
      bq (.mul (neL.getD i.val .one) e0T) (.mul (e8N (tg0 i)) (neL.getD i.val .one)) &&
      bq (.mul (neL.getD i.val .one) e1T) (.mul (e8N (tg1 i)) (neL.getD i.val .one))

@[expose] noncomputable def pkCE : Bool :=
  (List.finRange 512).all fun k =>
    !cm (.nf k) tT ||
      (List.finRange 18).all fun a =>
        !(cm (.mul (preN a.val) (.nf k)) e0T && cm (.mul (preN a.val) (.nf k)) e1T) ||
          (decide (a = 0) && (List.finRange 8).any fun l => bq (.nf k) (e8N l.val))

@[expose] noncomputable def pkC : Bool :=
  (List.finRange 7).all (fun i =>
      bq (.mul (ceL.getD i.val .one) (ceiL.getD i.val .one)) .one &&
        cm (ceL.getD i.val .one) e0T) &&
    (List.finRange 6).all fun j =>
      bq (.mul (cnL.getD j.val .one) (cniL.getD j.val .one)) .one &&
        cm (cnL.getD j.val .one) e0T

@[expose] noncomputable def pkA : Bool :=
  (List.finRange 512).all fun k =>
    !cm (.nf k) e0T ||
      (List.finRange 4).any (fun l => bq (.nf k) (e8N l.val)) ||
      (List.finRange 6).any (fun j =>
        !cm (.mul (.mul (cnL.getD j.val .one) (.nf k)) (cniL.getD j.val .one)) (.nf k)) ||
      (List.finRange 7).any fun i =>
        (List.finRange 4).any fun l =>
          bq (.mul (.mul (ceL.getD i.val .one) (.nf k)) (ceiL.getD i.val .one)) (.mul e1T (e8N l.val))

theorem ok687011R : pkR = true := by quickRfl

theorem ok687011E : pkE = true := by quickRfl

theorem ok687011N : pkN = true := by quickRfl

theorem ok687011CE : pkCE = true := by quickRfl

theorem ok687011C : pkC = true := by quickRfl

theorem ok687011A : pkA = true := by quickRfl

end CertificateChecks.KernelTh.Fam.F11

end
