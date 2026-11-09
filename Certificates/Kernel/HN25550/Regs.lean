module

public import Certificates.Kernel.HN25550.Data
public import Certificates.Data.Kernel.HNMultK
public import CFSG.Certificates.Kernel.Orders.HN.Data.Sel
import CFSG.Certificates.Kernel.Common.Harness

public section

namespace CFSG.KD.HN25550

open CFSG.KC.HNMult

theorem l_ok : Nat.beq L 46 = true := by quickRfl

theorem roots : CFSG.KC.Ord.rootsOK RB vld 1 47 = true := by quickRfl

theorem invs : CFSG.KC.Ord.invsOK RB mul vld 46 CFSG.KD.OrdHN.ONE = true := by quickRfl

theorem rels : REL.all (relW RB mul 46 CFSG.KD.OrdHN.ONE) = true := by quickRfl

theorem all_of_take_drop {α : Type} {f : α → Bool} (l : List α) (n : Nat)
    (h1 : (l.take n).all f = true) (h2 : (l.drop n).all f = true) : l.all f = true := by
  rw [← List.take_append_drop n l]
  simp only [List.all_append, h1, h2, Bool.and_self]

theorem irels0 :
    (List.take 24 IREL).all
      (relW RB mul 46 CFSG.KD.OrdHN.ONE) = true := by
  quickRfl

theorem irels1 :
    (List.take 17 (List.drop 24 IREL)).all
      (relW RB mul 46 CFSG.KD.OrdHN.ONE) = true := by
  quickRfl

theorem irels2 :
    (List.take 14 (List.drop 17 (List.drop 24 IREL))).all
      (relW RB mul 46 CFSG.KD.OrdHN.ONE) = true := by
  quickRfl

theorem irels3 :
    (List.take 14 (List.drop 14 (List.drop 17 (List.drop 24 IREL)))).all
      (relW RB mul 46 CFSG.KD.OrdHN.ONE) = true := by
  quickRfl

theorem irels4 :
    (List.take 13 (List.drop 14 (List.drop 14 (List.drop 17 (List.drop 24 IREL))))).all
      (relW RB mul 46 CFSG.KD.OrdHN.ONE) = true := by
  quickRfl

theorem irels5 :
    (List.take 12 (List.drop 13 (List.drop 14 (List.drop 14 (List.drop 17 (List.drop 24 IREL)))))).all
      (relW RB mul 46 CFSG.KD.OrdHN.ONE) = true := by
  quickRfl

theorem irels6 :
    (List.drop 12 (List.drop 13 (List.drop 14 (List.drop 14 (List.drop 17 (List.drop 24 IREL)))))).all
      (relW RB mul 46 CFSG.KD.OrdHN.ONE) = true := by
  quickRfl

theorem irels : IREL.all (relW RB mul 46 CFSG.KD.OrdHN.ONE) = true :=
  all_of_take_drop _ 24 irels0
    (all_of_take_drop _ 17 irels1
    (all_of_take_drop _ 14 irels2
    (all_of_take_drop _ 14 irels3
    (all_of_take_drop _ 13 irels4
    (all_of_take_drop _ 12 irels5
    (irels6))))))

theorem s2rel : relW RB mul 46 CFSG.KD.OrdHN.ONE S2W = true := by quickRfl

theorem ra : Nat.beq (RB 1) (CFSG.KD.OrdHN.RW 1) = true := by quickRfl

theorem rb : Nat.beq (RB 2) (CFSG.KD.OrdHN.RW 2) = true := by quickRfl

end CFSG.KD.HN25550

end
