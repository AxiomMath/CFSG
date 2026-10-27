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

theorem irels : IREL.all (relW RB mul 46 CFSG.KD.OrdHN.ONE) = true := by quickRfl

theorem s2rel : relW RB mul 46 CFSG.KD.OrdHN.ONE S2W = true := by quickRfl

theorem ra : Nat.beq (RB 1) (CFSG.KD.OrdHN.RW 1) = true := by quickRfl

theorem rb : Nat.beq (RB 2) (CFSG.KD.OrdHN.RW 2) = true := by quickRfl

end CFSG.KD.HN25550

end
