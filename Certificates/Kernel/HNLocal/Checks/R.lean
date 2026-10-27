module

public import Certificates.Kernel.HNLocal.Data
public import Certificates.Data.Kernel.HNMultK
public import CFSG.Certificates.Kernel.Orders.HN.Data.Sel
import CFSG.Certificates.Kernel.Common.Harness

set_option maxRecDepth 100000
set_option maxHeartbeats 0

public section

namespace CFSG.KD.HNLocal

theorem roots : CFSG.KC.Ord.rootsOK RB vld (nat_lit 0x1) (nat_lit 0x30) = true := by quickRfl

theorem invs : CFSG.KC.Ord.invsOK RB mul vld (nat_lit 0x2f) CFSG.KD.OrdHN.ONE = true := by quickRfl

theorem rws : CFSG.KC.HNMult.relWRange RB mul (nat_lit 0x2f) CFSG.KD.OrdHN.ONE WDL (nat_lit 0x0)
    (nat_lit 0x2d) = true := by
  quickRfl

theorem pc0 : Nat.beq (PC (nat_lit 0x0)) (CFSG.KD.OrdHN.RW (CFSG.KC.Ord.at16
    (nat_lit 0x153014a013d01340127011a010f010200fb00f300e900e100d500cc) (nat_lit 0x0))) = true := by
  quickRfl

theorem pc1 : Nat.beq (PC (nat_lit 0x1)) (CFSG.KD.OrdHN.RW (CFSG.KC.Ord.at16
    (nat_lit 0x153014a013d01340127011a010f010200fb00f300e900e100d500cc) (nat_lit 0x1))) = true := by
  quickRfl

theorem pc2 : Nat.beq (PC (nat_lit 0x2)) (CFSG.KD.OrdHN.RW (CFSG.KC.Ord.at16
    (nat_lit 0x153014a013d01340127011a010f010200fb00f300e900e100d500cc) (nat_lit 0x2))) = true := by
  quickRfl

theorem pc3 : Nat.beq (PC (nat_lit 0x3)) (CFSG.KD.OrdHN.RW (CFSG.KC.Ord.at16
    (nat_lit 0x153014a013d01340127011a010f010200fb00f300e900e100d500cc) (nat_lit 0x3))) = true := by
  quickRfl

theorem pc4 : Nat.beq (PC (nat_lit 0x4)) (CFSG.KD.OrdHN.RW (CFSG.KC.Ord.at16
    (nat_lit 0x153014a013d01340127011a010f010200fb00f300e900e100d500cc) (nat_lit 0x4))) = true := by
  quickRfl

theorem pc5 : Nat.beq (PC (nat_lit 0x5)) (CFSG.KD.OrdHN.RW (CFSG.KC.Ord.at16
    (nat_lit 0x153014a013d01340127011a010f010200fb00f300e900e100d500cc) (nat_lit 0x5))) = true := by
  quickRfl

theorem pc6 : Nat.beq (PC (nat_lit 0x6)) (CFSG.KD.OrdHN.RW (CFSG.KC.Ord.at16
    (nat_lit 0x153014a013d01340127011a010f010200fb00f300e900e100d500cc) (nat_lit 0x6))) = true := by
  quickRfl

theorem pc7 : Nat.beq (PC (nat_lit 0x7)) (CFSG.KD.OrdHN.RW (CFSG.KC.Ord.at16
    (nat_lit 0x153014a013d01340127011a010f010200fb00f300e900e100d500cc) (nat_lit 0x7))) = true := by
  quickRfl

theorem pc8 : Nat.beq (PC (nat_lit 0x8)) (CFSG.KD.OrdHN.RW (CFSG.KC.Ord.at16
    (nat_lit 0x153014a013d01340127011a010f010200fb00f300e900e100d500cc) (nat_lit 0x8))) = true := by
  quickRfl

theorem pc9 : Nat.beq (PC (nat_lit 0x9)) (CFSG.KD.OrdHN.RW (CFSG.KC.Ord.at16
    (nat_lit 0x153014a013d01340127011a010f010200fb00f300e900e100d500cc) (nat_lit 0x9))) = true := by
  quickRfl

theorem pc10 : Nat.beq (PC (nat_lit 0xa)) (CFSG.KD.OrdHN.RW (CFSG.KC.Ord.at16
    (nat_lit 0x153014a013d01340127011a010f010200fb00f300e900e100d500cc) (nat_lit 0xa))) = true := by
  quickRfl

theorem pc11 : Nat.beq (PC (nat_lit 0xb)) (CFSG.KD.OrdHN.RW (CFSG.KC.Ord.at16
    (nat_lit 0x153014a013d01340127011a010f010200fb00f300e900e100d500cc) (nat_lit 0xb))) = true := by
  quickRfl

theorem pc12 : Nat.beq (PC (nat_lit 0xc)) (CFSG.KD.OrdHN.RW (CFSG.KC.Ord.at16
    (nat_lit 0x153014a013d01340127011a010f010200fb00f300e900e100d500cc) (nat_lit 0xc))) = true := by
  quickRfl

theorem pc13 : Nat.beq (PC (nat_lit 0xd)) (CFSG.KD.OrdHN.RW (CFSG.KC.Ord.at16
    (nat_lit 0x153014a013d01340127011a010f010200fb00f300e900e100d500cc) (nat_lit 0xd))) = true := by
  quickRfl

theorem ra : Nat.beq (RB (nat_lit 0x1)) (CFSG.KD.OrdHN.RW (nat_lit 0x1)) = true := by quickRfl

theorem rb : Nat.beq (RB (nat_lit 0x2)) (CFSG.KD.OrdHN.RW (nat_lit 0x2)) = true := by quickRfl

end CFSG.KD.HNLocal

end
