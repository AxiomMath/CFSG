module

public import Certificates.Kernel.HNLocal.Data
public import Certificates.Data.Kernel.HNMultK
public import Certificates.Kernel.HNLocal.Checks.Split
public import CFSG.Certificates.Kernel.Orders.HN.Data.Sel
import CFSG.Certificates.Kernel.Common.Harness

set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false

public section

namespace CFSG.KD.HNLocal

theorem roots : CFSG.KC.Ord.rootsOK RB vld (nat_lit 0x1) (nat_lit 0x30) = true := by quickRfl

theorem invs : CFSG.KC.Ord.invsOK RB mul vld (nat_lit 0x2f) CFSG.KD.OrdHN.ONE = true := by quickRfl

theorem rws_0 : CFSG.KC.HNMult.relWRange RB mul (nat_lit 0x2f) CFSG.KD.OrdHN.ONE WDL (nat_lit 0x0)
    (nat_lit 0x1) = true := by
  quickRfl

theorem rws_1 : CFSG.KC.HNMult.relWRange RB mul (nat_lit 0x2f) CFSG.KD.OrdHN.ONE WDL (nat_lit 0x1)
    (nat_lit 0x1) = true := by
  quickRfl

theorem rws_2 : CFSG.KC.HNMult.relWRange RB mul (nat_lit 0x2f) CFSG.KD.OrdHN.ONE WDL (nat_lit 0x2)
    (nat_lit 0x1) = true := by
  quickRfl

theorem rws_3 : CFSG.KC.HNMult.relWRange RB mul (nat_lit 0x2f) CFSG.KD.OrdHN.ONE WDL (nat_lit 0x3)
    (nat_lit 0x1) = true := by
  quickRfl

theorem rws_4 : CFSG.KC.HNMult.relWRange RB mul (nat_lit 0x2f) CFSG.KD.OrdHN.ONE WDL (nat_lit 0x4)
    (nat_lit 0x1) = true := by
  quickRfl

theorem rws_5 : CFSG.KC.HNMult.relWRange RB mul (nat_lit 0x2f) CFSG.KD.OrdHN.ONE WDL (nat_lit 0x5)
    (nat_lit 0x1) = true := by
  quickRfl

theorem rws_6 : CFSG.KC.HNMult.relWRange RB mul (nat_lit 0x2f) CFSG.KD.OrdHN.ONE WDL (nat_lit 0x6)
    (nat_lit 0x1) = true := by
  quickRfl

theorem rws_7 : CFSG.KC.HNMult.relWRange RB mul (nat_lit 0x2f) CFSG.KD.OrdHN.ONE WDL (nat_lit 0x7)
    (nat_lit 0x1) = true := by
  quickRfl

theorem rws_8 : CFSG.KC.HNMult.relWRange RB mul (nat_lit 0x2f) CFSG.KD.OrdHN.ONE WDL (nat_lit 0x8)
    (nat_lit 0x1) = true := by
  quickRfl

theorem rws_9 : CFSG.KC.HNMult.relWRange RB mul (nat_lit 0x2f) CFSG.KD.OrdHN.ONE WDL (nat_lit 0x9)
    (nat_lit 0x3) = true := by
  quickRfl

theorem rws_10 : CFSG.KC.HNMult.relWRange RB mul (nat_lit 0x2f) CFSG.KD.OrdHN.ONE WDL (nat_lit 0xc)
    (nat_lit 0x3) = true := by
  quickRfl

theorem rws_11 : CFSG.KC.HNMult.relWRange RB mul (nat_lit 0x2f) CFSG.KD.OrdHN.ONE WDL (nat_lit 0xf)
    (nat_lit 0x3) = true := by
  quickRfl

theorem rws_12 : CFSG.KC.HNMult.relWRange RB mul (nat_lit 0x2f) CFSG.KD.OrdHN.ONE WDL (nat_lit 0x12)
    (nat_lit 0x9) = true := by
  quickRfl

theorem rws_13 : CFSG.KC.HNMult.relWRange RB mul (nat_lit 0x2f) CFSG.KD.OrdHN.ONE WDL (nat_lit 0x1b)
    (nat_lit 0x9) = true := by
  quickRfl

theorem rws_14 : CFSG.KC.HNMult.relWRange RB mul (nat_lit 0x2f) CFSG.KD.OrdHN.ONE WDL (nat_lit 0x24)
    (nat_lit 0x9) = true := by
  quickRfl

theorem rws : CFSG.KC.HNMult.relWRange RB mul (nat_lit 0x2f) CFSG.KD.OrdHN.ONE WDL (nat_lit 0x0)
    (nat_lit 0x2d) = true := by
  have h := (relWRange_of (relWRange_of (relWRange_of (relWRange_of (relWRange_of (relWRange_of (relWRange_of (relWRange_of (relWRange_of (relWRange_of (relWRange_of (relWRange_of (relWRange_of (relWRange_of rws_0 rws_1) rws_2) rws_3) rws_4) rws_5) rws_6) rws_7) rws_8) rws_9) rws_10) rws_11) rws_12) rws_13) rws_14)
  exact h

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
