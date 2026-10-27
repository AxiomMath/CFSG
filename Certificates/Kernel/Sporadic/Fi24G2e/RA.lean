module

public import Certificates.Kernel.Sporadic.Fi24G2e.RData
public import Certificates.Kernel.SporSch.Ru.RowsGen
import CFSG.Certificates.Kernel.Common.Harness

set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false

public noncomputable section

namespace CFSG.KD.Fi24G2e

@[expose] def rsqC (i : Nat) : Bool :=
  Nat.beq (CFSG.KD.BrFi24.MUL (REP i) (REP i)) CFSG.KD.BrFi24.ONE

end CFSG.KD.Fi24G2e

namespace CFSG.KD.Fi24G2e.RA

open CFSG.KD.Fi24G2e CFSG.KD.BrFi24 CFSG.KD.Fi24Ext CFSG.KC.Fi24Fix

theorem h0sq : Nat.beq (MUL Fi24Ext.H0 Fi24Ext.H0) ONE = true := by quickRfl

theorem hs : Nat.beq (MUL Fi24Ext.H1 Fi24Ext.H1) HS = true := by quickRfl

theorem h1cb : Nat.beq (MUL Fi24Ext.H1 HS) ONE = true := by quickRfl

theorem d1h : Nat.beq (wordMul MUL HR HW1 ONE) D1H = true := by quickRfl

theorem d1 : Nat.beq (wordMul MUL HR HW0 D1H) D1 = true := by quickRfl

theorem d2 : Nat.beq (MUL D1 D1) D2 = true := by quickRfl

theorem d4 : Nat.beq (MUL D2 D2) D4 = true := by quickRfl

theorem d6 : Nat.beq (MUL D4 D2) D6 = true := by quickRfl

theorem d7 : Nat.beq (MUL D6 D1) RD = true := by quickRfl

theorem u2 : Nat.beq (MUL RD (MUL Fi24Ext.H0 (MUL RD Fi24Ext.H0))) RU2 = true := by quickRfl

theorem ww : Nat.beq (wordMul MUL HR WWL ONE) WW = true := by quickRfl

theorem wi : Nat.beq (wordMul MUL HR WIL ONE) WI = true := by quickRfl

theorem u3 : Nat.beq (MUL RU2 (MUL WW (MUL RD WI))) RU3 = true := by quickRfl

theorem dt : Nat.beq (MUL RD T) RDT = true := by quickRfl

theorem u2t : Nat.beq (MUL RU2 T) RU2T = true := by quickRfl

theorem u3t : Nat.beq (MUL RU3 T) RU3T = true := by quickRfl

theorem mwa : Nat.beq (wordMul MUL LG [0, 2] ONE) MWA = true := by quickRfl

theorem mwasq : Nat.beq (MUL MWA MWA) ONE = true := by quickRfl

theorem mwd : Nat.beq (wordMul MUL LG [0, 2, 4] ONE) MWD = true := by quickRfl

theorem mwdsq : Nat.beq (MUL MWD MWD) ONE = true := by quickRfl

theorem mwb : Nat.beq (wordMul MUL LG [0, 2, 4, 6] ONE) MWB = true := by quickRfl

theorem mwbsq : Nat.beq (MUL MWB MWB) ONE = true := by quickRfl

end CFSG.KD.Fi24G2e.RA

#kss_each CFSG.KD.Fi24G2e.RA.SQ CFSG.KD.Fi24G2e.rsqC 7

end
