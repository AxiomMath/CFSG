module

public import Certificates.Kernel.Sporadic.Fi24Ext.Data
public import Certificates.Kernel.Sporadic.Fi24Fix.DataI
import CFSG.Certificates.Kernel.Common.Harness

public section

namespace CFSG.KD.Fi24Ext

theorem rr : CFSG.KC.Fi24Ext.digRowsOK (Nat.land Rr CFSG.KD.BrFi24.LO)
    (Nat.shiftRight Rr (nat_lit 609961)) CFSG.KD.Fi24Fix.CT (nat_lit 253) (nat_lit 528) true
    (nat_lit 0) (nat_lit 253) (nat_lit 4) = true := by
  quickRfl

theorem rz : CFSG.KC.Fi24Ext.zeroFromOK (Nat.land Rr CFSG.KD.BrFi24.LO)
    (Nat.shiftRight Rr (nat_lit 609961)) (nat_lit 253) = true := by
  quickRfl

theorem qd : CFSG.KC.Fi24Ext.digRowsOK (Nat.land Q CFSG.KD.BrFi24.LO)
    (Nat.shiftRight Q (nat_lit 609961)) CTQ (nat_lit 0) (nat_lit 253) false (nat_lit 0) (nat_lit 253)
    (nat_lit 4) = true := by
  quickRfl

theorem qz : CFSG.KC.Fi24Ext.zeroFromOK (Nat.land Q CFSG.KD.BrFi24.LO)
    (Nat.shiftRight Q (nat_lit 609961)) (nat_lit 253) = true := by
  quickRfl

end CFSG.KD.Fi24Ext

end
