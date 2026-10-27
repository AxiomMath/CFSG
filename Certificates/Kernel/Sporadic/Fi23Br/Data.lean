module

import CFSG.Certificates.Kernel.Common.Harness
import CFSG.Certificates.Kernel.Common.Repo
public import CFSG.Certificates.Kernel.Orders.Cert

#kc_repo #kc_ktree CFSG.KD.BrFi23 MT "Certificates/Kernel/Sporadic/Fi23Br/data/mats.bin" 88013 6 3080455 11924354789306080938

public noncomputable section

namespace CFSG.KD.BrFi23

@[expose] def L : Nat := CFSG.KC.Ord.rep1 (nat_lit 11) (nat_lit 64009)

@[expose] def H : Nat := Nat.shiftLeft L (nat_lit 10)

@[expose] def CM : Nat := Nat.mul (nat_lit 2047) (CFSG.KC.Ord.rep1 (nat_lit 2783) (nat_lit 253))

@[expose] def RM : Nat := Nat.sub (Nat.shiftLeft (nat_lit 1) (nat_lit 2783)) (nat_lit 1)

@[expose] def ONE : Nat := CFSG.KC.Ord.rep1 (nat_lit 2794) (nat_lit 253)

@[expose] def LV : Nat := CFSG.KC.Ord.rep1 (nat_lit 11) (nat_lit 253)

@[expose] def HV : Nat := Nat.shiftLeft LV (nat_lit 10)

@[expose] def RB (k : Nat) : Nat :=
  [nat_lit 0, MT 0, MT 1, MT 2, MT 3, MT 4, MT 5, MT 6, MT 7, MT 8, MT 9, MT 10, MT 11,
    MT 0, MT 1, MT 2, MT 3, MT 4, MT 5, MT 6, MT 7, MT 8, MT 9, MT 10, MT 12].getD k (nat_lit 0)

end CFSG.KD.BrFi23

end

#kc_repo #kc_ktree CFSG.KD.BrFi23 P1 "CFSG/Blueprint/Data/F23G1-f3r253B0.m1" 256 4 65042 9686454688332762093
#kc_repo #kc_ktree CFSG.KD.BrFi23 P2 "CFSG/Blueprint/Data/F23G1-f3r253B0.m2" 256 4 65042 11467227030737908174
