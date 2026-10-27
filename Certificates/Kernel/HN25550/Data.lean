module

public import CFSG.Certificates.Kernel.Orders.Cert
public import CFSG.Certificates.Kernel.Orders.HN.Data.Const
public import CFSG.Certificates.Kernel.Bounds.Core3
import CFSG.Certificates.Kernel.Bounds.LoadGz
import CFSG.Certificates.Kernel.Common.JsonGz
import CFSG.Certificates.Kernel.Common.Repo

#kc_repo #kc_items_gz CFSG.KD.HN25550.RB "Certificates/Kernel/HN25550/data/regs.bin.gz" 2643499 11861112722744672404
#kc_repo #kc_json_gz CFSG.KD.HN25550 "Certificates/Kernel/HN25550/data/c25550.json.gz"
  14162 9310129353436276987
  (L : Nat) (RW : List (List Nat)) (REL : List (List Nat)) (SP : List Nat) (HJ : List Nat)
  (C6J : List Nat) (C6 : List Nat) (U : Nat) (HC : Nat) (G6C : Nat) (M2 : List Nat) (M2R1 : Nat)
  (E61 : Nat) (G6S : List Nat) (G6 : List Nat) (PW : List (List Nat)) (PR : List Nat)
  (SG : List Nat) (PP : List Nat) (CNT : Nat) (PAR : List Nat) (LAB : List Nat) (NW : List Nat)
  (INV : List Nat) (IREL : List (List Nat)) (S2N : Nat) (S2W : List Nat)

public section

namespace CFSG.KD.HN25550

noncomputable abbrev mul : Nat → Nat → Nat :=
  CFSG.KC.Ord.mulR 5 13 1729 133 9 CFSG.KD.OrdHN.L CFSG.KD.OrdHN.H CFSG.KD.OrdHN.CM CFSG.KD.OrdHN.RM

noncomputable abbrev vld : Nat → Bool := CFSG.KC.Ord.validM 5 229957 CFSG.KD.OrdHN.L CFSG.KD.OrdHN.H

end CFSG.KD.HN25550

end
