module

public import Init
import CFSG.Certificates.Kernel.Common.JsonGz
import CFSG.Certificates.Kernel.Common.HarnessGzTree
import CFSG.Certificates.Kernel.Common.Repo

#kc_repo #kc_json_gz CFSG.KD.HSZC "Certificates/Kernel/HSZC/data/gens.json.gz" 27525
  3857419663486192640 (A : Nat) (AI : Nat) (B : Nat) (BI : Nat) (IDN : Nat) (Z : List Nat)
  (ZI : List Nat) (ZW : Nat) (ZL : Nat) (ZP : Nat) (G : List Nat) (SW : List Nat) (SL : List Nat)
  (H2 : Nat) (H2W : Nat) (H2L : Nat) (VP : List Nat) (VC : List Nat) (REPS : List Nat)
  (NC1 : List (List Nat)) (NC2 : List (List Nat)) (K3 : Nat) (K3P : Nat) (PM : Nat) (RO : Nat)
  (RE : Nat) (RH : Nat) (NL : Nat) (NX : Nat) (NS : Nat) (NH : Nat)

#kc_repo #kc_ktree_gz CFSG.KD.HSZC OT "Certificates/Kernel/HSZC/data/olist.bin.gz" 96 4
  2032800 8396163814630355387

#kc_repo #kc_ktree_gz CFSG.KD.HSZC ET "Certificates/Kernel/HSZC/data/elist.bin.gz" 99 4
  50688 17379982615774517023

#kc_repo #kc_ktree_gz CFSG.KD.HSZC HT "Certificates/Kernel/HSZC/data/hlist.bin.gz" 93 4
  15624 2004469356364346676

public section

namespace CFSG.KD.HSZC

@[expose] noncomputable def zP (e : Nat) : Nat := List.getD Z e (nat_lit 0)

@[expose] noncomputable def zPI (e : Nat) : Nat := List.getD ZI e (nat_lit 0)

@[expose] noncomputable def gS (j : Nat) : Nat := List.getD G j (nat_lit 0)

@[expose] noncomputable def wS (j : Nat) : Nat := List.getD SW j (nat_lit 0)

@[expose] noncomputable def lS (j : Nat) : Nat := List.getD SL j (nat_lit 0)

@[expose] noncomputable def vP (k : Nat) : Nat := List.getD VP k (nat_lit 0)

@[expose] noncomputable def vC (k : Nat) : Nat := List.getD VC k (nat_lit 0)

@[expose] noncomputable def rep (i : Nat) : Nat := List.getD REPS i (nat_lit 0)

end CFSG.KD.HSZC

end
