module

public import Init
import CFSG.Certificates.Kernel.Common.JsonGz
import CFSG.Certificates.Kernel.Common.HarnessGzTree
import CFSG.Certificates.Kernel.Common.Repo

#kc_repo #kc_json_gz CFSG.KD.J2ZC "Certificates/Kernel/J2ZC/data/gens.json.gz" 14715
  14829421818414813905 (A : Nat) (AI : Nat) (B : Nat) (BI : Nat) (IDN : Nat) (Z : List Nat)
  (ZI : List Nat) (G : List Nat) (SW : List Nat) (SL : List Nat) (PM : Nat) (RO : Nat) (RE : Nat)
  (NL : Nat) (NS : Nat)

#kc_repo #kc_ktree_gz CFSG.KD.J2ZC OT "Certificates/Kernel/J2ZC/data/olist.bin.gz" 361 4
  1023435 1199333550704806855

#kc_repo #kc_ktree_gz CFSG.KD.J2ZC ET "Certificates/Kernel/J2ZC/data/elist.bin.gz" 364 4
  46592 4888098839974183748

public section

namespace CFSG.KD.J2ZC

@[expose] noncomputable def zP (e : Nat) : Nat := List.getD Z e (nat_lit 0)

@[expose] noncomputable def zPI (e : Nat) : Nat := List.getD ZI e (nat_lit 0)

@[expose] noncomputable def gS (j : Nat) : Nat := List.getD G j (nat_lit 0)

@[expose] noncomputable def wS (j : Nat) : Nat := List.getD SW j (nat_lit 0)

@[expose] noncomputable def lS (j : Nat) : Nat := List.getD SL j (nat_lit 0)

end CFSG.KD.J2ZC

end
