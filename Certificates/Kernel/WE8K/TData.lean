module

public import Certificates.Kernel.WE8K.Data
public import Certificates.Data.Kernel.WE8K.Tab
import CFSG.Certificates.Kernel.Common.JsonGz
import CFSG.Certificates.Kernel.Common.Repo

public section

#kc_repo #kc_json_gz CFSG.KD.WE8K "Certificates/Kernel/WE8K/data/we8t.json.gz" 18744
  12784357839307889482
  (rT : Nat) (zW : List (List Nat))

namespace CFSG.KD.WE8K

open CFSG.KC.WE8K

@[expose] noncomputable def tabPFam (j : Nat) : Bool := tabPF rT permP j

@[expose] noncomputable def tabDFam (k : Nat) : Bool := tabDF rT addP k

@[expose] noncomputable def qPFam (k : Nat) : Bool := qF false qp rT k

@[expose] noncomputable def qMFam (k : Nat) : Bool := qF true qm rT k

@[expose] noncomputable def startFam (k : Nat) : Bool := startF oS k

@[expose] noncomputable def zwFam (i : Nat) : Bool :=
  zwOK permP negP addP adjM (nthN oS i) (nthL zW i) (nthN oS (Nat.sub (nat_lit 7) i))

end CFSG.KD.WE8K

end
