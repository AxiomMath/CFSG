module

public import Certificates.Data.Kernel.WE8K.Defs
import CFSG.Certificates.Kernel.Common.JsonGz
import CFSG.Certificates.Kernel.Common.Repo

public section

#kc_repo #kc_json_gz CFSG.KD.WE8K "Certificates/Kernel/WE8K/data/we8.json.gz" 2669129
  11370651469866713143
  (permP : Nat) (negP : Nat) (addP : Nat) (adjM : Nat)
  (oS : List Nat) (oL : List (List Nat)) (oN : List Nat)
  (xp : Nat) (qp : List Nat) (bp : Nat) (cp : Nat) (np : Nat)
  (xm : Nat) (qm : List Nat) (bm : Nat) (cm : Nat) (nm : Nat)

namespace CFSG.KD.WE8K

open CFSG.KC.WE8K

@[expose] noncomputable def orbFam (k : Nat) : Bool := orbF permP negP addP adjM oS oL oN k

@[expose] noncomputable def symPFam (k : Nat) : Bool := symF qp xp bp cp k

@[expose] noncomputable def symMFam (k : Nat) : Bool := symF qm xm bm cm k

end CFSG.KD.WE8K

end
