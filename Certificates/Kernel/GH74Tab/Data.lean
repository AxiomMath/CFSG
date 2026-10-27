module

public import Certificates.Data.Kernel.GH74Tab.Defs
import CFSG.Certificates.Kernel.Common.JsonGz
import CFSG.Certificates.Kernel.Common.Repo

public section

#kc_repo #kc_json_gz CFSG.KD.GH74Tab "Certificates/Kernel/GH74Tab/data/tab.json.gz"
  46845 17013055011236119549
  (T : Nat) (I : Nat) (one : Nat) (x0 : Nat) (Q : Nat) (C : Nat) (Tr : List (List Nat))
  (rel : List Nat) (L : List (List Nat)) (NM : List (List Nat)) (NL : List (List (List Nat)))
  (CM : Nat) (IV : Nat) (adm : List (Nat × Nat)) (adm7 : List (Nat × Nat))

namespace CFSG.KD.GH74Tab

@[expose] noncomputable def dat : CFSG.KC.GH74Tab.Dat :=
  ⟨T, I, one, x0, Q, C, Tr, rel, L, NM, NL, CM, IV, adm, adm7⟩

end CFSG.KD.GH74Tab

end
