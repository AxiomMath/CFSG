module

public import Certificates.Data.Kernel.Misc.Coset.Act
public import CFSG.Literature.ParrottTitsCheckInputs
import CFSG.Certificates.Kernel.Bounds.LoadRoot
import CFSG.Certificates.Kernel.Common.Repo

public section

#kc_repo #kc_blocked_root CFSG.KAct.P2004.A "Certificates/Kernel/Parrott/data/P2004.act" 8 4 65535 84240 16940767923485590841

namespace CFSG.KAct.P2004

open CFSG.Literature.ParrottTits CFSG.Monster.B.Co2

@[expose] def e2 (h : Fin 2) : Fin 12 := ⟨h.val, by omega⟩

@[expose] def sh (h : Fin 10) : Fin 12 := ⟨h.val + 2, by omega⟩

@[expose] def permWords : List (List (Fin 12 × Bool)) :=
  (parrottWords.map fun w => w.map fun l => (sh l.1, l.2)) ++
    ((List.finRange 2).map fun j => (e2 j, false) ::
      (toLetters 10 ([parrottD0Word, parrottD1Word].getD j.val [])).map fun l => (sh l.1, l.2))

@[expose] def rels : List (List Nat) :=
  permWords.map fun w => (w.map CFSG.Certificates.CosetEnumeration.letterCode).reverse

end CFSG.KAct.P2004

end
