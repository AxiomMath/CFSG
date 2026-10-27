module

public import Certificates.Data.Kernel.IdxFourChainK
import CFSG.Certificates.Kernel.Common.JsonGz
import CFSG.Certificates.Kernel.Common.Repo

public section

#kc_repo #kc_json_gz CFSG.KD.IF4K "Certificates/Kernel/IdxFour/data/skchain.json.gz" 34044
  1595185594363432734 (B : List Nat) (O : List Nat) (SP : Nat) (SI : Nat) (WD : List (List Nat))
  (TL : List (List Nat)) (T : List Nat) (PS : List Nat) (TR : List (List (List Nat)))
  (R : List (List (List Nat))) (W : List (List Nat))

namespace CFSG.KD.IF4K

open CFSG.KC.IF4C

@[expose] noncomputable def blk (i c : Nat) : Bool := blkOK SP T O TL R i c

@[expose] noncomputable def lvl (i : Nat) : Bool :=
  cntOK O TL R i && treeOK SP T O TL TR i && posOK T O PS B i

@[expose] noncomputable def gens : Bool :=
  tlOK SP B TL 5 1 && invOK SP SI 5 && wordsOK SP SI 5 WD 4

end CFSG.KD.IF4K

end
