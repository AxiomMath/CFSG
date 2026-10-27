module

public import Certificates.Data.Kernel.IdxFourChainK
import CFSG.Certificates.Kernel.Common.JsonGz
import CFSG.Certificates.Kernel.Common.Repo

public section

#kc_repo #kc_json_gz CFSG.KD.IF4E "Certificates/Kernel/IdxFour/data/e0chain.json.gz" 100199
  5510760524462366798 (B : List Nat) (O : List Nat) (SP : Nat) (SI : Nat) (WD : List (List Nat))
  (TL : List (List Nat)) (T : List Nat) (PS : List Nat) (TR : List (List (List Nat)))
  (R : List (List (List Nat)))

namespace CFSG.KD.IF4E

open CFSG.KC.IF4C

@[expose] noncomputable def blk (i c : Nat) : Bool := blkOK SP T O TL R i c

@[expose] noncomputable def lvl (i : Nat) : Bool :=
  cntOK O TL R i && treeOK SP T O TL TR i && posOK T O PS B i

@[expose] noncomputable def gens : Bool :=
  tlOK SP B TL 10 1 && tlOK SP B TL 10 2 && tlOK SP B TL 10 3 && tlOK SP B TL 10 4 &&
    invOK SP SI 10 && wordsOK SP SI 10 WD 3

end CFSG.KD.IF4E

end
