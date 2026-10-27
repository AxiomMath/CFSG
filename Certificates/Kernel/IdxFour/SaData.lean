module

public import Certificates.Data.Kernel.IdxFourChainK
import CFSG.Certificates.Kernel.Common.JsonGz
import CFSG.Certificates.Kernel.Common.Repo

public section

#kc_repo #kc_json_gz CFSG.KD.IF4S "Certificates/Kernel/IdxFour/data/sachain.json.gz" 56139
  4785188013438877605 (B : List Nat) (O : List Nat) (SP : Nat) (SI : Nat) (WD : List (List Nat))
  (TL : List (List Nat)) (T : List Nat) (PS : List Nat) (TR : List (List (List Nat)))

namespace CFSG.KD.IF4S

open CFSG.KC.IF4C

@[expose] noncomputable def lvl (i : Nat) : Bool := treeOK SP T O TL TR i && posOK T O PS B i

@[expose] noncomputable def gens : Bool :=
  tlOK SP B TL 9 1 && tlOK SP B TL 9 2 && tlOK SP B TL 9 3 && tlOK SP B TL 9 4 &&
    tlOK SP B TL 9 5 && invOK SP SI 9 && wordsOK SP SI 9 WD 3

end CFSG.KD.IF4S

end
