module

import CFSG.Certificates.Kernel.Common.HarnessGzTree
import CFSG.Certificates.Kernel.Common.JsonGz
import CFSG.Certificates.Kernel.Common.Repo
public import Certificates.Kernel.Sporadic.Fi24Br.Data
public import Certificates.Data.Kernel.Ssa3

#kc_repo #kc_ktree_gz CFSG.KD.Fi24Cp MT "Certificates/Kernel/Sporadic/Fi24Cp/data/mats.bin.gz" 152491 4 22111195 17938997051326631593
#kc_repo #kc_json_gz CFSG.KD.Fi24Cp "Certificates/Kernel/Sporadic/Fi24Cp/data/cp.json.gz" 16443 14683821741514945273
  (NK : List Nat) (NA : List Nat) (NB : List Nat) (NS : List Nat) (OPN : List Nat) (FV : List Nat)
  (CB : List Nat) (QB : List Nat) (QK : List Nat) (QX : List Nat) (QY : List Nat) (QT : List Nat)
  (QF : List Nat)

public section

namespace CFSG.KD.Fi24Cp

@[expose] noncomputable def AR : CFSG.KC.Ssa3.Ar :=
  ⟨CFSG.KD.BrFi24.MUL, CFSG.KD.BrFi24.ONE, CFSG.KD.BrFi24.RB 23, CFSG.KD.BrFi24.RB 24, MT, 781,
    609961, CFSG.KD.BrFi24.RM⟩

@[expose] noncomputable def SD : CFSG.KC.Ssa3.SData := ⟨NK, NA, NB, NS, OPN, FV, CB, QB, QK, QX, QY, QT, QF⟩

@[expose] noncomputable def chk (c : Nat) : Bool := CFSG.KC.Ssa3.chunkOK AR SD c

end CFSG.KD.Fi24Cp

end
