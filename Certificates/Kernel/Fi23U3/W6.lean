module

public import Certificates.Data.Kernel.InvWords
public import Certificates.Data.CFSGNative.ComponentPrimary.Cover3Fi23
import CFSG.Certificates.Kernel.Common.JsonGz
import CFSG.Certificates.Kernel.Common.Repo

public section

#kc_repo #kc_json_gz CFSG.KD.Fi23W6 "Certificates/Kernel/Fi23U3/data/w6.json.gz" 6066 970640858517818600
  (cert : List (List Nat))

namespace CFSG.KD.Fi23W6

open CFSG.SectionRank.Native

@[expose] def rels0 : List (List Nat) := fi23U3Cover3.relCodes.map (List.map fun x => x / 2 % 4)

theorem check : CFSG.KC.InvWords.invCheck rels0 cert [1, 2, 1, 2, 1, 2, 1, 2, 1, 2, 1, 2] = true := by
  decide +kernel

theorem check_neg_drop :
    (!CFSG.KC.InvWords.invCheck rels0 cert.tail [1, 2, 1, 2, 1, 2, 1, 2, 1, 2, 1, 2]) = true := by
  decide +kernel

theorem check_neg_target :
    (!CFSG.KC.InvWords.invCheck rels0 cert [1, 2, 1, 2, 1, 2, 1, 2, 1, 2]) = true := by
  decide +kernel

theorem check_neg_extra :
    (!CFSG.KC.InvWords.invCheck rels0 ([0, 1] :: cert) [1, 2, 1, 2, 1, 2, 1, 2, 1, 2, 1, 2]) =
      true := by
  decide +kernel

end CFSG.KD.Fi23W6
