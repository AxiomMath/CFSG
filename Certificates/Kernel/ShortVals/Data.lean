module

public import CFSG.Certificates.Kernel.Common.HexNat
import CFSG.Certificates.Kernel.Common.JsonGz
import CFSG.Certificates.Kernel.Common.Repo

public section

namespace CFSG.KD.ShortVals

@[expose] def VPText : String := include_str "vp.hex"

@[expose] def RPText : String := include_str "rp.hex"

@[expose] def PPText : String := include_str "pp.hex"

#kc_repo #kc_json_gz CFSG.KD.ShortVals
  "Certificates/Kernel/ShortVals/data/Data.json.gz" 35991 5741302139902819597
  (AP : Nat) (WT : Nat) (OWT : Nat) (OC : Nat) (ET : Nat) (PT : Nat)

@[expose] noncomputable def VP : Nat := by
  hex_nat VPText 884520 12357827639421095003

@[expose] noncomputable def RP : Nat := by
  hex_nat RPText 417690 9255036168328988184

@[expose] noncomputable def PP : Nat := by
  hex_nat PPText 417690 4189901661931790143

end CFSG.KD.ShortVals

end
