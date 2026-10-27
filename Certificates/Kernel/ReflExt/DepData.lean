module

public import Certificates.Data.Kernel.ReflExt.DepK
public import Certificates.Data.CFSGNative.DepFrame.A5
import CFSG.Certificates.Kernel.Common.JsonGz
import CFSG.Certificates.Kernel.Common.Repo

public section

set_option maxRecDepth 200000

#kc_repo #kc_json_gz CFSG.KD.DK708607 "Certificates/Kernel/ReflExt/data/dk.json.gz"
  191688 12810910528523121245 (fr : List CFSG.ReflExt.NK.FDN)

namespace CFSG.KD.DK708607

open CFSG.TwoNodeSmall CFSG.TwoNodeSmall.WitK CFSG.DepFrame CFSG.ReflExt.NK CFSG.ReflExt.DK

@[expose] def fd0 : FDN := ([], [], [], [], [], [])

@[expose] noncomputable def f0 : FDN := nthK fd0 fr 0

@[expose] noncomputable def cd (i : Nat) : Bool := partD (a5DepPt ()) a5DepBstab f0 i

end CFSG.KD.DK708607

end
