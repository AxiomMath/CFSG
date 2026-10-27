module

public import Certificates.Data.Kernel.ReflExt.MovK
public import Certificates.Data.CFSGNative.DepFrame.E6
import CFSG.Certificates.Kernel.Common.JsonGz
import CFSG.Certificates.Kernel.Common.Repo

public section

set_option maxRecDepth 200000

#kc_repo #kc_json_gz CFSG.KD.MK708608 "Certificates/Kernel/ReflExt/data/mk.json.gz"
  148563 9561274441116129894 (fr : List CFSG.ReflExt.NK.FDN)

namespace CFSG.KD.MK708608

open CFSG.TwoNodeSmall CFSG.TwoNodeSmall.WitK CFSG.DepFrame CFSG.ReflExt.NK CFSG.ReflExt.MK

@[expose] def fd0 : FDN := ([], [], [], [], [], [])

@[expose] noncomputable def f0 : FDN := nthK fd0 fr 0

@[expose] noncomputable def cd (i : Nat) : Bool := partM (e6DepPt ()) f0 i

end CFSG.KD.MK708608

end
