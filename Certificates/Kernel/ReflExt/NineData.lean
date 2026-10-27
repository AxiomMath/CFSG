module

public import Certificates.Data.Kernel.ReflExt.NineK
public import Certificates.Data.CFSGNative.NineAll.Check
import CFSG.Certificates.Kernel.Common.JsonGz
import CFSG.Certificates.Kernel.Common.Repo

public section

set_option maxRecDepth 200000

#kc_repo #kc_json_gz CFSG.KD.NK708606 "Certificates/Kernel/ReflExt/data/nk.json.gz"
  12143994 14400712317496241855 (fr : List CFSG.ReflExt.NK.FDN)

namespace CFSG.KD.NK708606

open CFSG.TwoNodeSmall CFSG.TwoNodeSmall.WitK CFSG.NineAll CFSG.ReflExt.NK

@[expose] def pt0 : Pt := ⟨0, 0, 0, [], [], 0⟩

@[expose] def fd0 : FDN := ([], [], [], [], [], [])

@[expose] def nineFs : List Pt := [nineFrame8 (), nineFrame9 ()]

@[expose] noncomputable def cn (i : Nat) : Bool :=
  partN (nthK pt0 nineFs (i / 20)) nineBstab (nthK fd0 fr (i / 20)) (i % 20)

end CFSG.KD.NK708606

end
