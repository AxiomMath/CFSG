module

public import Certificates.Data.Kernel.ReflExt.ReflExtK
public import Certificates.Data.CFSGNative.ReflExt.E6
public import Certificates.Data.CFSGNative.ReflExt.A5
import CFSG.Certificates.Kernel.Common.JsonGz
import CFSG.Certificates.Kernel.Common.Repo

public section

#kc_repo #kc_json_gz CFSG.KD.RX708604 "Certificates/Kernel/ReflExt/data/rx.json.gz"
  1520113 4261724799404072707 (e6 : List CFSG.ReflExt.RXK.FD) (a5 : List CFSG.ReflExt.RXK.FD)

namespace CFSG.KD.RX708604

open CFSG.TwoNodeSmall CFSG.TwoNodeSmall.WitK CFSG.ReflExt CFSG.ReflExt.RXK

@[expose] def pt0 : Pt := ⟨0, 0, 0, [], [], 0⟩

@[expose] def fd0 : FD := ([], [], [], [], [])

@[expose] def e6Fs : List Pt := [e6Frame 6 0, e6Frame 7 1, e6Frame 7 0]

@[expose] def a5Fs : List Pt := [a5Frame 5, a5Frame 6]

@[expose] noncomputable def ce (i : Nat) : Bool :=
  partK (nthK pt0 e6Fs (i / 5)) (nthK fd0 e6 (i / 5)) (i % 5)

@[expose] noncomputable def ca (i : Nat) : Bool :=
  partK (nthK pt0 a5Fs (i / 5)) (nthK fd0 a5 (i / 5)) (i % 5)

end CFSG.KD.RX708604

end
