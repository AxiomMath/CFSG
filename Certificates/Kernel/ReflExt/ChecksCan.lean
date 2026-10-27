module

public import Certificates.Kernel.ReflExt.Data
public import Certificates.Data.Kernel.ReflExt.ReflExtKCan
import CFSG.Certificates.Kernel.Common.EachTrue
import CFSG.Certificates.Kernel.Common.Harness
public import CFSG.Certificates.Kernel.Common.Lce

public section

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace CFSG.KD.RX708604

open CFSG.TwoNodeSmall CFSG.TwoNodeSmall.WitK CFSG.ReflExt CFSG.ReflExt.RXK CFSG.KC

@[expose] noncomputable def cn (i : Nat) : Bool :=
  bif Nat.blt i 3 then canK (nthK pt0 e6Fs i) (nthK fd0 e6 i)
  else canK (nthK pt0 a5Fs (Nat.sub i 3)) (nthK fd0 a5 (Nat.sub i 3))

end CFSG.KD.RX708604

#kc_each CFSG.KD.RX708604.chCan708604 f_ CFSG.KD.RX708604.cn 0 5

namespace CFSG.KD.RX708604

open CFSG.TwoNodeSmall CFSG.TwoNodeSmall.WitK CFSG.ReflExt CFSG.ReflExt.RXK CFSG.KC

theorem nCan708604 : notB (canK (e6Frame 7 1) (let f := nthK fd0 e6 1
    (f.1, f.2.1, f.2.2.1, f.2.2.2.1, match f.2.2.2.2 with
      | [] => []
      | rp :: rs => (((rp.1.1 + 3, rp.1.2), rp.2) : RXK.Rep) :: rs))) = true := by quickRfl

end CFSG.KD.RX708604

end
