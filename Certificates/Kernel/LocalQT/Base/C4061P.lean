module

public import Certificates.Kernel.LocalQT.Base.C4061L
public import CFSG.Certificates.Kernel.LocalQTX1RSound
import CFSG.Certificates.Kernel.Common.Harness

set_option maxRecDepth 100000

public section

namespace CFSG.KD.LQT.C4061

open CFSG.KC.LQT.XR CFSG.QuasithinUnique.K1.SporadicPerm CFSG.QuasithinUnique.Setup.X1

theorem prog2_eq : ruProg2 = P2 := by
  apply eqPL_spec
  unfold ruProg2 ruExt
  rw [pairsOfFlat_eq]
  unfold ruExtFlat
  rw [Array.toList_flatten]
  quickRfl

theorem wprog_eq : ruWprog = WP := by
  apply eqPL_spec
  unfold ruWprog
  rw [pairsOfFlat_eq]
  unfold ruWprogFlat
  rw [Array.toList_flatten]
  quickRfl

end CFSG.KD.LQT.C4061

end
