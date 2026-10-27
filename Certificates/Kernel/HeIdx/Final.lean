module

public import Certificates.Kernel.HeIdx.C3
public import Certificates.Kernel.HeIdx.C9
public import Certificates.Kernel.HeDc.Final
public import CFSG.Certificates.Kernel.S151IdxFSound
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.SporLatHeKInputs

set_option maxRecDepth 100000

public section

namespace CFSG.KD.HeIdx

open CFSG.KC.IdxF CFSG.KC.E64F CFSG.Quasithin.S151S9T CFSG.QuasithinUnique.Ch1.SporLat
open CFSG.QuasithinUnique.Ch1.SporLat.He CFSG.QuasithinUnique.K1.SporadicPerm


theorem hyp : Hyp 8330 heMemW 11 4 mlen CFSG.KD.HeDc.Lm Sl where
  nm_eq := CFSG.KD.HeDc.mw_size
  ns_eq := CFSG.KD.HeDc.sTabs_len
  len := fun j hj => by
    change (CFSG.KD.HeDc.heLatK.mt[j]!).length = _
    rw [CFSG.KD.HeDc.mt_get hj, List.length_map, mlen, CFSG.KD.HeDc.mwJ]
  goodM := fun j hj => CFSG.KD.HeDc.good_m hj
  goodS := fun l hl => CFSG.KD.HeDc.good_s (by simpa [heMemW, CFSG.KD.HeDc.sTabs_len] using hl)

theorem good_z : Good 8330 heSLPC[170]! Z := by
  rw [CFSG.KD.He7149.hSLPC]
  exact CFSG.KD.E68S4215.good_he (by decide)

theorem he_idx_ok : heWit1.Ok 8330 ptAct heDelta heMemW (heSLPC[170]!) ∧
    heWit9.Ok 8330 ptAct heDelta heMemW :=
  ⟨idx3OkF_sound hyp good_z idx3_ok, idx9OkF_sound hyp idx9_ok⟩

end CFSG.KD.HeIdx

end
