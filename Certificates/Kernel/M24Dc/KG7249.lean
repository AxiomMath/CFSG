module

public import CFSG.Quasithin.Vol2.Ch12Sec5KGM24KInputs
public import Certificates.Data.Kernel.M24QSpan
public import Certificates.Kernel.M24Dc.Idx3
import CFSG.Certificates.Kernel.Common.Harness

set_option maxRecDepth 100000
set_option maxHeartbeats 0

public section

namespace CFSG.KD.M24Dc

open CFSG.KC.SLDc CFSG.QuasithinUnique.Ch1.SporLat CFSG.Quasithin.H13.S125KG.M24

theorem chkXK_ok : chkXK () = true := by
  unfold chkXK inYK labW
  rw [codeSetAct_eq, delta_eqK]
  quickRfl

theorem chkAlphaK_ok : chkAlphaK () = true := by
  unfold chkAlphaK inYK labW
  rw [codeSetAct_eq, delta_eqK]
  quickRfl

theorem chkKK_ok : chkKK () = true := by
  unfold chkKK inYK labW
  rw [codeSetAct_eq, delta_eqK]
  quickRfl

theorem chkQF_ok : chkQF () = true := by
  unfold chkQF inYK labW
  rw [codeSetAct_eq, delta_eqK]
  quickRfl

theorem chkVWK_ok : chkVWK () = true := by
  unfold chkVWK inYK labW
  rw [codeSetAct_eq, delta_eqK]
  quickRfl

theorem latCheckK_ok : latCheckK () = true := by
  unfold latCheckK gensInK
  rw [codeSetAct_eq, delta_eqK]
  quickRfl

end CFSG.KD.M24Dc

end
