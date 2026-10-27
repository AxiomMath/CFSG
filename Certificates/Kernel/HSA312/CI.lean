module

public import Certificates.Kernel.LocalQT.HS4089.L
public import Certificates.Data.Kernel.HSA312.Defs
public import Certificates.Data.Kernel.HSDc.Defs
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtA312HsInputs
import CFSG.Certificates.Kernel.Common.Harness

set_option maxRecDepth 100000
set_option maxHeartbeats 0set_option Elab.async false

public noncomputable section

namespace CFSG.KD.HSA312

open CFSG.KC.HSA312

@[expose] def inclB (j jj : Nat) : Bool :=
  gensInC 1100 11 2047 (CFSG.KD.LQT.H4089.TF 0) CFSG.KD.LQT.H4089.Lab
      (CFSG.KD.HSDc.J.mw.getD j []) CFSG.QuasithinUnique.Ch1.SporLat.HS.hsDelta
      (CFSG.KD.HSDc.Om jj).lbl.toList ==
    (CFSG.Quasithin.A312Hs.hsIncl.getD j []).contains jj

theorem incl : ((List.range 5).all fun j => (List.range 5).all fun jj => inclB j jj) = true := by
  quickRfl

end CFSG.KD.HSA312

end
