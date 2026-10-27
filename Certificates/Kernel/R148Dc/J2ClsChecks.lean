module

public import Certificates.Kernel.R148Dc.J2ClsData
public import Certificates.Kernel.R148Dc.J2ADefs
public import Certificates.Kernel.R148Dc.J2BDefs
import CFSG.Certificates.Kernel.Common.Harness

set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false

public noncomputable section

namespace CFSG.KD.R148Dc.J2A

open CFSG.KC.SLDc CFSG.KC.SLCls

@[expose] def memK (j : Nat) : Bool :=
  (96 % (Om j).lbl.size == 0) || clsOK L 315 (L 2) (mE j) (J2Cls.J.ca.getD j [])

theorem memsK : (List.range 9).all memK = true := by
  quickRfl

theorem mwK : (J.mw.length == 9 && J.mw.all fun ws => ws.all fun w => w.all fun l => Nat.blt l 2) =
    true := by
  quickRfl

end CFSG.KD.R148Dc.J2A

namespace CFSG.KD.R148Dc.J2B

open CFSG.KC.SLDc CFSG.KC.SLCls

@[expose] def memK (j : Nat) : Bool :=
  (96 % (Om j).lbl.size == 0) || clsOK L 315 (L 2) (mE j) (J2Cls.J.cb.getD j [])

theorem memsK : (List.range 12).all memK = true := by
  quickRfl

theorem mwK : (J.mw.length == 12 &&
    J.mw.all fun ws => ws.all fun w => w.all fun l => Nat.blt l 2) = true := by
  quickRfl

end CFSG.KD.R148Dc.J2B

end
