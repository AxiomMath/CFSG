module

public import Certificates.Kernel.J2Dc.Defs
public import Certificates.Data.Kernel.S151IdxG
public import Certificates.Data.Kernel.LocalQT.Pipe
public import CFSG.Quasithin.EmptyFaithful.S151S9TJ2Inputs
import CFSG.Certificates.Kernel.Common.Harness

set_option maxRecDepth 100000
set_option maxHeartbeats 0

public section

namespace CFSG.KD.J2Dc

open CFSG.KC.LQT.PW CFSG.KC.LQT.PP CFSG.KC.LQT.BC CFSG.KC.IdxG CFSG.Quasithin.S151S9T
open CFSG.QuasithinUnique.K1.SporadicPerm

@[expose] noncomputable def wW (w : List Nat) : Nat :=
  w.foldr (fun l acc => mulW 315 9 (J.tc.getD l 0) acc) (oneW 315 9)

@[expose] noncomputable def mc (j l : Nat) : Nat :=
  if l < 3 then J.tc.getD (2 + l) 0 else wW ((J.mw.getD j []).getD (l - 3) [])

@[expose] noncomputable def zc : Nat :=
  nodeK (slpW 315 9 (J.tc.getD 0 0) (J.tc.getD 1 0) j2Prog) 143

@[expose] noncomputable def okG (W : Idx3Wit) : Bool :=
  idx3OkG W 315 (fixCodes 315 Δc) 5 3 (fun j => (J.mw.getD j []).length)
    (fun j l => imgW 9 (mc j l)) (fun l => L0 (2 + l)) (imgW 9 zc)

theorem okG_j2 : okG j2Wit = true := by quickRfl

theorem codesB : codesBelow 315 Δc = true := by quickRfl

end CFSG.KD.J2Dc

end
