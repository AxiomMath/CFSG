module

public import Certificates.Kernel.HS589207.M
import CFSG.Certificates.Kernel.Common.Harness
public import Certificates.Data.Kernel.BfsRecK

set_option maxRecDepth 100000
set_option maxHeartbeats 0

public section

namespace CFSG.KD.HS589207.ScanK

open CFSG.KC.DcHSOutK CFSG.KC.Enum

@[expose] noncomputable def centT (m : Nat) : Bool :=
  !(I0.all fun j => commF (mF m) (mF j)) || I0.contains m

@[expose] noncomputable def outT (m : Nat) : Bool :=
  (I0.all fun j => commF (fun q => wF (mF m q)) (mF j)) == IO.contains m

theorem c0 : allBlk 0 centT 2880 = true := by quickRfl

theorem c1 : allBlk 2880 centT 2880 = true := by quickRfl

theorem c2 : allBlk 5760 centT 2880 = true := by quickRfl

theorem c3 : allBlk 8640 centT 2880 = true := by quickRfl

theorem o0 : allBlk 0 outT 2880 = true := by quickRfl

theorem o1 : allBlk 2880 outT 2880 = true := by quickRfl

theorem o2 : allBlk 5760 outT 2880 = true := by quickRfl

theorem o3 : allBlk 8640 outT 2880 = true := by quickRfl

end CFSG.KD.HS589207.ScanK

end
