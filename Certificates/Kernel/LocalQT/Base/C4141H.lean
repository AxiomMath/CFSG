module

public import Certificates.Kernel.LocalQT.Base.C4141N
public import Certificates.Kernel.LocalQT.Base.C4141S
public import Certificates.Kernel.He4049.T
import CFSG.Certificates.Kernel.Common.Harness

set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false

public section

namespace CFSG.KD.LQT.C4141

open CFSG.KC.LQT.BS CFSG.QuasithinUnique.K1.SporadicPerm

@[expose] noncomputable def ta : List Nat :=
  (List.range 8330).map (CFSG.KC.Enum.pg 14 16383 (CFSG.KD.He4049.TF 0))

@[expose] noncomputable def tb : List Nat :=
  (List.range 8330).map (CFSG.KC.Enum.pg 14 16383 (CFSG.KD.He4049.TF 1))

theorem valid : slpValidAux heProg 2 = true := by quickRfl

theorem hd : baseSK 8330 14 heB ta tb heProg heQp TF 34 8 131 RT 170 249 253 251 255 10 100000
    1024 10 E 4 256 = true := by
  quickRfl

end CFSG.KD.LQT.C4141

end
