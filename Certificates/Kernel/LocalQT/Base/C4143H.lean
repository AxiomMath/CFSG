module

public import Certificates.Kernel.LocalQT.Base.C4143N
public import Certificates.Kernel.LocalQT.Base.C4143S
public import Certificates.Kernel.VecCert.Ru
import CFSG.Certificates.Kernel.Common.Harness

set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false

public section

namespace CFSG.KD.LQT.C4143

open CFSG.KC.LQT.BS CFSG.QuasithinUnique.K1.SporadicPerm CFSG.KC.VecK
open CertificateChecks.KernelVec.Ru (AT BT)

@[expose] noncomputable def ta : List Nat := (List.range 4060).map (lk AT 32)

@[expose] noncomputable def tb : List Nat := (List.range 4060).map (lk BT 32)

theorem valid : slpValidAux ruProg 2 = true := by quickRfl

theorem hd : baseSK 4060 12 ruB ta tb ruProg ruQp TF 26 8 64 RT 154 187 191 189 193 14 100000
    16384 14 E 16 1024 = true := by
  quickRfl

end CFSG.KD.LQT.C4143

end
