module

public import Certificates.Kernel.E68Spor4215.D
public import Certificates.Kernel.LocalQT.Base.C4141D
public import Certificates.Data.Kernel.SporLatOm
public import Certificates.Data.Kernel.LocalQT.PermW
public import Certificates.Data.E68Spor.Words
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.SporLatHeCertificateInputs
import CFSG.Certificates.Kernel.Common.Harness

set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false

public section

namespace CFSG.KD.E68S4215.He

open CFSG.KC.SLOm CFSG.Quasithin.E6.Spor CFSG.QuasithinUnique.Ch1.SporLat.He

@[expose] noncomputable def cL : List Nat :=
  [CFSG.KD.LQT.C4141.TF 197, CFSG.KD.LQT.C4141.TF 207, CFSG.KD.LQT.C4141.TF 226,
    CFSG.KD.LQT.C4141.TF 247, TF 0]

@[expose] noncomputable def L (l p : Nat) : Nat := CFSG.KC.LQT.PW.imgW 14 (cL.getD l 0) p

@[expose] noncomputable def AB (l p : Nat) : Nat :=
  CFSG.KC.LQT.PW.imgW 14 (CFSG.KD.LQT.C4141.TF l) p

@[expose] noncomputable def Z (p : Nat) : Nat := CFSG.KC.LQT.PW.imgW 14 (CFSG.KD.LQT.C4141.TF 170) p

theorem r_ok : rChkF 8330 heDelta L 4 AB Z heUWords heYWord heNWord 7 21 100 = true := by
  quickRfl

theorem nc_ok : ncChkF 8330 (AB 0) Z = true := by
  quickRfl

end CFSG.KD.E68S4215.He

end
