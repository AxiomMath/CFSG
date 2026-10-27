module

public import Certificates.Kernel.E68Spor4215.D
public import Certificates.Kernel.LocalQT.Base.C4143D
public import Certificates.Data.Kernel.SporLatOm
public import Certificates.Data.Kernel.LocalQT.PermW
public import Certificates.Data.E68Spor.Words
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.SporLatRuCertificateInputs
import CFSG.Certificates.Kernel.Common.Harness

set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false

public section

namespace CFSG.KD.E68S4215.Ru

open CFSG.KC.SLOm CFSG.Quasithin.E6.Spor CFSG.QuasithinUnique.Ch1.SporLat.RuCert

@[expose] noncomputable def cL : List Nat :=
  [CFSG.KD.LQT.C4143.TF 163, CFSG.KD.LQT.C4143.TF 172, CFSG.KD.LQT.C4143.TF 185, TF 0]

@[expose] noncomputable def L (l p : Nat) : Nat := CFSG.KC.LQT.PW.imgW 12 (cL.getD l 0) p

@[expose] noncomputable def AB (l p : Nat) : Nat :=
  CFSG.KC.LQT.PW.imgW 12 (CFSG.KD.LQT.C4143.TF l) p

@[expose] noncomputable def Z (p : Nat) : Nat := CFSG.KC.LQT.PW.imgW 12 (CFSG.KD.LQT.C4143.TF 154) p

theorem r_ok : rChkF 4060 ruDelta L 3 AB Z ruUWords ruYWord ruNWord 5 15 100 = true := by
  quickRfl

theorem nc_ok : ncChkF 4060 (AB 0) Z = true := by
  quickRfl

end CFSG.KD.E68S4215.Ru

end
