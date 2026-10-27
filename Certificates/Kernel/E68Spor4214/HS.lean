module

public import Certificates.Kernel.E68Spor4214.HSD
public import Certificates.Kernel.LocalQT.HS4089.SD
public import Certificates.Data.Kernel.SporLatOm
public import Certificates.Data.Kernel.LocalQT.PermW
public import Certificates.Data.E68Spor.Words
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.SporLatHSInputs
import CFSG.Certificates.Kernel.Common.Harness

set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false

public section

namespace CFSG.KD.E68S4214.HS

open CFSG.KC.SLOm CFSG.Quasithin.E6.Spor CFSG.QuasithinUnique.Ch1.SporLat.HS

@[expose] noncomputable def cL : List Nat :=
  [CFSG.KD.LQT.H4089S.TF 172, CFSG.KD.LQT.H4089S.TF 185, CFSG.KD.LQT.H4089S.TF 200, TF 0]

@[expose] noncomputable def L (l p : Nat) : Nat := CFSG.KC.LQT.PW.imgW 11 (cL.getD l 0) p

@[expose] noncomputable def AB (l p : Nat) : Nat :=
  CFSG.KC.LQT.PW.imgW 11 (CFSG.KD.LQT.H4089S.TF l) p

@[expose] noncomputable def Z (p : Nat) : Nat :=
  CFSG.KC.LQT.PW.imgW 11 (CFSG.KD.LQT.H4089S.TF 164) p

theorem r_ok : rChkF 1100 hsDelta L 3 AB Z hsUWords hsYWord hsNWord 5 15 100 = true := by
  quickRfl

theorem nc_ok : ncChkF 1100 (AB 0) Z = true := by
  quickRfl

end CFSG.KD.E68S4214.HS

end
