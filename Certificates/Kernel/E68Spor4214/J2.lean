module

public import Certificates.Data.Kernel.LocalQT.Pipe
public import Certificates.Data.Kernel.SporLatOrbP
public import Certificates.Data.Kernel.SporLatCodeR
public import Certificates.Data.E68Spor.Words
public import CFSG.Quasithin.Background.E2TwoProofSporJ2Inputs
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X1J2Data
import CFSG.Certificates.Kernel.Common.Harness

set_option maxRecDepth 100000
set_option maxHeartbeats 0

public section

namespace CFSG.KD.E68S4214.J2

open CFSG.KC.SLOrb CFSG.KC.SLOm CFSG.KC.E64F CFSG.KC.LQT.PP CFSG.KC.LQT.BC
open CFSG.QuasithinUnique.K1.SporadicPerm CFSG.Quasithin.E6.Spor

@[expose] def ta : List Nat :=
  CFSG.QuasithinUnique.Setup.X1.j2ta_0.toList ++ CFSG.QuasithinUnique.Setup.X1.j2ta_1.toList

@[expose] def tb : List Nat :=
  CFSG.QuasithinUnique.Setup.X1.j2tb_0.toList ++ CFSG.QuasithinUnique.Setup.X1.j2tb_1.toList

@[expose] noncomputable def R : List Nat := slpW 315 9 (codeK 9 ta) (codeK 9 tb) j2Prog

@[expose] noncomputable def N (j p : Nat) : Nat := CFSG.KC.LQT.PW.imgW 9 (nodeK R j) p

@[expose] noncomputable def zT : Array Nat := ((List.range 315).map (N 143)).toArray

@[expose] noncomputable def AB (l p : Nat) : Nat := N l p

@[expose] noncomputable def L (l p : Nat) : Nat :=
  if l < 3 then N ([155, 166, 179].getD l 0) p else wordF AB (j2UWords.getD (l - 3) []) p

@[expose] def D : List Nat :=
  insN (CFSG.Quasithin.E2P.SporB.J2Lat.j2Sets.map (CFSG.QuasithinUnique.Ch1.SporLat.encodeSet 315))

theorem tab_ok : (tabOK 9 315 ta.toArray tb.toArray && ltB 315 zT) = true := by
  quickRfl

theorem orb_ok : orbChk (actS 9 315 [pk 9 315 ta, pk 9 315 tb]) 2 [pz 9 315 zT] 315 = true := by
  quickRfl

theorem r_ok : rChkC 315 D L 3 AB (N 143) j2UWords j2YWord j2NWord 5 15 100 = true := by
  quickRfl

end CFSG.KD.E68S4214.J2

end
