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

@[expose] def gPF (w T p : Nat) : Nat :=
  Nat.land (Nat.shiftRight T (Nat.mul w p)) (Nat.sub (Nat.shiftLeft 1 w) 1)

theorem gPF_eq (w T p : Nat) : gPF w T p = gP w T p := by
  show (T >>> (w * p)) &&& (1 <<< w - 1) = T / 2 ^ (w * p) % 2 ^ w
  rw [Nat.one_shiftLeft, Nat.and_two_pow_sub_one_eq_mod, Nat.shiftRight_eq_div_pow]

@[expose] def packLF (w : Nat) : List Nat → Nat
  | [] => 0
  | a :: l => Nat.add a (Nat.mul (Nat.shiftLeft 1 w) (packLF w l))

theorem packLF_eq (w : Nat) : ∀ l, packLF w l = packL w l
  | [] => rfl
  | a :: l => by
    show a + (1 <<< w) * packLF w l = a + 2 ^ w * packL w l
    rw [Nat.one_shiftLeft, packLF_eq w l]

@[expose] def actSF (w n : Nat) (Ls : List (Nat × Nat)) (l : Nat) (x : List Nat) : List Nat :=
  [packLF w ((List.range n).map fun q =>
    gPF w (Ls.getD l (0, 0)).1 (gPF w (x.headD 0) (gPF w (Ls.getD l (0, 0)).2 q)))]

theorem actSF_eq : actSF = actS := by
  funext w n Ls l x
  simp only [actSF, actS, conjP, packLF_eq, gPF_eq]

theorem orb_ok : orbChk (actS 9 315 [pk 9 315 ta, pk 9 315 tb]) 2 [pz 9 315 zT] 315 = true := by
  rw [← actSF_eq]
  quickRfl

theorem r_ok : rChkC 315 D L 3 AB (N 143) j2UWords j2YWord j2NWord 5 15 100 = true := by
  quickRfl

end CFSG.KD.E68S4214.J2

end
