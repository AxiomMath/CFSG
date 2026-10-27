module

public import Certificates.Data.Kernel.M22Out.Replay
public import CFSG.LocalAnalysis.EvenSporadicStandard.M22Std.OutTab47Check
public import Certificates.Kernel.M22Out24790.Data

public section

set_option maxRecDepth 200000
set_option maxHeartbeats 0

namespace CertificateChecks.KernelM22Out24790

open CFSG.KC.M22Out CFSG.KD.M22Out24790
open CFSG.EvenSporadicStandard.M22Std.TabCheck CFSG.EvenSporadicStandard.M22Std.FusionCheck
  CFSG.EvenSporadicStandard.M22Std.OutCheck

@[expose] noncomputable def TP : Nat := packTs T

@[expose] noncomputable def WP : Nat := packW W

@[expose] noncomputable def EW : List Nat := W.map encW

@[expose] noncomputable def segOK (s : Nat) : Bool :=
  Nat.beq (replayK TP WP (nGensTab.getD 0 idTab) (nGensTab.getD 1 idTab)
    ((T.drop (480 * s)).take 480) (EW.drop (480 * s)) (KK.drop (480 * s)) (480 * s) (cs.getD s 0))
    (cs.getD (s + 1) 0)

theorem ch24790seg0 : segOK 0 = true := by decide +kernel
theorem ch24790seg1 : segOK 1 = true := by decide +kernel
theorem ch24790seg2 : segOK 2 = true := by decide +kernel
theorem ch24790seg3 : segOK 3 = true := by decide +kernel
theorem ch24790seg4 : segOK 4 = true := by decide +kernel
theorem ch24790seg5 : segOK 5 = true := by decide +kernel
theorem ch24790seg6 : segOK 6 = true := by decide +kernel
theorem ch24790seg7 : segOK 7 = true := by decide +kernel
theorem ch24790seg8 : segOK 8 = true := by decide +kernel
theorem ch24790seg9 : segOK 9 = true := by decide +kernel
theorem ch24790seg10 : segOK 10 = true := by decide +kernel
theorem ch24790seg11 : segOK 11 = true := by decide +kernel

@[expose] def validT (t : Tab) : Bool := Nat.beq t.length 22 && t.all fun a => Nat.blt a 22

theorem ch24790head : (T.headD [] == idTab && W.headD [0] == [] && Nat.beq T.length 5760 &&
    Nat.beq W.length 5760 && Nat.beq KK.length 5760 && Nat.beq U.length 5760 &&
    Nat.beq (cs.getD 0 0) 1 && Nat.beq (cs.getD 12 0) 5760 &&
    KK.all (fun k => Nat.beq k.length 2) &&
    W.all (fun w => Nat.blt w.length 17 && w.all fun i => Nat.blt i 2)) = true := by
  decide +kernel

theorem ch24790valid : (T.all validT && U.all validT && IT.all validT) = true := by decide +kernel

@[expose] noncomputable def uSegOK (s : Nat) : Bool :=
  mapEqK (tmul betaTab) ((T.drop (960 * s)).take 960) ((U.drop (960 * s)).take 960)

theorem ch24790u0 : uSegOK 0 = true := by decide +kernel
theorem ch24790u1 : uSegOK 1 = true := by decide +kernel
theorem ch24790u2 : uSegOK 2 = true := by decide +kernel
theorem ch24790u3 : uSegOK 3 = true := by decide +kernel
theorem ch24790u4 : uSegOK 4 = true := by decide +kernel
theorem ch24790u5 : uSegOK 5 = true := by decide +kernel

theorem ch24790keys : (keysK (packKeys (T ++ U)) 11520 SG 0 && Nat.beq SG.length 11520) = true := by
  decide +kernel

@[expose] noncomputable def invSegOK (s : Nat) : Bool :=
  (((((T ++ U).drop (960 * s)).take 960).filter isInv).map packT) ==
    (((IT.drop (IC.getD s 0)).take (IC.getD (s + 1) 0 - IC.getD s 0)).map packT)

theorem ch24790i0 : invSegOK 0 = true := by decide +kernel
theorem ch24790i1 : invSegOK 1 = true := by decide +kernel
theorem ch24790i2 : invSegOK 2 = true := by decide +kernel
theorem ch24790i3 : invSegOK 3 = true := by decide +kernel
theorem ch24790i4 : invSegOK 4 = true := by decide +kernel
theorem ch24790i5 : invSegOK 5 = true := by decide +kernel
theorem ch24790i6 : invSegOK 6 = true := by decide +kernel
theorem ch24790i7 : invSegOK 7 = true := by decide +kernel
theorem ch24790i8 : invSegOK 8 = true := by decide +kernel
theorem ch24790i9 : invSegOK 9 = true := by decide +kernel
theorem ch24790i10 : invSegOK 10 = true := by decide +kernel
theorem ch24790i11 : invSegOK 11 = true := by decide +kernel

theorem ch24790ic : (Nat.beq (IC.getD 0 0) 0 && Nat.beq (IC.getD 12 0) 375 && Nat.beq IT.length 375 &&
    Nat.beq IX.length 375 && Nat.beq (IC.getD 6 0) 195 && Nat.beq IC.length 13) = true := by
  decide +kernel

@[expose] def gens3 : List Tab := nGensTab ++ [betaTab]

@[expose] noncomputable def classTreeOK : Bool :=
  (PR.zip CL).all fun e => Nat.beq (CL.getD e.1.1 5) e.2

theorem ch24790tree : (conjTreeK gens3 GI IT PR PR IT && Nat.beq PR.length 375 &&
    Nat.beq CL.length 375 && classTreeOK) = true := by
  decide +kernel

theorem ch24790norm : (decide (tmul (tmul betaTab (nGensTab.getD 0 idTab)) betaTab ∈ T) &&
    decide (tmul (tmul betaTab (nGensTab.getD 1 idTab)) betaTab ∈ T) &&
    tmul betaTab betaTab == idTab && (nGensTab.all fun g => normOK (elemTabs 1) g)) = true := by
  decide +kernel

@[expose] def centOf (c : Nat) : Nat := ((invClassData.getD c (0, 0, false, false)).1)

@[expose] def repIdx : List Nat := [0, 12, 195, 196, 197]

theorem ch24790repIdx : ((PR.zip (List.range 375)).all fun e =>
    !(Nat.beq e.1.2.1 3) || repIdx.contains e.2) = true := by
  decide +kernel

@[expose] noncomputable def repOK (j : Nat) : Bool :=
  Nat.beq (centN (T ++ U) (IT.getD j idTab)) (centOf (CL.getD j 5))

theorem ch24790rep0 : repOK 0 = true := by decide +kernel
theorem ch24790rep12 : repOK 12 = true := by decide +kernel
theorem ch24790rep195 : repOK 195 = true := by decide +kernel
theorem ch24790rep196 : repOK 196 = true := by decide +kernel
theorem ch24790rep197 : repOK 197 = true := by decide +kernel

@[expose] noncomputable def LP : Nat := packTs (T ++ U)

@[expose] noncomputable def dataOK : Bool :=
  (IT.zip (IX.zip CL)).all fun e =>
    let d := invClassData.getD e.2.2 (0, 0, false, false)
    Nat.beq (packT e.1) (tabAt LP e.2.1) && Nat.blt e.2.1 11520 &&
      Nat.blt e.2.1 5760 == d.2.2.1 && Nat.beq (fixF e.1) d.2.1 &&
      decide (e.1 ∈ f1Tabs) == d.2.2.2

theorem ch24790data : dataOK = true := by decide +kernel

end CertificateChecks.KernelM22Out24790
