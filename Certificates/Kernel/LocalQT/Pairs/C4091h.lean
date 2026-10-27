module

public import CFSG.Certificates.Kernel.LocalQTPermWSound
public import Certificates.Kernel.LocalQT.Pairs.D4091
import CFSG.Certificates.Kernel.Common.Harness
public import CFSG.LocalAnalysis.ComponentInitial.PGroupRankOneClassification
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.A312ListAlt7Base
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.A312ListPermIso
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.L246C127EvenBundle
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.L246C127EvenCT
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X35Basic
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_2
public import CFSG.Monster.Code.Weights
public import CFSG.Quasithin.Background.A3Structure318Red
public import CFSG.Quasithin.Background.A3Structure36A
public import CFSG.Quasithin.Background.A3Structure36BAction
public import CFSG.Quasithin.Background.A3Structure36BBase
public import CFSG.Quasithin.Background.A3Structure36BCase3Base
public import CFSG.Quasithin.Background.A3Structure36BCasesBase
public import CFSG.Quasithin.Background.A3Structure36BCommonBase
public import CFSG.Quasithin.Background.A3Structure36BFrattini
public import CFSG.Quasithin.Background.A3Structure36BHeisBase
public import CFSG.Quasithin.Background.A3Structure36BHomocyclic
public import CFSG.Quasithin.Background.A3Structure36BPrimeDataBase
public import CFSG.Quasithin.Background.A3Structure36BStarBase
public import CFSG.Quasithin.Background.A3Structure36Base
public import CFSG.Quasithin.Background.A3Structure38Part3
public import CFSG.Quasithin.Background.B1MoreElevenE
public import CFSG.Quasithin.Background.B1MoreNineG
public import CFSG.Quasithin.Background.C2Basic
public import CFSG.Quasithin.Background.E1
public import CFSG.Quasithin.Background.E1Sec4
public import CFSG.Quasithin.Background.E1Sec5
public import CFSG.Quasithin.Background.E1Sec8
public import CFSG.Quasithin.Background.E1Solv
public import CFSG.Quasithin.Background.E1Twelve
public import CFSG.Quasithin.Background.E3Cent

set_option maxRecDepth 100000
set_option Elab.async false

public section

namespace CFSG.KD.LQT.C4091

open CFSG.KC.LQT.PW CFSG.KC.Ord CFSG.KD.LQT.J2T CFSG.ComponentClassification.J2Cover
  CFSG.QuasithinUnique.Vol2Native.L239.J2Pairs

noncomputable abbrev GAB : List Nat :=
  [arrCodeW 9 (autStrong[0]!).toList, arrCodeW 9 (autStrong[1]!).toList]
noncomputable abbrev S0G : List Nat := List.map (evalZW 315 9 GAB) s0Words
noncomputable abbrev t1C : Nat := evalZW 315 9 GAB t1Word
noncomputable abbrev t2C : Nat := evalZW 315 9 GAB t2Word
noncomputable abbrev K1G : List Nat := List.append S0G [t1C]
noncomputable abbrev K2G : List Nat := List.append S0G [t2C]
noncomputable abbrev A2G : List Nat := List.map (evalZW 315 9 S0G) a2Words
noncomputable abbrev Q1G : List Nat := List.map (evalZW 315 9 S0G) q1Words

noncomputable abbrev S0E : List Nat := grpE S0G S0P
noncomputable abbrev A2E : List Nat := grpE A2G A2P
noncomputable abbrev Q1E : List Nat := grpE Q1G Q1P
noncomputable abbrev K1E : List Nat := grpE K1G K1P
noncomputable abbrev K2E : List Nat := grpE K2G K2P

noncomputable abbrev pA1 : Nat → Bool := fun c =>
  CFSG.KC.LQT.P.allL S0G fun s => Nat.beq (mulW 315 9 s c) (mulW 315 9 c s)
noncomputable abbrev A1E : List Nat := CFSG.KC.LQT.S.filtL S0E pA1
noncomputable abbrev pZ2 : Nat → Bool := fun y =>
  CFSG.KC.LQT.P.allL S0G fun s => CFSG.KC.LQT.S.memL
    (mulW 315 9 (mulW 315 9 (mulW 315 9 y s) (invW 315 9 y)) (invW 315 9 s)) A1E
noncomputable abbrev Z2E : List Nat := CFSG.KC.LQT.S.filtL S0E pZ2
noncomputable abbrev pA2 : Nat → Bool := fun x =>
  CFSG.KC.LQT.P.allL Z2E fun y => Nat.beq (mulW 315 9 y x) (mulW 315 9 x y)
noncomputable abbrev A2X' : List Nat := CFSG.KC.LQT.S.filtL S0E pA2
noncomputable abbrev F1M : Nat := fixMaskW 315 9 A1E
noncomputable abbrev F2M : Nat := fixMaskW 315 9 A2X'

theorem gS1 : CFSG.KC.LQT.T2.monoK (CFSG.KC.LQT.Syl.pairUpK S0P) = true := by quickRfl
theorem gS2 : CFSG.KC.LQT.T2.sincK (CFSG.KC.LQT.Syl.sortN S0E) = true := by quickRfl
theorem gS3 : closedE S0G S0E = true := by quickRfl
theorem gS4 : depthOK S0G S0P 40 = true := by quickRfl
theorem gS5 : CFSG.KC.LQT.T2.sincK (CFSG.KC.LQT.Syl.sortN (List.map (hkW 315 9) S0E)) = true := by
  quickRfl
theorem gA1 : CFSG.KC.LQT.T2.monoK (CFSG.KC.LQT.Syl.pairUpK A2P) = true := by quickRfl
theorem gA2 : CFSG.KC.LQT.T2.sincK (CFSG.KC.LQT.Syl.sortN A2E) = true := by quickRfl
theorem gA3 : closedE A2G A2E = true := by quickRfl
theorem gA4 : depthOK A2G A2P 40 = true := by quickRfl
theorem gA5 : CFSG.KC.LQT.T2.sincK (CFSG.KC.LQT.Syl.sortN (List.map (hkW 315 9) A2E)) = true := by
  quickRfl
theorem gQ1 : CFSG.KC.LQT.T2.monoK (CFSG.KC.LQT.Syl.pairUpK Q1P) = true := by quickRfl
theorem gQ2 : CFSG.KC.LQT.T2.sincK (CFSG.KC.LQT.Syl.sortN Q1E) = true := by quickRfl
theorem gQ3 : closedE Q1G Q1E = true := by quickRfl
theorem gQ4 : depthOK Q1G Q1P 40 = true := by quickRfl
theorem gQ5 : CFSG.KC.LQT.T2.sincK (CFSG.KC.LQT.Syl.sortN (List.map (hkW 315 9) Q1E)) = true := by
  quickRfl

theorem lS : Nat.beq (CFSG.KC.LQT.S.lenL S0E) 128 = true := by quickRfl
theorem lA : CFSG.KC.LQT.S.allBs [Nat.beq (CFSG.KC.LQT.S.lenL A1E) 2,
    Nat.beq (CFSG.KC.LQT.S.lenL Z2E) 4, Nat.beq (CFSG.KC.LQT.S.lenL A2X') 64] = true := by quickRfl
theorem lQ : Nat.beq (CFSG.KC.LQT.S.lenL Q1E) 32 = true := by quickRfl
theorem kSe : CFSG.KC.LQT.P.allL S0E (fun x => Nat.beq (sqW 315 9 x 3) (oneW 315 9)) = true := by
  quickRfl
theorem kA2g : CFSG.KC.LQT.P.allL A2G (fun a => CFSG.KC.LQT.S.memL a A2X') = true := by quickRfl
theorem kA2c : CFSG.KC.LQT.P.allL A2X' (fun a => CFSG.KC.LQT.S.memL a A2E) = true := by quickRfl

noncomputable abbrev ord3 : Nat → Bool := fun x =>
  andB (notB (Nat.beq x (oneW 315 9))) (Nat.beq (mulW 315 9 (mulW 315 9 x x) x) (oneW 315 9))

noncomputable abbrev cmW : Nat → Nat → Nat := fun q b =>
  mulW 315 9 (conjW 315 9 q b) (invW 315 9 b)

noncomputable abbrev fK1 : Nat → Nat → Bool := fun x h =>
  CFSG.KC.LQT.S.allBs [
    CFSG.KC.LQT.P.impB (CFSG.KC.LQT.P.allL Q1G fun q => commW 315 9 x q) (CFSG.KC.LQT.S.memL x Q1E),
    CFSG.KC.LQT.P.impB (ord3 x)
      (CFSG.KC.LQT.P.letB (cmW (CFSG.KC.LQT.S.getK Q1E (Nat.div h 32)) x) fun cp =>
        CFSG.KC.LQT.P.letB (cmW (CFSG.KC.LQT.S.getK Q1E (Nat.mod h 32)) x) fun cq =>
          orB (notB (Nat.beq (mulW 315 9 cp cq) (mulW 315 9 cq cp)))
            (notB (Nat.beq (mulW 315 9 cp cp) (oneW 315 9))))]

noncomputable abbrev fK2 : Nat → Bool := fun x =>
  CFSG.KC.LQT.S.allBs [
    CFSG.KC.LQT.P.impB (CFSG.KC.LQT.P.allL A2G fun q => commW 315 9 x q)
      (CFSG.KC.LQT.S.memL x A2X'),
    CFSG.KC.LQT.P.impB (ord3 x) (CFSG.KC.LQT.PH.fiveK (fun q => encW 315 9 (cmW q x)) A2X')]

end CFSG.KD.LQT.C4091

end
