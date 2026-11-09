module

public import CFSG.Certificates.Kernel.LocalQTLatMSound
public import CFSG.Certificates.Kernel.LocalQTGrpCOfSound
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.L246C127Even8Inputs
import CFSG.Certificates.Kernel.Common.Harness
public import CFSG.Certificates.Kernel.LocalQTListLemmas
public import CFSG.LocalAnalysis.ComponentInitial.PGroupRankOneClassification
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.A312ListAlt7Base
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.A312ListBender
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.A5.G3LatSixCheck
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.L246C127EvenBundle
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.L246C127EvenCT
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X35Basic
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
set_option maxHeartbeats 0
set_option Elab.async false

public section

namespace CFSG.KD.LQT.C4071

open CFSG.KC.LQT.L CFSG.KC.LQT.S CFSG.QuasithinUnique.L246C127.Even8

@[expose] def C : List Lvl :=
  [(7, [7722896418, 42082634816, 76442373121, 104394297346, 139627533315, 175088310276, 210556197893, 247132686368], [0, 1, 2, 3, 4, 5, 6, 7], 8),
    (5, [245891138662, 245924628582, 245958280198, 245987607686, 246024307718, 247132686368, 240723789861, 0], [0, 1, 2, 3, 4, 5, 6, 0], 7),
    (6, [240689153158, 241762830470, 242833523846, 243911427078, 244980974694, 0, 247132686368, 0], [0, 1, 2, 3, 4, 0, 5, 0], 6),
    (4, [247128524835, 247129571395, 247130623008, 247131539492, 247132686368, 0, 0, 0], [0, 1, 2, 3, 4, 0, 0, 0], 5),
    (3, [247132589090, 247132621888, 247132651555, 247132686368, 0, 0, 0, 0], [0, 1, 2, 3, 0, 0, 0, 0], 4),
    (0, [247132686368, 247132684353, 247132685314, 0, 0, 0, 0, 0], [0, 1, 2, 0, 0, 0, 0, 0], 3)]

@[expose] def MW : List (List (List Nat)) :=
  [[[0, 0, 1], [1], [0, 1], [1, 0, 1], [1, 1, 0, 1], [1, 1, 1, 0, 1], [1, 1, 1, 1, 0, 1], []],
    [[1, 1, 0, 1, 1, 1, 0, 1], [0, 1, 1, 0, 1, 1, 1, 0, 1], [1, 0, 1, 0, 1, 1, 1, 0, 1], [1, 1, 0, 0, 1, 1, 1, 0, 1], [1, 1, 1, 1, 1, 0, 1], [], [1, 1, 1, 1, 0, 1, 1, 1], []],
    [[1, 1, 1, 0, 1, 1, 0, 1], [0, 1, 1, 1, 0, 1, 1, 0, 1], [1, 0, 1, 1, 0, 1, 1, 0, 1], [1, 1, 0, 1, 0, 1, 1, 0, 1], [1, 1, 0, 0, 1, 0, 1, 1, 0, 1], [], [], []],
    [[1, 1, 0, 1, 1, 1, 1, 1], [0, 1, 1, 0, 1, 1, 1, 1, 1], [1, 0, 1, 0, 1, 1, 1, 1, 1], [1, 1, 0, 0, 1, 1, 1, 1, 1], [], [], [], []],
    [[1, 0, 1, 1, 1, 1, 1, 1], [0, 1, 0, 1, 1, 1, 1, 1, 1], [1, 0, 0, 1, 1, 1, 1, 1, 1], [], [], [], [], []],
    [[], [0], [0, 0], [], [], [], [], []]]

@[expose] def mem0 : Mem :=
  (((cert.tGens :: cert.lat).getD 0 []).map code, false, [])
@[expose] def mem1 : Mem :=
  (((cert.tGens :: cert.lat).getD 1 []).map code, false, [])
@[expose] def mem2 : Mem :=
  (((cert.tGens :: cert.lat).getD 2 []).map code, false, [])
@[expose] def mem3 : Mem :=
  (((cert.tGens :: cert.lat).getD 3 []).map code, false, [])
@[expose] def mem4 : Mem :=
  (((cert.tGens :: cert.lat).getD 4 []).map code, false, [])
@[expose] def mem5 : Mem :=
  (((cert.tGens :: cert.lat).getD 5 []).map code, false, [])
@[expose] def mem6 : Mem :=
  (((cert.tGens :: cert.lat).getD 6 []).map code, false, [])
@[expose] def mem7 : Mem :=
  (((cert.tGens :: cert.lat).getD 7 []).map code, true, [[[0, 0, 1, 3, 1, 3, 0, 3, 0], [0, 2, 0, 3, 1, 3, 0, 3, 0, 3, 0], [0, 2, 0, 3, 2, 3, 0, 1, 2], [2, 1, 3, 0, 1, 3, 0, 2, 3, 1], [0, 0, 2, 3, 2, 3, 2, 2, 3, 0], [0, 0, 3, 2, 3, 1, 2, 1, 0], [0, 3, 1, 2, 1, 0, 3, 2, 2], []],
    [[0, 1, 0, 3, 2, 2, 3, 2, 3, 2], [0, 0, 3, 1, 2, 1, 3, 2, 2, 3], [0, 2, 3, 1, 3, 2, 2, 3, 0, 0], [0, 3, 2, 3, 0, 0, 1, 3, 2, 3], [0, 3, 0, 3, 2, 0, 3, 0, 0, 1], [], [2, 1, 0, 3, 1, 3, 0, 2], []],
    [[2, 3, 2, 3, 0, 3, 0, 3, 0], [0, 3, 0, 1, 0, 3, 2, 2, 2, 3], [0, 3, 2, 3, 0, 3, 1], [0, 3, 0, 1, 3, 0, 0, 2, 0], [3, 1, 2, 3, 2, 3, 0, 3, 1], [], [], []],
    [[2, 2, 0, 3, 1, 3, 0, 1], [1, 0, 2, 1, 3], [0, 0, 0, 1, 2, 3], [0, 1, 2, 1, 0, 3, 0, 1, 3], [], [], [], []],
    [[2, 1, 3, 1, 3, 0, 1, 3], [2, 0, 3, 2, 3, 1, 3, 1, 2], [0, 3, 1, 3, 2, 0, 3, 2], [], [], [], [], []],
    [[], [1, 3, 2, 3, 1, 3, 0], [0, 3, 1, 3, 2, 0, 3, 1, 2], [], [], [], [], []]])

@[expose] def ms : List Mem := [mem0, mem1, mem2, mem3, mem4, mem5, mem6, mem7]

theorem p0 : memsOK (cert.tGens.map code) (cert.lat.map (List.map code)) ms = true := by
  quickRfl
theorem p1a : chainOK 8 C = true := by quickRfl
theorem p1bg : CFSG.KC.LQT.P.allL (cert.mGens.map code) (inC 8 C (chainF C)) = true := by quickRfl
theorem p1bw : wordsC 8 C (cert.mGens.map code) MW cert.depth = true := by quickRfl
theorem inj : chainInj 8 C = true := by quickRfl
theorem p1bS : CFSG.KC.LQT.PH.grpS 8 C (chainF C) (cert.mGens.map code) MW cert.depth = true := by
  quickRfl
theorem p1b : grpC 8 C (chainF C) (cert.mGens.map code) MW cert.depth = true :=
  CFSG.KC.LQT.CM.grpC_of_sims (by decide) p1a inj cert.mGens p1bS
theorem p1bM : grpM 8 C (chainF C) cert.depth (cert.mGens.map code) MW = true :=
  grpM_of_grpC p1b
@[expose] noncomputable def hmF (p : Mem × SetX) : Bool :=
  CFSG.KC.Ord.andB (closedX 8 C (chainF C) cert.depth p.1 p.2)
    (CFSG.KC.Ord.orB (Nat.beq (sizeX (chainF C) p.2) cert.msize)
      (anyA (cts.map fun ct => (ct.depth, ct.hGens.map code, ct.nGens.map code, ct.expo))
        fun c => CFSG.KC.Ord.andB (eqL c.2.1 p.1.1) (ctC 8 C (chainF C) c.1 c.2.1 c.2.2.1 c.2.2.2)))
theorem memChecks : ((hmF (mem0, mkX 8 C (chainF C) cert.depth mem0) &&
    (hmF (mem1, mkX 8 C (chainF C) cert.depth mem1) &&
    (hmF (mem2, mkX 8 C (chainF C) cert.depth mem2) &&
    (hmF (mem3, mkX 8 C (chainF C) cert.depth mem3) &&
    (hmF (mem4, mkX 8 C (chainF C) cert.depth mem4) &&
    (hmF (mem5, mkX 8 C (chainF C) cert.depth mem5) &&
    hmF (mem6, mkX 8 C (chainF C) cert.depth mem6))))))) &&
    (repsC 8 C (chainF C) (cert.tGens.map code) (membersX 8 C (chainF C) cert.depth ms)
      (repsCode cert) &&
    (joinsC 8 C (chainF C) (membersX 8 C (chainF C) cert.depth ms) cert.joins &&
    sizesC (chainF C) (membersX 8 C (chainF C) cert.depth ms) cert.sizes cert.msize))) = true := by
  quickRfl
theorem memH : (hmF (mem0, mkX 8 C (chainF C) cert.depth mem0) &&
    (hmF (mem1, mkX 8 C (chainF C) cert.depth mem1) &&
    (hmF (mem2, mkX 8 C (chainF C) cert.depth mem2) &&
    (hmF (mem3, mkX 8 C (chainF C) cert.depth mem3) &&
    (hmF (mem4, mkX 8 C (chainF C) cert.depth mem4) &&
    (hmF (mem5, mkX 8 C (chainF C) cert.depth mem5) &&
    hmF (mem6, mkX 8 C (chainF C) cert.depth mem6))))))) = true :=
  (Bool.and_eq_true_iff.mp memChecks).1
theorem memP : (repsC 8 C (chainF C) (cert.tGens.map code)
      (membersX 8 C (chainF C) cert.depth ms) (repsCode cert) &&
    (joinsC 8 C (chainF C) (membersX 8 C (chainF C) cert.depth ms) cert.joins &&
    sizesC (chainF C) (membersX 8 C (chainF C) cert.depth ms) cert.sizes cert.msize)) = true :=
  (Bool.and_eq_true_iff.mp memChecks).2
theorem memH3 : (hmF (mem3, mkX 8 C (chainF C) cert.depth mem3) &&
    (hmF (mem4, mkX 8 C (chainF C) cert.depth mem4) &&
    (hmF (mem5, mkX 8 C (chainF C) cert.depth mem5) &&
    hmF (mem6, mkX 8 C (chainF C) cert.depth mem6)))) = true :=
  (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp memH).2).2).2
theorem hmc0 : hmF (mem0, mkX 8 C (chainF C) cert.depth mem0) = true :=
  (Bool.and_eq_true_iff.mp memH).1
theorem hmc1 : hmF (mem1, mkX 8 C (chainF C) cert.depth mem1) = true :=
  (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp memH).2).1
theorem hmc2 : hmF (mem2, mkX 8 C (chainF C) cert.depth mem2) = true :=
  (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp memH).2).2).1
theorem hmc3 : hmF (mem3, mkX 8 C (chainF C) cert.depth mem3) = true :=
  (Bool.and_eq_true_iff.mp memH3).1
theorem hmc4 : hmF (mem4, mkX 8 C (chainF C) cert.depth mem4) = true :=
  (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp memH3).2).1
theorem hmc5 : hmF (mem5, mkX 8 C (chainF C) cert.depth mem5) = true :=
  (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp memH3).2).2).1
theorem hmc6 : hmF (mem6, mkX 8 C (chainF C) cert.depth mem6) = true :=
  (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp memH3).2).2).2
theorem q0 : closedX 8 C (chainF C) cert.depth mem0
    (mkX 8 C (chainF C) cert.depth mem0) = true :=
  (Bool.and_eq_true_iff.mp ((CFSG.KC.LQT.L.andB_eq _ _).symm.trans hmc0)).1
theorem q1 : closedX 8 C (chainF C) cert.depth mem1
    (mkX 8 C (chainF C) cert.depth mem1) = true :=
  (Bool.and_eq_true_iff.mp ((CFSG.KC.LQT.L.andB_eq _ _).symm.trans hmc1)).1
theorem q2 : closedX 8 C (chainF C) cert.depth mem2
    (mkX 8 C (chainF C) cert.depth mem2) = true :=
  (Bool.and_eq_true_iff.mp ((CFSG.KC.LQT.L.andB_eq _ _).symm.trans hmc2)).1
theorem q3 : closedX 8 C (chainF C) cert.depth mem3
    (mkX 8 C (chainF C) cert.depth mem3) = true :=
  (Bool.and_eq_true_iff.mp ((CFSG.KC.LQT.L.andB_eq _ _).symm.trans hmc3)).1
theorem q4 : closedX 8 C (chainF C) cert.depth mem4
    (mkX 8 C (chainF C) cert.depth mem4) = true :=
  (Bool.and_eq_true_iff.mp ((CFSG.KC.LQT.L.andB_eq _ _).symm.trans hmc4)).1
theorem q5 : closedX 8 C (chainF C) cert.depth mem5
    (mkX 8 C (chainF C) cert.depth mem5) = true :=
  (Bool.and_eq_true_iff.mp ((CFSG.KC.LQT.L.andB_eq _ _).symm.trans hmc5)).1
theorem q6 : closedX 8 C (chainF C) cert.depth mem6
    (mkX 8 C (chainF C) cert.depth mem6) = true :=
  (Bool.and_eq_true_iff.mp ((CFSG.KC.LQT.L.andB_eq _ _).symm.trans hmc6)).1
theorem m7g : CFSG.KC.LQT.P.allL mem7.1 (inC 8 C (chainF C)) = true := by quickRfl
theorem m7w : wordsC 8 C mem7.1 mem7.2.2 cert.depth = true := by quickRfl
theorem m7 : grpC 8 C (chainF C) mem7.1 mem7.2.2 cert.depth = true :=
  CFSG.KC.LQT.CM.grpC_of_grpC (by decide) p1a inj cert.mGens
    ((cert.tGens :: cert.lat).getD 7 []) p1b m7g m7w
theorem q7 : closedX 8 C (chainF C) cert.depth mem7
    (mkX 8 C (chainF C) cert.depth mem7) = true := m7
theorem s7 : CFSG.KC.Ord.orB (Nat.beq (sizeX (chainF C) (mkX 8 C (chainF C) cert.depth mem7))
    cert.msize) (anyA (cts.map fun ct => (ct.depth, ct.hGens.map code, ct.nGens.map code, ct.expo))
      fun c => CFSG.KC.Ord.andB (eqL c.2.1 mem7.1) (ctC 8 C (chainF C) c.1 c.2.1 c.2.2.1 c.2.2.2))
    = true := by
  quickRfl
theorem hmc7 : hmF (mem7, mkX 8 C (chainF C) cert.depth mem7) = true :=
  (CFSG.KC.LQT.L.andB_eq _ _).trans (Bool.and_eq_true_iff.mpr ⟨q7, s7⟩)
theorem p1c : allA (membersX 8 C (chainF C) cert.depth ms) (fun p =>
    closedX 8 C (chainF C) cert.depth p.1 p.2) = true :=
  allA_cons q0 (allA_cons q1 (allA_cons q2 (allA_cons q3 (allA_cons q4 (allA_cons q5 (allA_cons q6 (allA_cons q7 rfl)))))))
theorem p1 : closedOKC 8 C (chainF C) cert.depth (cert.mGens.map code) MW ms = true := by
  rw [closedOKC, p1a, p1bM, p1c]
  rfl
theorem p2 : coverC 8 C (chainF C) (bfsM 8 C (chainF C) (cert.tGens.map code) cert.depth)
    (repsCode cert) = true := by quickRfl
theorem p3 : repsC 8 C (chainF C) (cert.tGens.map code) (membersX 8 C (chainF C) cert.depth ms)
    (repsCode cert) = true :=
  (Bool.and_eq_true_iff.mp memP).1
theorem p4 : joinsC 8 C (chainF C) (membersX 8 C (chainF C) cert.depth ms) cert.joins = true :=
  (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp memP).2).1
theorem p5 : sizesC (chainF C) (membersX 8 C (chainF C) cert.depth ms) cert.sizes cert.msize =
    true :=
  (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp memP).2).2
theorem p6 : tleC 8 C (chainF C) (cert.tGens.map code) = true := by quickRfl
theorem hl : latC 8 C cert.depth (cert.mGens.map code) MW (cert.tGens.map code)
    (cert.lat.map (List.map code)) ms (repsCode cert) cert.joins cert.sizes cert.msize = true :=
  latC_intro p0 p1 p2 p3 p4 p5 p6
theorem hmA : allA (membersX 8 C (chainF C) cert.depth ms) (fun p =>
    CFSG.KC.Ord.andB (closedX 8 C (chainF C) cert.depth p.1 p.2)
    (CFSG.KC.Ord.orB (Nat.beq (sizeX (chainF C) p.2) cert.msize)
      (anyA (cts.map fun ct => (ct.depth, ct.hGens.map code, ct.nGens.map code, ct.expo))
        fun c => CFSG.KC.Ord.andB (eqL c.2.1 p.1.1) (ctC 8 C (chainF C) c.1 c.2.1 c.2.2.1 c.2.2.2))))
    = true :=
  allA_cons hmc0 (allA_cons hmc1 (allA_cons hmc2 (allA_cons hmc3 (allA_cons hmc4
    (allA_cons hmc5 (allA_cons hmc6 (allA_cons hmc7 rfl)))))))
theorem sm : CFSG.KC.LQT.P.allL (mGens.map code) (CFSG.KC.LQT.P.even 8) = true := by quickRfl
theorem st : CFSG.KC.LQT.P.allL (tGens.map code) (CFSG.KC.LQT.P.even 8) = true := by quickRfl
theorem hm : memberC 8 C cert.depth (cert.tGens.map code) (cert.lat.map (List.map code)) ms
    cert.msize (cts.map fun ct => (ct.depth, ct.hGens.map code, ct.nGens.map code, ct.expo)) =
    true := by
  rw [memberC, p0, p1a, hmA]
  rfl

end CFSG.KD.LQT.C4071

end
