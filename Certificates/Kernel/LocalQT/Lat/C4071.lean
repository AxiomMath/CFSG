module

public import CFSG.Certificates.Kernel.LocalQTLatMSound
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
theorem p1bc0 : chainChunk 8 C
    (fun s => CFSG.KC.LQT.P.allL (cert.mGens.map code) fun g => inC 8 C (chainF C) (CFSG.KC.LQT.P.mul 8 s g)) 0 = true := by quickRfl
theorem p1bc1 : chainChunk 8 C
    (fun s => CFSG.KC.LQT.P.allL (cert.mGens.map code) fun g => inC 8 C (chainF C) (CFSG.KC.LQT.P.mul 8 s g)) 1 = true := by quickRfl
theorem p1bc2 : chainChunk 8 C
    (fun s => CFSG.KC.LQT.P.allL (cert.mGens.map code) fun g => inC 8 C (chainF C) (CFSG.KC.LQT.P.mul 8 s g)) 2 = true := by quickRfl
theorem p1bc3 : chainChunk 8 C
    (fun s => CFSG.KC.LQT.P.allL (cert.mGens.map code) fun g => inC 8 C (chainF C) (CFSG.KC.LQT.P.mul 8 s g)) 3 = true := by quickRfl
theorem p1bc4 : chainChunk 8 C
    (fun s => CFSG.KC.LQT.P.allL (cert.mGens.map code) fun g => inC 8 C (chainF C) (CFSG.KC.LQT.P.mul 8 s g)) 4 = true := by quickRfl
theorem p1bc5 : chainChunk 8 C
    (fun s => CFSG.KC.LQT.P.allL (cert.mGens.map code) fun g => inC 8 C (chainF C) (CFSG.KC.LQT.P.mul 8 s g)) 5 = true := by quickRfl
theorem p1bc6 : chainChunk 8 C
    (fun s => CFSG.KC.LQT.P.allL (cert.mGens.map code) fun g => inC 8 C (chainF C) (CFSG.KC.LQT.P.mul 8 s g)) 6 = true := by quickRfl
theorem p1bc7 : chainChunk 8 C
    (fun s => CFSG.KC.LQT.P.allL (cert.mGens.map code) fun g => inC 8 C (chainF C) (CFSG.KC.LQT.P.mul 8 s g)) 7 = true := by quickRfl
theorem p1b : grpC 8 C (chainF C) (cert.mGens.map code) MW cert.depth = true :=
  grpC_intro (lv := C.head!) (C := C.tail) p1bg p1bw fun j hj => match j, hj with
    | 0, _ => p1bc0
    | 1, _ => p1bc1
    | 2, _ => p1bc2
    | 3, _ => p1bc3
    | 4, _ => p1bc4
    | 5, _ => p1bc5
    | 6, _ => p1bc6
    | 7, _ => p1bc7
    | _k + 8, h => absurd h (Nat.not_lt.2 (Nat.le_add_left _ _))
theorem p1bM : grpM 8 C (chainF C) cert.depth (cert.mGens.map code) MW = true :=
  grpM_of_grpC p1b
theorem q0 : closedX 8 C (chainF C) cert.depth mem0
    (mkX 8 C (chainF C) cert.depth mem0) = true := by quickRfl
theorem q1 : closedX 8 C (chainF C) cert.depth mem1
    (mkX 8 C (chainF C) cert.depth mem1) = true := by quickRfl
theorem q2 : closedX 8 C (chainF C) cert.depth mem2
    (mkX 8 C (chainF C) cert.depth mem2) = true := by quickRfl
theorem q3 : closedX 8 C (chainF C) cert.depth mem3
    (mkX 8 C (chainF C) cert.depth mem3) = true := by quickRfl
theorem q4 : closedX 8 C (chainF C) cert.depth mem4
    (mkX 8 C (chainF C) cert.depth mem4) = true := by quickRfl
theorem q5 : closedX 8 C (chainF C) cert.depth mem5
    (mkX 8 C (chainF C) cert.depth mem5) = true := by quickRfl
theorem q6 : closedX 8 C (chainF C) cert.depth mem6
    (mkX 8 C (chainF C) cert.depth mem6) = true := by quickRfl
theorem m7g : CFSG.KC.LQT.P.allL mem7.1 (inC 8 C (chainF C)) = true := by quickRfl
theorem m7w : wordsC 8 C mem7.1 mem7.2.2 cert.depth = true := by quickRfl
theorem m7c0 : chainChunk 8 C
    (fun s => CFSG.KC.LQT.P.allL mem7.1 fun g => inC 8 C (chainF C) (CFSG.KC.LQT.P.mul 8 s g)) 0 = true := by quickRfl
theorem m7c1 : chainChunk 8 C
    (fun s => CFSG.KC.LQT.P.allL mem7.1 fun g => inC 8 C (chainF C) (CFSG.KC.LQT.P.mul 8 s g)) 1 = true := by quickRfl
theorem m7c2 : chainChunk 8 C
    (fun s => CFSG.KC.LQT.P.allL mem7.1 fun g => inC 8 C (chainF C) (CFSG.KC.LQT.P.mul 8 s g)) 2 = true := by quickRfl
theorem m7c3 : chainChunk 8 C
    (fun s => CFSG.KC.LQT.P.allL mem7.1 fun g => inC 8 C (chainF C) (CFSG.KC.LQT.P.mul 8 s g)) 3 = true := by quickRfl
theorem m7c4 : chainChunk 8 C
    (fun s => CFSG.KC.LQT.P.allL mem7.1 fun g => inC 8 C (chainF C) (CFSG.KC.LQT.P.mul 8 s g)) 4 = true := by quickRfl
theorem m7c5 : chainChunk 8 C
    (fun s => CFSG.KC.LQT.P.allL mem7.1 fun g => inC 8 C (chainF C) (CFSG.KC.LQT.P.mul 8 s g)) 5 = true := by quickRfl
theorem m7c6 : chainChunk 8 C
    (fun s => CFSG.KC.LQT.P.allL mem7.1 fun g => inC 8 C (chainF C) (CFSG.KC.LQT.P.mul 8 s g)) 6 = true := by quickRfl
theorem m7c7 : chainChunk 8 C
    (fun s => CFSG.KC.LQT.P.allL mem7.1 fun g => inC 8 C (chainF C) (CFSG.KC.LQT.P.mul 8 s g)) 7 = true := by quickRfl
theorem m7 : grpC 8 C (chainF C) mem7.1 mem7.2.2 cert.depth = true :=
  grpC_intro (lv := C.head!) (C := C.tail) m7g m7w fun j hj => match j, hj with
    | 0, _ => m7c0
    | 1, _ => m7c1
    | 2, _ => m7c2
    | 3, _ => m7c3
    | 4, _ => m7c4
    | 5, _ => m7c5
    | 6, _ => m7c6
    | 7, _ => m7c7
    | _k + 8, h => absurd h (Nat.not_lt.2 (Nat.le_add_left _ _))
theorem q7 : closedX 8 C (chainF C) cert.depth mem7
    (mkX 8 C (chainF C) cert.depth mem7) = true := m7
theorem p1c : allA (membersX 8 C (chainF C) cert.depth ms) (fun p =>
    closedX 8 C (chainF C) cert.depth p.1 p.2) = true :=
  allA_cons q0 (allA_cons q1 (allA_cons q2 (allA_cons q3 (allA_cons q4 (allA_cons q5 (allA_cons q6 (allA_cons q7 rfl)))))))
theorem p1 : closedOKC 8 C (chainF C) cert.depth (cert.mGens.map code) MW ms = true := by
  rw [closedOKC, p1a, p1bM, p1c]
  rfl
theorem p2 : coverC 8 C (chainF C) (bfsM 8 C (chainF C) (cert.tGens.map code) cert.depth)
    (repsCode cert) = true := by quickRfl
theorem p3 : repsC 8 C (chainF C) (cert.tGens.map code) (membersX 8 C (chainF C) cert.depth ms)
    (repsCode cert) = true := by quickRfl
theorem p4 : joinsC 8 C (chainF C) (membersX 8 C (chainF C) cert.depth ms) cert.joins = true := by
  quickRfl
theorem p5 : sizesC (chainF C) (membersX 8 C (chainF C) cert.depth ms) cert.sizes cert.msize =
    true := by quickRfl
theorem p6 : tleC 8 C (chainF C) (cert.tGens.map code) = true := by quickRfl
theorem hl : latC 8 C cert.depth (cert.mGens.map code) MW (cert.tGens.map code)
    (cert.lat.map (List.map code)) ms (repsCode cert) cert.joins cert.sizes cert.msize = true :=
  latC_intro p0 p1 p2 p3 p4 p5 p6
theorem sm : CFSG.KC.LQT.P.allL (mGens.map code) (CFSG.KC.LQT.P.even 8) = true := by quickRfl
theorem st : CFSG.KC.LQT.P.allL (tGens.map code) (CFSG.KC.LQT.P.even 8) = true := by quickRfl
theorem hm : memberC 8 C cert.depth (cert.tGens.map code) (cert.lat.map (List.map code)) ms
    cert.msize (cts.map fun ct => (ct.depth, ct.hGens.map code, ct.nGens.map code, ct.expo)) =
    true := by
  quickRfl
theorem inj : chainInj 8 C = true := by quickRfl

end CFSG.KD.LQT.C4071

end
