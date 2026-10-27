module

public import CFSG.Certificates.Kernel.LocalQTLatMSound
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.A312ListM11Inputs
import CFSG.Certificates.Kernel.Common.Harness
public import CFSG.Certificates.Kernel.LocalQTListLemmas
public import CFSG.LocalAnalysis.ComponentInitial.PGroupRankOneClassification
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.A312ListAlt7
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

namespace CFSG.KD.LQT.C4084

open CFSG.KC.LQT.L CFSG.KC.LQT.S CFSG.QuasithinUnique.Vol2Native.A312L.M11Lat

@[expose] def C : List Lvl :=
  [(7, [11576764645055619, 2392577305550115, 11581231272561927, 11580166027575458, 8060665812287778, 283847013240103, 9194330212368418, 11584701642934304, 3420860021279008, 2463220891754538, 3419829364326562], [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10], 11),
    (8, [11540718894094441, 2534624494556260, 4506042659838121, 5949700358603904, 1412013793319074, 10420315513559041, 4791915751183392, 0, 11584701642934304, 291612244677834, 9335095414657216], [0, 1, 2, 3, 4, 5, 6, 0, 7, 8, 9], 10),
    (5, [2612686593590563, 3562662520760614, 3703401126823108, 360885802700873, 11268036892888265, 11584701642934304, 2401579492812801, 0, 0, 2296021105577124, 4583014987208801], [0, 1, 2, 3, 4, 5, 6, 0, 0, 7, 8], 9),
    (6, [10282873430022467, 220144087640164, 1486782563617926, 4547824010330402, 6834809262638089, 0, 11584701642934304, 0, 0, 2366399372628170, 3386747243340865], [0, 1, 2, 3, 4, 0, 5, 0, 0, 6, 7], 8)]

@[expose] def MW : List (List (List Nat)) :=
  [[[1], [1, 0], [1, 1, 1], [1, 1], [1, 1, 0], [1, 1, 1, 0], [0, 1, 1, 0], [], [0], [0, 1, 0], [0, 1, 1]],
    [[1, 0, 1, 0, 1, 1, 0, 1, 0, 1], [1, 1, 0, 1, 1, 0, 1, 0, 1], [0, 1, 0, 1, 1, 0, 1, 0, 1, 0], [0, 1, 1, 1, 0, 1, 0, 1, 0], [1, 0, 1, 1, 0, 1], [1, 0, 1, 0, 1, 0, 1, 0, 1], [1, 1, 0, 1, 0, 1, 0, 1], [], [], [1, 1, 1, 0, 1], [0, 1, 1, 1, 0, 1, 1, 0, 1, 0]],
    [[1, 0, 1, 0, 1, 0, 1, 1, 1, 0, 1, 1, 1], [0, 1, 0, 1, 1, 1, 0, 1, 0, 1, 1, 1], [0, 1, 1, 0, 1, 0, 1, 1, 0, 1, 0, 1, 1, 1], [1, 1, 0, 1, 1, 0, 1, 1, 1, 0, 1, 1, 1], [0, 1, 0, 1, 1, 1, 0], [], [1, 0, 1, 1, 1], [], [], [1, 0, 1, 1, 1, 0, 1, 0, 1, 1, 1, 0], [0, 1, 1, 0, 1, 1, 0, 1, 1, 1, 0, 1, 1, 1, 0]],
    [[0, 1, 1, 0, 1, 1, 1, 0, 1, 1, 0], [1, 1, 0, 1, 0, 1, 1], [0, 1, 1, 0, 1, 0, 1, 1, 0], [1, 1, 0, 1, 1, 0, 1, 1], [0, 1, 1, 0, 1, 0, 1, 1, 0, 1, 1, 0, 1, 0, 1, 1], [], [], [], [], [1, 1, 0, 1, 1, 1, 0, 1, 1], [1, 1, 0, 1, 0, 1, 1, 0, 1, 1, 0, 1, 0, 1, 1, 0]]]

@[expose] def mem0 : Mem :=
  (((cert.tGens :: cert.lat).getD 0 []).map code, false, [])
@[expose] def mem1 : Mem :=
  (((cert.tGens :: cert.lat).getD 1 []).map code, false, [])
@[expose] def mem2 : Mem :=
  (((cert.tGens :: cert.lat).getD 2 []).map code, false, [])
@[expose] def mem3 : Mem :=
  (((cert.tGens :: cert.lat).getD 3 []).map code, true, [[[0, 0, 2, 0, 0, 1, 2, 0, 1, 2, 0], [2, 0, 2, 1, 2, 0, 1, 2, 0], [2, 0, 1, 0, 2, 0, 0, 1, 2, 0, 0, 1], [0, 0, 1, 0, 2, 0, 1], [1, 0, 2, 0, 1], [2, 1, 2, 0, 1, 2, 0, 0, 1, 2, 1, 2, 0], [0, 0, 1, 2, 0, 0, 2, 0, 0, 2, 1], [], [0, 1, 0, 2, 0, 2, 1, 0], [0, 2, 0, 0, 2, 0, 2, 1, 2, 0], [0, 0, 1, 0, 2, 0, 0, 0, 1]],
    [[2, 0, 1, 2, 0, 1, 0, 2, 1, 0, 1], [2, 0, 0, 1, 2, 1, 0, 2, 0], [0, 1, 2, 0, 1, 0, 2, 1, 0, 2, 1, 0], [2, 0, 0, 2, 1, 0], [0, 1, 2, 0, 1, 2, 0, 0, 2, 1, 0], [0, 2, 1, 0, 1], [1, 0, 1, 2, 0, 0, 2], [], [], [1, 2, 0, 1, 2, 1, 0, 2, 0, 1, 2], [1, 2, 0, 2, 0, 0, 1, 0, 2, 0, 0, 2]],
    [[2, 0, 1, 2, 0, 1], [1, 0, 2, 0, 0, 0, 1, 2, 0, 0, 1, 2], [0, 0, 2, 0, 0, 0, 1, 0, 2, 1], [1, 0, 2, 1, 0, 2, 0, 1, 0, 1], [1, 2, 1, 0, 2, 0, 0, 0, 1, 2, 1], [], [0, 2, 0, 0, 2, 0, 2, 0], [], [], [2, 0, 0, 1, 2, 1, 0, 2, 0, 0, 0, 1], [2, 0, 0, 1, 0, 2, 0, 0, 2, 0, 0]],
    [[2, 0, 0, 0, 1, 2, 0, 1, 2, 0, 0, 2], [2, 0, 0, 1, 2, 0, 1, 2, 0, 0, 0], [0, 2, 1, 0, 2, 1, 2, 0, 2], [1, 0, 2, 0, 0, 0, 1], [2, 0, 2, 1, 2, 0, 0, 2, 0, 0, 2], [], [], [], [], [0, 2, 0, 0, 1, 0, 2, 0, 0, 1, 2], [2, 0, 0, 1, 2, 0, 0, 2, 1, 2, 0, 2]]])
@[expose] def mem4 : Mem :=
  (((cert.tGens :: cert.lat).getD 4 []).map code, false, [])

@[expose] def ms : List Mem := [mem0, mem1, mem2, mem3, mem4]

theorem p0 : memsOK (cert.tGens.map code) (cert.lat.map (List.map code)) ms = true := by
  quickRfl
theorem p1a : chainOK 11 C = true := by quickRfl
theorem p1bg : CFSG.KC.LQT.P.allL (cert.mGens.map code) (inC 11 C (chainF C)) = true := by quickRfl
theorem p1bw : wordsC 11 C (cert.mGens.map code) MW cert.depth = true := by quickRfl
theorem p1bc0 : chainChunk 11 C
    (fun s => CFSG.KC.LQT.P.allL (cert.mGens.map code) fun g => inC 11 C (chainF C) (CFSG.KC.LQT.P.mul 11 s g)) 0 = true := by quickRfl
theorem p1bc1 : chainChunk 11 C
    (fun s => CFSG.KC.LQT.P.allL (cert.mGens.map code) fun g => inC 11 C (chainF C) (CFSG.KC.LQT.P.mul 11 s g)) 1 = true := by quickRfl
theorem p1bc2 : chainChunk 11 C
    (fun s => CFSG.KC.LQT.P.allL (cert.mGens.map code) fun g => inC 11 C (chainF C) (CFSG.KC.LQT.P.mul 11 s g)) 2 = true := by quickRfl
theorem p1bc3 : chainChunk 11 C
    (fun s => CFSG.KC.LQT.P.allL (cert.mGens.map code) fun g => inC 11 C (chainF C) (CFSG.KC.LQT.P.mul 11 s g)) 3 = true := by quickRfl
theorem p1bc4 : chainChunk 11 C
    (fun s => CFSG.KC.LQT.P.allL (cert.mGens.map code) fun g => inC 11 C (chainF C) (CFSG.KC.LQT.P.mul 11 s g)) 4 = true := by quickRfl
theorem p1bc5 : chainChunk 11 C
    (fun s => CFSG.KC.LQT.P.allL (cert.mGens.map code) fun g => inC 11 C (chainF C) (CFSG.KC.LQT.P.mul 11 s g)) 5 = true := by quickRfl
theorem p1bc6 : chainChunk 11 C
    (fun s => CFSG.KC.LQT.P.allL (cert.mGens.map code) fun g => inC 11 C (chainF C) (CFSG.KC.LQT.P.mul 11 s g)) 6 = true := by quickRfl
theorem p1bc7 : chainChunk 11 C
    (fun s => CFSG.KC.LQT.P.allL (cert.mGens.map code) fun g => inC 11 C (chainF C) (CFSG.KC.LQT.P.mul 11 s g)) 7 = true := by quickRfl
theorem p1bc8 : chainChunk 11 C
    (fun s => CFSG.KC.LQT.P.allL (cert.mGens.map code) fun g => inC 11 C (chainF C) (CFSG.KC.LQT.P.mul 11 s g)) 8 = true := by quickRfl
theorem p1bc9 : chainChunk 11 C
    (fun s => CFSG.KC.LQT.P.allL (cert.mGens.map code) fun g => inC 11 C (chainF C) (CFSG.KC.LQT.P.mul 11 s g)) 9 = true := by quickRfl
theorem p1bc10 : chainChunk 11 C
    (fun s => CFSG.KC.LQT.P.allL (cert.mGens.map code) fun g => inC 11 C (chainF C) (CFSG.KC.LQT.P.mul 11 s g)) 10 = true := by quickRfl
theorem p1b : grpC 11 C (chainF C) (cert.mGens.map code) MW cert.depth = true :=
  grpC_intro (lv := C.head!) (C := C.tail) p1bg p1bw fun j hj => match j, hj with
    | 0, _ => p1bc0
    | 1, _ => p1bc1
    | 2, _ => p1bc2
    | 3, _ => p1bc3
    | 4, _ => p1bc4
    | 5, _ => p1bc5
    | 6, _ => p1bc6
    | 7, _ => p1bc7
    | 8, _ => p1bc8
    | 9, _ => p1bc9
    | 10, _ => p1bc10
    | _k + 11, h => absurd h (Nat.not_lt.2 (Nat.le_add_left _ _))
theorem p1bM : grpM 11 C (chainF C) cert.depth (cert.mGens.map code) MW = true :=
  grpM_of_grpC p1b
theorem q0 : closedX 11 C (chainF C) cert.depth mem0
    (mkX 11 C (chainF C) cert.depth mem0) = true := by quickRfl
theorem q1 : closedX 11 C (chainF C) cert.depth mem1
    (mkX 11 C (chainF C) cert.depth mem1) = true := by quickRfl
theorem q2 : closedX 11 C (chainF C) cert.depth mem2
    (mkX 11 C (chainF C) cert.depth mem2) = true := by quickRfl
theorem m3g : CFSG.KC.LQT.P.allL mem3.1 (inC 11 C (chainF C)) = true := by quickRfl
theorem m3w : wordsC 11 C mem3.1 mem3.2.2 cert.depth = true := by quickRfl
theorem m3c0 : chainChunk 11 C
    (fun s => CFSG.KC.LQT.P.allL mem3.1 fun g => inC 11 C (chainF C) (CFSG.KC.LQT.P.mul 11 s g)) 0 = true := by quickRfl
theorem m3c1 : chainChunk 11 C
    (fun s => CFSG.KC.LQT.P.allL mem3.1 fun g => inC 11 C (chainF C) (CFSG.KC.LQT.P.mul 11 s g)) 1 = true := by quickRfl
theorem m3c2 : chainChunk 11 C
    (fun s => CFSG.KC.LQT.P.allL mem3.1 fun g => inC 11 C (chainF C) (CFSG.KC.LQT.P.mul 11 s g)) 2 = true := by quickRfl
theorem m3c3 : chainChunk 11 C
    (fun s => CFSG.KC.LQT.P.allL mem3.1 fun g => inC 11 C (chainF C) (CFSG.KC.LQT.P.mul 11 s g)) 3 = true := by quickRfl
theorem m3c4 : chainChunk 11 C
    (fun s => CFSG.KC.LQT.P.allL mem3.1 fun g => inC 11 C (chainF C) (CFSG.KC.LQT.P.mul 11 s g)) 4 = true := by quickRfl
theorem m3c5 : chainChunk 11 C
    (fun s => CFSG.KC.LQT.P.allL mem3.1 fun g => inC 11 C (chainF C) (CFSG.KC.LQT.P.mul 11 s g)) 5 = true := by quickRfl
theorem m3c6 : chainChunk 11 C
    (fun s => CFSG.KC.LQT.P.allL mem3.1 fun g => inC 11 C (chainF C) (CFSG.KC.LQT.P.mul 11 s g)) 6 = true := by quickRfl
theorem m3c7 : chainChunk 11 C
    (fun s => CFSG.KC.LQT.P.allL mem3.1 fun g => inC 11 C (chainF C) (CFSG.KC.LQT.P.mul 11 s g)) 7 = true := by quickRfl
theorem m3c8 : chainChunk 11 C
    (fun s => CFSG.KC.LQT.P.allL mem3.1 fun g => inC 11 C (chainF C) (CFSG.KC.LQT.P.mul 11 s g)) 8 = true := by quickRfl
theorem m3c9 : chainChunk 11 C
    (fun s => CFSG.KC.LQT.P.allL mem3.1 fun g => inC 11 C (chainF C) (CFSG.KC.LQT.P.mul 11 s g)) 9 = true := by quickRfl
theorem m3c10 : chainChunk 11 C
    (fun s => CFSG.KC.LQT.P.allL mem3.1 fun g => inC 11 C (chainF C) (CFSG.KC.LQT.P.mul 11 s g)) 10 = true := by quickRfl
theorem m3 : grpC 11 C (chainF C) mem3.1 mem3.2.2 cert.depth = true :=
  grpC_intro (lv := C.head!) (C := C.tail) m3g m3w fun j hj => match j, hj with
    | 0, _ => m3c0
    | 1, _ => m3c1
    | 2, _ => m3c2
    | 3, _ => m3c3
    | 4, _ => m3c4
    | 5, _ => m3c5
    | 6, _ => m3c6
    | 7, _ => m3c7
    | 8, _ => m3c8
    | 9, _ => m3c9
    | 10, _ => m3c10
    | _k + 11, h => absurd h (Nat.not_lt.2 (Nat.le_add_left _ _))
theorem q3 : closedX 11 C (chainF C) cert.depth mem3
    (mkX 11 C (chainF C) cert.depth mem3) = true := m3
theorem q4 : closedX 11 C (chainF C) cert.depth mem4
    (mkX 11 C (chainF C) cert.depth mem4) = true := by quickRfl
theorem p1c : allA (membersX 11 C (chainF C) cert.depth ms) (fun p =>
    closedX 11 C (chainF C) cert.depth p.1 p.2) = true :=
  allA_cons q0 (allA_cons q1 (allA_cons q2 (allA_cons q3 (allA_cons q4 rfl))))
theorem p1 : closedOKC 11 C (chainF C) cert.depth (cert.mGens.map code) MW ms = true := by
  rw [closedOKC, p1a, p1bM, p1c]
  rfl
theorem p2 : coverC 11 C (chainF C) (bfsM 11 C (chainF C) (cert.tGens.map code) cert.depth)
    (repsCode cert) = true := by quickRfl
theorem p3 : repsC 11 C (chainF C) (cert.tGens.map code) (membersX 11 C (chainF C) cert.depth ms)
    (repsCode cert) = true := by quickRfl
theorem p4 : joinsC 11 C (chainF C) (membersX 11 C (chainF C) cert.depth ms) cert.joins = true := by
  quickRfl
theorem p5 : sizesC (chainF C) (membersX 11 C (chainF C) cert.depth ms) cert.sizes cert.msize =
    true := by quickRfl
theorem p6 : tleC 11 C (chainF C) (cert.tGens.map code) = true := by quickRfl
theorem hl : latC 11 C cert.depth (cert.mGens.map code) MW (cert.tGens.map code)
    (cert.lat.map (List.map code)) ms (repsCode cert) cert.joins cert.sizes cert.msize = true :=
  latC_intro p0 p1 p2 p3 p4 p5 p6
theorem hd : diagK 11 6 64 (aGens.map code) (a6Gens.map code) 360 = true := by quickRfl
theorem hc : containsC 11 C 64 (cert.tGens.map code) (cert.lat.map (List.map code)) ms cert.sizes
    (aGens.map code) 5 720 = true := by quickRfl
theorem inj : chainInj 11 C = true := by quickRfl

end CFSG.KD.LQT.C4084

end
