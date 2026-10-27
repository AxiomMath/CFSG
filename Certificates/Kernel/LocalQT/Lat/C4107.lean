module

public import CFSG.Certificates.Kernel.LocalQTLatMSound
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.A5.G3M23Cert2Inputs
import CFSG.Certificates.Kernel.Common.Harness
import CFSG.Certificates.Kernel.Common.EachUnfold
public import CFSG.Certificates.Kernel.LocalQTListLemmas
public import CFSG.LocalAnalysis.ComponentInitial.PGroupRankOneClassification
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.A312ListAlt7Base
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.A312ListBender
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.A5.G3LatSixCheck
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.A5.G3M23Base
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

namespace CFSG.KD.LQT.C4107

open CFSG.KC.LQT.L CFSG.KC.LQT.S CFSG.QuasithinUnique.A5.G3.M23.C2

@[expose] def C : List Lvl :=
  [(8, [18319612544494840291299204332575148, 12317260177020876130905146352871830, 12316023435029016272706094263282070, 8137862594843320543019368986355055, 3959686626626020281508252000195846, 21361976920201965850244180334586550, 13899283076529971948251999799495170, 14507768013671033464741597891527942, 29435622565346244453937714881988640, 23471369271338968913548927433184710, 6759865721853017703345519692559465, 8139090786115089837328067581263982, 12316031985741100968618184217376803, 18320840813129856140546450777622530, 2622255481791061587239059840997928, 2621032705298783971649977188391464, 16982215393053280636561268310050278, 13898061100359976565106242765441538, 19942210187442621939809786113963010, 0, 0, 21363204995396269901187621570264235, 8139086082160934603033536395519343], [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 0, 0, 19, 20], 21),
    (2, [14547099054408024187968582935052393, 13858709624681396973297216662897746, 29435622565346244453937714881988640, 15845178620731856731674029435882645, 4527586394290325469282188754489750, 13492398187488036831345189407003725, 14587664540707533799693090921584815, 14872833266773782068332188263587510, 0, 4162511062401350133830438811412176, 9192531172339813220995356208671151, 27529074285257620779905753925758188, 18481890771402992944102463939227730, 14710573411127635853264507326936579, 27366821575429361608166439474182703, 15682925800969005313152529602723374, 14548332467527767845974120442708681, 14871604650759056362369885802054678, 4324751459165380313330139893549355, 0, 0, 14709369901641625839221013392872675, 27730660424511974265743492108048391], [0, 1, 2, 3, 4, 5, 6, 7, 0, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 0, 0, 18, 19], 20),
    (20, [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 29069304957762462340378035758663840, 29435622565346244453937714881988640, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0], 2),
    (0, [29435622565346244453937714881988640, 0, 0, 0, 0, 0, 0, 0, 0, 14467198107451566290799152204548777, 0, 0, 0, 0, 0, 0, 3960914701827186503747538466998416, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0], 3),
    (14, [0, 4609949651496752169413666596915648, 0, 1932673943753585757169341008644800, 13453077182112780322451856740976800, 15846394281359338100872078096140416, 9315464307771708957123737766234464, 8301335393897044550813573335845280, 0, 0, 5745759095500106093648741729995136, 17063342339254353527070354115365056, 6800438437494677028661668120496448, 14710575668127523749034332487092448, 29435622565346244453937714881988640, 22215063894856818460344663261481536, 0, 19537787993874719661128760850713248, 28178107676036394885354171093518816, 0, 0, 23959376304705231203396781182781984, 18929338027188465379704584311703648], [0, 0, 0, 1, 2, 3, 4, 5, 0, 0, 6, 7, 8, 9, 10, 11, 0, 12, 13, 0, 0, 14, 15], 16)]

@[expose] def MW : List (List (List Nat)) :=
  [[[1, 0, 1, 0, 1, 0, 1], [1, 1, 0, 1], [1, 1, 1], [1, 0, 1], [1, 1, 0, 1, 1, 0, 1], [0, 1, 1, 0, 1], [1, 1, 1, 1], [0, 1, 1, 0, 1, 1, 0, 1], [], [1, 1, 1, 1, 1], [1, 1, 1, 1, 1, 1], [0, 1, 0, 1], [1, 0, 1, 0, 1], [1, 0, 1, 1, 0, 1], [0, 1], [1], [0, 1, 1, 1, 1, 1], [1, 1, 1, 0, 1], [0, 1, 0, 1, 1, 0, 1], [], [], [0, 1, 0, 1, 0, 1], [1, 1]],
    [[1, 0, 1, 1, 0, 1, 0, 1, 0, 1, 1, 1, 1, 1, 1], [1, 0, 1, 1, 0, 1, 1, 0, 1, 1, 0, 1], [], [1, 1, 1, 0, 1, 0, 1, 1, 1, 1, 1, 1, 1], [0, 1, 0, 1, 0, 1, 1, 0, 1, 1, 1, 0, 1], [0, 1, 0, 1, 1, 0, 1, 1, 0, 1, 1, 0, 1], [1, 1, 1, 0, 1, 0, 1, 1, 1, 1, 0, 1, 0, 1, 1], [1, 0, 1, 0, 1, 1, 0, 1, 1, 1, 0, 1], [], [0, 1, 1, 1, 0, 1, 0, 1, 0, 1, 1, 1, 1, 1, 1], [1, 0, 1, 0, 1, 0, 1, 1, 0, 1, 1, 1, 0, 1, 1], [0, 1, 1, 1, 0, 1, 0, 1, 1, 1, 1, 1, 1, 1], [1, 1, 1, 0, 1, 1, 0, 1, 1, 0, 1], [1, 1, 0, 1, 1, 1, 1, 1, 0, 1], [1, 1, 0, 1, 0, 1, 1, 0, 1, 1, 1, 0, 1, 1], [0, 1, 1, 0, 1, 0, 1, 1, 0, 1, 1, 1, 0, 1, 1], [1, 1, 1, 0, 1, 0, 1, 0, 1, 1, 1, 1, 1, 1], [1, 0, 1, 0, 1, 1, 1, 1, 1, 0, 1], [0, 1, 1, 0, 1, 1, 1, 1, 1, 0, 1], [], [], [1, 1, 0, 1, 1, 0, 1, 1, 1, 0, 1], [1, 1, 1, 1, 1, 0, 1, 1, 1, 1, 1, 1, 1]],
    [[], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [0], [], [], []],
    [[], [], [], [], [], [], [], [], [], [0, 1, 1, 0, 1, 0, 1, 0, 1, 0], [], [], [], [], [], [], [1, 1, 0, 1, 0, 1, 0, 1], [], [], [], [], [], []],
    [[], [1, 0, 1, 0, 1, 1, 1, 0, 1, 1, 1, 1, 0, 1, 1, 0, 1, 1], [], [0, 1, 1, 0, 1, 0, 1, 1, 0, 1, 1, 0, 1, 0, 1, 1], [1, 0, 1, 0, 1, 1, 1, 1, 1, 1, 1, 1, 0, 1, 0, 1], [0, 1, 0, 1, 1, 1, 0, 1, 1, 0, 1, 1, 1, 1, 1, 1, 1, 0], [0, 1, 0, 1, 1, 0, 1, 1, 1, 1, 0, 1, 1, 0, 1, 1, 1, 1], [1, 1, 1, 0, 1, 1, 0, 1, 1, 1, 0, 1, 1, 1, 1, 1], [], [], [1, 0, 1, 1, 0, 1, 1, 1, 1, 0, 1, 1, 0, 1, 1, 1, 1, 0], [1, 1, 0, 1, 0, 1, 1, 0, 1, 1, 0, 1, 1, 0, 1, 0, 1, 0, 1, 1, 1, 1], [1, 1, 0, 1, 0, 1, 1, 0, 1, 1, 0, 1, 0, 1, 1, 0], [0, 1, 0, 1, 1, 1, 0, 1, 1, 0, 1, 1, 1, 1, 0, 1, 1, 1], [], [0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 1, 1, 1], [], [0, 1, 0, 1, 1, 1, 1, 0, 1, 1, 0, 1, 1, 0, 1, 1, 0, 1, 1, 1, 1, 1], [1, 0, 1, 1, 1, 0, 1, 1, 0, 1, 1, 1, 1, 1, 1, 1], [], [], [1, 1, 1, 1, 0, 1, 0, 1, 0, 1, 1, 1, 1, 1, 0, 1, 1, 1, 1, 0, 1, 1], [1, 0, 1, 0, 1, 0, 1, 1, 1, 1, 1, 1, 0, 1, 1, 1, 1, 0, 1, 1, 1, 1]]]

@[expose] def mem0 : Mem :=
  (((cert.tGens :: cert.lat).getD 0 []).map code, false, [])
@[expose] def mem1 : Mem :=
  (((cert.tGens :: cert.lat).getD 1 []).map code, false, [])
@[expose] def mem2 : Mem :=
  (((cert.tGens :: cert.lat).getD 2 []).map code, false, [])
@[expose] def mem3 : Mem :=
  (((cert.tGens :: cert.lat).getD 3 []).map code, true, [[[0, 3, 2, 3, 4, 3, 2, 4, 1, 2], [1, 0, 4, 3, 2, 4, 3, 1], [2, 4, 1, 0, 1, 3, 4, 3, 4], [0, 1, 0, 4, 3, 4, 1, 3, 4, 1], [3, 2, 1, 4, 0, 2, 4, 2], [3, 0, 4, 0, 1, 2], [0, 3, 4, 1, 4, 0, 3, 2, 3], [2, 3, 0, 4, 1, 4, 1, 0], [], [0, 2, 4, 1, 2, 4, 1, 3, 2], [4, 3, 4, 3, 1, 3, 4, 3, 0], [0, 1, 3, 0, 4, 1, 2, 4, 3, 4], [0, 2, 4, 1, 3, 2, 1, 4, 2], [2, 3, 4, 0, 2, 4, 0, 2], [3, 3, 4, 0, 2, 4, 3, 4], [1, 0, 3, 4, 0, 2, 3, 2], [1, 3, 2, 4, 3, 2, 4, 1, 2, 4], [0, 3, 2, 4, 1, 0, 4, 2, 3, 4], [0, 3, 1, 4], [], [], [2, 3, 4, 1, 2, 4, 1, 2], [2, 4, 0, 1, 3, 1, 4, 0, 1]],
    [[3, 3, 4, 1, 3, 4, 3, 2], [1, 4, 3, 4, 3, 1], [], [0, 1, 0, 1, 4, 2, 4], [0, 3, 0, 4, 0, 2, 1, 4], [4, 0, 3, 1, 4, 0, 3, 1, 4], [3, 2, 1, 4, 1, 2, 4, 1], [0, 1, 4, 1, 3, 4, 0, 1, 4], [], [4, 0, 1, 4, 1, 3, 2], [0, 1, 2, 4, 2, 3, 3, 4], [4, 1, 3, 4, 3, 2, 3, 4, 3], [0, 1, 4, 3, 3, 1, 4, 1, 2, 4], [3, 1, 3, 4, 0, 1, 0, 3], [0, 1, 2, 4, 2, 3, 3, 4, 2], [4, 1, 0, 4, 2, 4, 1, 3, 2], [0, 1, 4, 3, 0, 4, 0, 1], [4, 0, 3, 1, 3, 4, 1, 2, 4], [1, 0, 4, 0, 2, 1, 4, 3, 2], [], [], [0, 3, 3, 2, 4, 1, 4, 3], [3, 3, 4, 2, 1, 4, 3, 0, 1]],
    [[], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [0, 1, 4, 1, 3, 4, 2, 4, 3], [], [], []],
    [[], [], [], [], [], [], [], [], [], [1, 0, 1, 4, 2, 4, 3, 4], [], [], [], [], [], [], [4, 0, 1, 4, 3, 0, 1, 2], [], [], [], [], [], []],
    [[], [4, 1, 3, 4, 1, 2, 4, 0, 1], [], [0, 4, 1, 3, 4, 1, 2, 4, 1], [4, 1, 0, 4, 1, 3, 1, 4, 3], [0, 1, 0, 1], [2, 4, 1, 4, 1, 4], [0, 1, 2], [], [], [2, 4, 1, 3, 4, 1, 2, 4], [1, 0, 4, 1, 3, 4, 1, 2, 4], [1, 0, 4, 1, 4, 1, 4], [1, 3, 4, 0, 1, 3, 4, 3, 0, 4], [], [4, 1, 3, 4, 1, 2, 4, 2], [], [0, 1, 4, 1, 3, 4, 1, 2, 4], [0, 2, 1], [], [], [0, 2, 4, 1, 4, 1, 4, 0], [0, 1, 4, 1, 4, 1, 4]]])
@[expose] def mem4 : Mem :=
  (((cert.tGens :: cert.lat).getD 4 []).map code, false, [])

@[expose] def ms : List Mem := [mem0, mem1, mem2, mem3, mem4]

theorem p0 : memsOK (cert.tGens.map code) (cert.lat.map (List.map code)) ms = true := by
  quickRfl
theorem p1a : chainOK 23 C = true := by quickRfl
theorem p1bg : CFSG.KC.LQT.P.allL (cert.mGens.map code) (inC 23 C (chainF C)) = true := by quickRfl
theorem p1bw : wordsC 23 C (cert.mGens.map code) MW cert.depth = true := by quickRfl
@[expose] noncomputable def p1bcF (j : Nat) : Bool := chainChunk 23 C
  (fun s => CFSG.KC.LQT.P.allL (cert.mGens.map code) fun g => inC 23 C (chainF C)
    (CFSG.KC.LQT.P.mul 23 s g)) j

#kc_each_unfold p1bcF 0 23 as CFSG.KD.LQT.C4107.p1bc
theorem p1b : grpC 23 C (chainF C) (cert.mGens.map code) MW cert.depth = true :=
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
    | 11, _ => p1bc11
    | 12, _ => p1bc12
    | 13, _ => p1bc13
    | 14, _ => p1bc14
    | 15, _ => p1bc15
    | 16, _ => p1bc16
    | 17, _ => p1bc17
    | 18, _ => p1bc18
    | 19, _ => p1bc19
    | 20, _ => p1bc20
    | 21, _ => p1bc21
    | 22, _ => p1bc22
    | _k + 23, h => absurd h (Nat.not_lt.2 (Nat.le_add_left _ _))
theorem p1bM : grpM 23 C (chainF C) cert.depth (cert.mGens.map code) MW = true :=
  grpM_of_grpC p1b
theorem q0 : closedX 23 C (chainF C) cert.depth mem0
    (mkX 23 C (chainF C) cert.depth mem0) = true := by quickRfl
theorem q1 : closedX 23 C (chainF C) cert.depth mem1
    (mkX 23 C (chainF C) cert.depth mem1) = true := by quickRfl
theorem q2 : closedX 23 C (chainF C) cert.depth mem2
    (mkX 23 C (chainF C) cert.depth mem2) = true := by quickRfl
theorem m3g : CFSG.KC.LQT.P.allL mem3.1 (inC 23 C (chainF C)) = true := by quickRfl
theorem m3w : wordsC 23 C mem3.1 mem3.2.2 cert.depth = true := by quickRfl
@[expose] noncomputable def m3cF (j : Nat) : Bool := chainChunk 23 C
  (fun s => CFSG.KC.LQT.P.allL mem3.1 fun g => inC 23 C (chainF C) (CFSG.KC.LQT.P.mul 23 s g)) j

#kc_each_unfold m3cF 0 23 as CFSG.KD.LQT.C4107.m3c
theorem m3 : grpC 23 C (chainF C) mem3.1 mem3.2.2 cert.depth = true :=
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
    | 11, _ => m3c11
    | 12, _ => m3c12
    | 13, _ => m3c13
    | 14, _ => m3c14
    | 15, _ => m3c15
    | 16, _ => m3c16
    | 17, _ => m3c17
    | 18, _ => m3c18
    | 19, _ => m3c19
    | 20, _ => m3c20
    | 21, _ => m3c21
    | 22, _ => m3c22
    | _k + 23, h => absurd h (Nat.not_lt.2 (Nat.le_add_left _ _))
theorem q3 : closedX 23 C (chainF C) cert.depth mem3
    (mkX 23 C (chainF C) cert.depth mem3) = true := m3
theorem q4 : closedX 23 C (chainF C) cert.depth mem4
    (mkX 23 C (chainF C) cert.depth mem4) = true := by quickRfl
theorem p1c : allA (membersX 23 C (chainF C) cert.depth ms) (fun p =>
    closedX 23 C (chainF C) cert.depth p.1 p.2) = true :=
  allA_cons q0 (allA_cons q1 (allA_cons q2 (allA_cons q3 (allA_cons q4 rfl))))
theorem p1 : closedOKC 23 C (chainF C) cert.depth (cert.mGens.map code) MW ms = true := by
  rw [closedOKC, p1a, p1bM, p1c]
  rfl
theorem p2 : coverC 23 C (chainF C) (bfsM 23 C (chainF C) (cert.tGens.map code) cert.depth)
    (repsCode cert) = true := by quickRfl
theorem p3 : repsC 23 C (chainF C) (cert.tGens.map code) (membersX 23 C (chainF C) cert.depth ms)
    (repsCode cert) = true := by quickRfl
theorem p4 : joinsC 23 C (chainF C) (membersX 23 C (chainF C) cert.depth ms) cert.joins = true := by
  quickRfl
theorem p5 : sizesC (chainF C) (membersX 23 C (chainF C) cert.depth ms) cert.sizes cert.msize =
    true := by quickRfl
theorem p6 : tleC 23 C (chainF C) (cert.tGens.map code) = true := by quickRfl
theorem hl : latC 23 C cert.depth (cert.mGens.map code) MW (cert.tGens.map code)
    (cert.lat.map (List.map code)) ms (repsCode cert) cert.joins cert.sizes cert.msize = true :=
  latC_intro p0 p1 p2 p3 p4 p5 p6
theorem ht : tleCC 23 C cert.depth (cert.mGens.map code) MW (cert.tGens.map code) = true := by
  rw [tleCC, p1a, p1bM, p6]
  rfl
theorem hs : latSixC 23 C cert.depth (cert.tGens.map code) (cert.lat.map (List.map code)) ms
    cert.sizes ([aData1, aData2].map fun A => (A.gens.map code, A.perf)) = true := by quickRfl
theorem inj : chainInj 23 C = true := by quickRfl

end CFSG.KD.LQT.C4107

end
