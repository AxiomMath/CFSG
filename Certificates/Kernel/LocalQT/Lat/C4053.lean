module

public import Certificates.Kernel.LocalQT.Lat.D4053
public import CFSG.Certificates.Kernel.LocalQTLatESound
import CFSG.Certificates.Kernel.Common.Harness
public import CFSG.LocalAnalysis.ComponentInitial.PGroupRankOneClassification
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.A312ListAlt7Base
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.A312ListBender
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.A312ListPermExt
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

namespace CFSG.KD.LQT.C4053

open CFSG.KC.LQT.L CFSG.KC.LQT.S CFSG.QuasithinUnique.Vol2Native.A312L.M22Lat

theorem p0 : memsOKG (cert.tGens.map code) (cert.lat.map (List.map code)) ms = true := by
  quickRfl
theorem p1 : chainOK 22 C = true := by quickRfl
theorem p2 : grpT 22 C (chainF C) (cert.mGens.map code) MW 2 TW 38 cert.depth = true := by
  quickRfl
theorem p3 : allA ms (closedMG 22 cert.depth) = true := by quickRfl
theorem p4a : coverA 22 C (chainF C) mem0 3 labT (repsCode cert) = true := by quickRfl
theorem p4d : coverD 22 mem0 3 labT (repsCode cert) = true := by quickRfl
theorem p4n : coverN 22 (chainF C) mem0 (repsCode cert) = true := by quickRfl
theorem p4 : Option.rec (motive := fun _ => Bool) false
    (fun Tm => coverG 22 C (chainF C) Tm 3 labT (repsCode cert)) (getO ms 0) = true :=
  coverG_intro p4a p4d p4n
theorem p5 : repsG 22 (cert.tGens.map code) ms (repsCode cert) = true := by quickRfl
theorem p6 : joinsG 22 ms cert.joins = true := by quickRfl
theorem p7 : sizesG (chainF C) ms cert.sizes cert.msize = true := by quickRfl
theorem p8 : tleC 22 C (chainF C) (cert.tGens.map code) = true := by quickRfl
theorem hl : latG 22 C cert.depth (cert.mGens.map code) MW 2 TW 38 (cert.tGens.map code)
    (cert.lat.map (List.map code)) ms 3 labT (repsCode cert) cert.joins cert.sizes cert.msize =
    true :=
  latG_intro p0 p1 p2 p3 p4 p5 p6 p7 p8
theorem hd5 : diagExtC 22 5 64 (p5Gens.map code) (a5Gens.map code) 960 60 C5A W5A C5B W5B C5D
    W5D = true := by quickRfl
theorem hd6 : diagExtC 22 6 64 (l6Gens.map code) (a6Gens.map code) 5760 360 C6A W6A C6B W6B C6D
    W6D = true := by quickRfl
theorem hp5 : perfK 22 (p5Gens.map code) perf5 = true := by quickRfl
theorem hp6 : perfK 22 (l6Gens.map code) perf6 = true := by quickRfl
theorem hc5 : containsG 22 64 (cert.tGens.map code) (cert.lat.map (List.map code)) ms cert.sizes
    (p5Gens.map code) 6 1920 = true := by quickRfl
theorem inj : chainInj 22 C = true := by quickRfl
theorem injM : allA ms (fun m => chainInj 22 m.2.1) = true := by quickRfl
theorem inj5 : chainInj 22 C5A = true ∧ chainInj 5 C5B = true ∧ chainInj (22 + 5) C5D = true :=
  ⟨by quickRfl, by quickRfl, by quickRfl⟩
theorem inj6 : chainInj 22 C6A = true ∧ chainInj 6 C6B = true ∧ chainInj (22 + 6) C6D = true :=
  ⟨by quickRfl, by quickRfl, by quickRfl⟩
theorem hc6 : containsG 22 64 (cert.tGens.map code) (cert.lat.map (List.map code)) ms cert.sizes
    (l6Gens.map code) 6 5760 = true := by quickRfl

end CFSG.KD.LQT.C4053

end
