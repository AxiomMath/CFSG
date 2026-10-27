module

public import Certificates.Kernel.LocalQT.Lat.D4055
public import CFSG.Certificates.Kernel.LocalQTLatMSound
public import Certificates.Data.Kernel.LocalQT.LatT
public import CFSG.Certificates.Kernel.LocalQTLatESound
public import Certificates.Data.Kernel.LocalQT.ChainInj
import CFSG.Certificates.Kernel.LocalQTTleTSound
import CFSG.Certificates.Kernel.Common.Harness
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
import CFSG.Certificates.Kernel.LocalQTLatCCheckSound

set_option maxRecDepth 100000
set_option maxHeartbeats 0

public section

namespace CFSG.KD.LQT.C4055

open CFSG.KC.LQT.L CFSG.KC.LQT.S CFSG.QuasithinUnique.A5.G3 CFSG.QuasithinUnique.A5.G3.M23.C1
open CFSG.QuasithinUnique.Vol2Native.A312L.PermLat

theorem p0 : memsOKG (cert.tGens.map code) (cert.lat.map (List.map code)) ms = true := by
  quickRfl
theorem p1 : chainOK 23 C = true := by quickRfl
theorem p2 : grpT 23 C (chainF C) (cert.mGens.map code) MW 5 [] 0 cert.depth = true := by
  quickRfl
theorem p3 : allA ms (closedMG 23 cert.depth) = true := by quickRfl
theorem p4a : coverA 23 C (chainF C) mem0 4 labT (repsCode cert) = true := by quickRfl
theorem p4d : coverD 23 mem0 4 labT (repsCode cert) = true := by quickRfl
theorem p4n : coverN 23 (chainF C) mem0 (repsCode cert) = true := by quickRfl
theorem p4 : Option.rec (motive := fun _ => Bool) false
    (fun Tm => coverG 23 C (chainF C) Tm 4 labT (repsCode cert)) (getO ms 0) = true :=
  coverG_intro p4a p4d p4n
theorem p5 : repsG 23 (cert.tGens.map code) ms (repsCode cert) = true := by quickRfl
theorem p6 : joinsG 23 ms cert.joins = true := by quickRfl
theorem p7 : sizesG (chainF C) ms cert.sizes cert.msize = true := by quickRfl
theorem p8 : tleC 23 C (chainF C) (cert.tGens.map code) = true := by quickRfl
theorem inj : chainInj 23 C = true := by quickRfl
theorem injM : allA ms (fun m => chainInj 23 m.2.1) = true := by quickRfl

@[expose] def msX : List Mem := (cert.tGens :: cert.lat).map fun g => (g.map code, false, [])

theorem hs : latSixC 23 C cert.depth (cert.tGens.map code) (cert.lat.map (List.map code)) msX
    cert.sizes ([aData1].map fun A => (A.gens.map code, A.perf)) = true := by quickRfl

theorem ht : tleT 23 C cert.depth (cert.mGens.map code) MW 5 [] 0 (cert.tGens.map code) =
    true := by
  rw [tleT, p1, p2, p8]
  rfl

end CFSG.KD.LQT.C4055

end
