module

public import Certificates.Kernel.LocalQT.Lat.D4079
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

public section

namespace CFSG.KD.LQT.C4079

open CFSG.KC.LQT.L CFSG.KC.LQT.S CFSG.QuasithinUnique.Vol2Native.A312L.M12Lat
open CFSG.QuasithinUnique.Vol2Native.A312L.PermLat

theorem p0 : memsOKG (cert.tGens.map code) (cert.lat.map (List.map code)) ms = true := by
  quickRfl
theorem p1 : chainOK 12 C = true := by quickRfl
theorem p2 : grpT 12 C (chainF C) (cert.mGens.map code) MW 2 TW 46 cert.depth = true := by
  quickRfl
theorem p3 : allA ms (closedMG 12 cert.depth) = true := by quickRfl
theorem p4a : coverA 12 C (chainF C) mem0 2 labT (repsCode cert) = true := by quickRfl
theorem p4d : coverD 12 mem0 2 labT (repsCode cert) = true := by quickRfl
theorem p4n : coverN 12 (chainF C) mem0 (repsCode cert) = true := by quickRfl
theorem p4 : Option.rec (motive := fun _ => Bool) false
    (fun Tm => coverG 12 C (chainF C) Tm 2 labT (repsCode cert)) (getO ms 0) = true :=
  coverG_intro p4a p4d p4n
theorem p5 : repsG 12 (cert.tGens.map code) ms (repsCode cert) = true := by quickRfl
theorem p6 : joinsG 12 ms cert.joins = true := by quickRfl
theorem p7 : sizesG (chainF C) ms cert.sizes cert.msize = true := by quickRfl
theorem p8 : tleC 12 C (chainF C) (cert.tGens.map code) = true := by quickRfl
theorem inj : chainInj 12 C = true := by quickRfl
theorem injM : allA ms (fun m => chainInj 12 m.2.1) = true := by quickRfl

end CFSG.KD.LQT.C4079

end
