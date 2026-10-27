module

public import CFSG.Certificates.Kernel.LocalQTLatSound
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.L246B113OverCertL32Inputs
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

namespace CFSG.KD.LQT.C4124

open CFSG.KC.LQT.L CFSG.KC.LQT.S CFSG.QuasithinUnique.Bridge.Over.CertL32

theorem p1 : closedOKK 7 cert.depth (cert.mGens.map code) (cert.tGens.map code)
    (cert.lat.map (List.map code)) = true := by quickRfl
theorem p2 : coverK 7 cert.depth (cert.mGens.map code) (cert.tGens.map code) (repsCode cert) =
    true := by quickRfl
theorem p3 : repsK 7 (cert.tGens.map code)
    (membersK 7 cert.depth (cert.tGens.map code) (cert.lat.map (List.map code)))
    (repsCode cert) = true := by quickRfl
theorem p4 : joinsK 7
    (membersK 7 cert.depth (cert.tGens.map code) (cert.lat.map (List.map code)))
    cert.joins = true := by quickRfl
theorem p5 : sizesK 7 cert.depth (cert.mGens.map code) (cert.tGens.map code)
    (cert.lat.map (List.map code)) cert.sizes cert.msize = true := by quickRfl
theorem p6 : tleK 7 cert.depth (cert.mGens.map code) (cert.tGens.map code) = true := by
  quickRfl
theorem hl : latK 7 cert.depth (cert.mGens.map code) (cert.tGens.map code)
    (cert.lat.map (List.map code)) (repsCode cert) cert.joins cert.sizes cert.msize = true :=
  latK_intro p1 p2 p3 p4 p5 p6
theorem hm : memberK 7 cert.depth (cert.tGens.map code) (cert.lat.map (List.map code))
    cert.msize (cts.map fun ct => (ct.depth, ct.hGens.map code, ct.nGens.map code, ct.expo)) =
    true := by
  quickRfl

end CFSG.KD.LQT.C4124

end
