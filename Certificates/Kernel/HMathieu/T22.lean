module

public import Certificates.Data.Kernel.HMathieu.Tab
public import CFSG.Quasithin.Background.HMathieuMask
public import CFSG.Quasithin.Background.HMathieuCodeMask
public import CFSG.Certificates.Kernel.Common.Harness
public meta import CFSG.Certificates.Kernel.Common.JsonGz
public meta import CFSG.Certificates.Kernel.Common.Repo
public import CFSG.Certificates.Kernel.Common.JsonGz
public import CFSG.Certificates.Kernel.Common.Repo
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueKProper
public import CFSG.LocalAnalysis.ComponentClassification.TwoLayer
public import CFSG.LocalAnalysis.QuasithinUnique.Setting
public import CFSG.LocalAnalysis.RankThreeCoreUniqueness.CharacteristicPrimeLocal
public import CFSG.LocalAnalysis.SectionRank.EvenCover.Catalog
public import CFSG.LocalAnalysis.SectionRank.LargeRee.SuzukiData
public import CFSG.LocalAnalysis.SectionRank.OddCover.CatalogOdd
public import CFSG.LocalAnalysis.SectionRank.SectionAssemblyBase
public import CFSG.LocalAnalysis.SectionRank.Sporadic.J4LocalBase
public import CFSG.LocalAnalysis.SectionRank.Sporadic.MathieuLocalBase
public import CFSG.LocalAnalysis.SectionRank.TitsCover
public import CFSG.Quasithin.Background.A3Components
public import CFSG.Quasithin.Background.A3ComponentsAmbient
public import CFSG.Quasithin.Background.B1Basic
public import CFSG.Quasithin.Background.E1
public import CFSG.Quasithin.Background.E1Sec4
public import CFSG.Quasithin.Background.E1Sec5
public import CFSG.Quasithin.Background.E1Sec8
public import CFSG.Quasithin.Background.E1Solv
public import CFSG.Quasithin.Background.E1Twelve
public import CFSG.Sporadic.J4.Simple
public import CFSG.Sporadic.J4Base
public import CFSG.Sporadic.Mathieu.M12
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Huppert.IV.ComplementTransfer
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFchapter1section1.proposition_4_c
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Proposition82
public import Certificates.Certificate43

set_option maxRecDepth 400000

public section

#kc_repo #kc_json_gz CertificateChecks.KernelHMathieu.T22
  "Certificates/Kernel/HMathieu/data/T22.json.gz" 32137 1188082706113008685
  (gens : List Nat) (E : List Nat) (inv : List Nat) (P : List Nat) (rows : List (Nat × Nat))
  (Mc : List (List Nat)) (Md : List (List Nat))

namespace CertificateChecks.KernelHMathieu.T22

open CFSG.KC.HMathieu CFSG.KC.Enum CFSG.Quasithin.H.Mathieu

set_option maxHeartbeats 0 in
theorem bfs : (bfsP gens 64 [pidn 24 5] [pidn 24 5]).reverse = E := by decide +kernel

theorem vpE : E.all vpK = true := by decide +kernel

theorem vpG : gens.all vpK = true := by decide +kernel

theorem invOK : invFrom (E.getD 0 0) E 0 = inv := by decide +kernel

theorem pOK : P = inv.map (fun i => E.getD i 0) ++ [E.getD 0 0] := by decide +kernel

theorem lenOK : inv.length = 71 ∧ rows.length = 71 := by decide +kernel

set_option maxHeartbeats 0 in
theorem tabs : tabsK 71 P rows = true := by decide +kernel

set_option maxHeartbeats 0 in
theorem mcOK : Mc = P.map (matP cc10Cols lift10Cols 10) := by decide +kernel

set_option maxHeartbeats 0 in
theorem mdOK : Md = P.map (matP κC22Cols lift22Cols 10) := by decide +kernel

end CertificateChecks.KernelHMathieu.T22

end
