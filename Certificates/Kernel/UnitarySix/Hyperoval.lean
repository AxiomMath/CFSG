module

public import Certificates.Kernel.UnitarySix.Tables
public import CFSG.Certificates.Kernel.U6Sound3146
public import CFSG.LocalAnalysis.EvenSmallLie.UnitarySix.FischerHyperovalInputs
import CFSG.Certificates.Kernel.Common.Harness
public import CFSG.Fischer.Polar.Facts
public import CFSG.LocalAnalysis.ComponentClassification.TwoLayer
public import CFSG.LocalAnalysis.EvenSmallLie.UnitarySix.FischerPoints
public import CFSG.LocalAnalysis.SectionRank.Ccomm.Supercritical
public import CFSG.LocalAnalysis.ZStar.BrauerSylowFusion
public import CFSG.LocalAnalysis.ZStar.PrincipalBlockTraceApplication
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Isaacs.VII.lemma_7_7
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Basic

public section

namespace CertificateChecks.KernelU6

open CFSG.KC.U6 CFSG.Fischer.Native CFSG.F4.Native

theorem kDom1 : check3146 nzC prodCoordC U.UP T.R 1 = true := by quickRfl
theorem kDom2 : check3146 nzC prodCoordC U.UP T.R 2 = true := by quickRfl
theorem kDom3 : check3146 nzC prodCoordC U.UP T.R 3 = true := by quickRfl

theorem domOK_eq (k : ℕ) :
    CFSG.EvenSmallLie.UnitarySix.Fischer.domOK k = domOKG nzC prodCoordC k uPts uPos := by
  unfold CFSG.EvenSmallLie.UnitarySix.Fischer.domOK domOKG rootFlags rootFlagsG
  rw [tvTabs_eq]

open Certificates in
open CFSG.EvenSmallLie.UnitarySix.Fischer in
theorem cert3146 : domOK 1 = true ∧ domOK 2 = true ∧ domOK 3 = true := by
  rw [domOK_eq, domOK_eq, domOK_eq]
  exact ⟨sound3146 up_eq pos_eq kTables kDom1, sound3146 up_eq pos_eq kTables kDom2,
    sound3146 up_eq pos_eq kTables kDom3⟩

end CertificateChecks.KernelU6

end
