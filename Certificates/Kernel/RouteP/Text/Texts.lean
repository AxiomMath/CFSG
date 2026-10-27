module

public import CFSG.Certificates.Kernel.RouteP.TextSlp
public meta import CFSG.Certificates.Kernel.Common.StrChunks
public import CFSG.Certificates.Kernel.Common.StrChunks

public section

set_option maxRecDepth 1000000

#str_chunks CertificateChecks.KernelRouteP.TPres
  CFSG.EvenSporadicStandard.TwoFi22.DS81.RouteP.Model.Native.presText 140000 1000000 512
#str_chunks CertificateChecks.KernelRouteP.TBr
  CFSG.EvenSporadicStandard.TwoFi22.DS81.RouteP.Model.Native.bridgeText 140000 1000000 512
#str_chunks CertificateChecks.KernelRouteP.TBrG
  CFSG.EvenSporadicStandard.TwoFi22.DS81.RouteP.Model.Native.bridgeGensText 140000 1000000 512
#str_chunks CertificateChecks.KernelRouteP.TStab
  CFSG.EvenSporadicStandard.TwoFi22.DS81.RouteP.Model.Native.coverStabText 140000 1000000 512
#str_chunks CertificateChecks.KernelRouteP.TN0
  CFSG.EvenSporadicStandard.TwoFi22.DS81.RouteP.Model.Native.coverN0Text 140000 1000000 512
#str_chunks CertificateChecks.KernelRouteP.TY332
  CFSG.EvenSporadicStandard.TwoFi22.DS81.RouteP.Model.Native.coverY332Text 140000 1000000 512
#str_chunks CertificateChecks.KernelRouteP.TWords
  CFSG.EvenSporadicStandard.TwoFi22.DS81.RouteP.Model.Native.planeWordsText 140000 1000000 512
#str_chunks CertificateChecks.KernelRouteP.TBase
  CFSG.EvenSporadicStandard.TwoFi22.DS81.RouteP.Model.Native.baseText 140000 1000000 512

namespace CertificateChecks.KernelRouteP

open CFSG.KC.RouteP CFSG.KS.RouteP CFSG.EvenSporadicStandard.TwoFi22.DS81.RouteP.Model.Native

@[expose] noncomputable def presLinesK : List (List Int) :=
  prefLinesL ['L', ' '] TPres.chars ++ prefLinesL ['L', ' '] TBr.chars

@[expose] noncomputable def bridgeGensLinesK : List (List Int) := prefLinesL ['L', ' '] TBrG.chars

@[expose] noncomputable def objLinesK : List (List Int) :=
  prefLinesL ['L', ' '] TStab.chars ++ prefLinesL ['L', ' '] TN0.chars

@[expose] noncomputable def y332LinesK : List (List Int) :=
  prefLinesL ['L', ' '] TStab.chars ++ prefLinesL ['L', ' '] TY332.chars

@[expose] noncomputable def planeDWordsK : List (List Int) := prefLinesL ['D', ' '] TWords.chars

@[expose] noncomputable def planeUWordK : List Int := (prefLinesL ['U', ' '] TWords.chars).headD []

@[expose] noncomputable def planeVWordK : List Int := (prefLinesL ['V', ' '] TWords.chars).headD []

theorem ok_pres : prefOKL ['L', ' '] TPres.chars = true := by decide +kernel
theorem ok_br : prefOKL ['L', ' '] TBr.chars = true := by decide +kernel
theorem ok_brg : prefOKL ['L', ' '] TBrG.chars = true := by decide +kernel
theorem ok_stab : prefOKL ['L', ' '] TStab.chars = true := by decide +kernel
theorem ok_n0 : prefOKL ['L', ' '] TN0.chars = true := by decide +kernel
theorem ok_y332 : prefOKL ['L', ' '] TY332.chars = true := by decide +kernel
theorem ok_wd : prefOKL ['D', ' '] TWords.chars = true := by decide +kernel
theorem ok_wu : prefOKL ['U', ' '] TWords.chars = true := by decide +kernel
theorem ok_wv : prefOKL ['V', ' '] TWords.chars = true := by decide +kernel

theorem lines_L (s : String) (cs : List Char) (e : s = String.ofList cs)
    (h : prefOKL ['L', ' '] cs = true) : slpLines s = (prefLinesL ['L', ' '] cs).toArray := by
  rw [e]
  exact slpLines_ofList cs h

theorem presLines_eq : slpLines presText ++ slpLines bridgeText = presLinesK.toArray := by
  rw [lines_L _ _ TPres.eq ok_pres, lines_L _ _ TBr.eq ok_br, presLinesK, List.append_toArray]

theorem bridgeGensLines_eq : slpLines bridgeGensText = bridgeGensLinesK.toArray :=
  lines_L _ _ TBrG.eq ok_brg

theorem objLines_eq : objLines () = objLinesK.toArray := by
  unfold objLines
  rw [lines_L _ _ TStab.eq ok_stab, lines_L _ _ TN0.eq ok_n0, objLinesK, List.append_toArray]

theorem y332Lines_eq : y332Lines () = y332LinesK.toArray := by
  unfold y332Lines
  rw [lines_L _ _ TStab.eq ok_stab, lines_L _ _ TY332.eq ok_y332, y332LinesK, List.append_toArray]

theorem words (pre : String) (p : List Char) (hp : pre.toList = p)
    (h : prefOKL p TWords.chars = true) :
    wordLines planeWordsText pre = (prefLinesL p TWords.chars).toArray := by
  rw [TWords.eq, wordLines_ofList pre _ (hp ▸ h), hp]

theorem planeDWords_eq : planeDWords () = planeDWordsK.toArray :=
  words "D " ['D', ' '] rfl ok_wd

theorem planeUWord_eq : planeUWord () = planeUWordK := by
  unfold planeUWord planeUWordK
  rw [words "U " ['U', ' '] rfl ok_wu]
  cases prefLinesL ['U', ' '] TWords.chars <;> rfl

theorem planeVWord_eq : planeVWord () = planeVWordK := by
  unfold planeVWord planeVWordK
  rw [words "V " ['V', ' '] rfl ok_wv]
  cases prefLinesL ['V', ' '] TWords.chars <;> rfl

end CertificateChecks.KernelRouteP
