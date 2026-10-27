module

public import Certificates.Kernel.J2Cover.M22Out
public import Certificates.Kernel.Fin76bAut.Data
public import Certificates.Data.Kernel.Fin76bAut
public import Certificates.Data.Kernel.TC2Outer0
public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.TC2J2Check
import CFSG.Certificates.Kernel.Common.Harness
public import CFSG.LocalAnalysis.EvenSporadicStandard.Common
public import CFSG.LocalAnalysis.ZStar.BrauerSylowFusion
public import CFSG.LocalAnalysis.ZStar.PrincipalBlockTraceApplication
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Isaacs.VII.lemma_7_7
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Basic

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelJ2Cover

open CFSG.KC.Enum CFSG.KS CFSG.KS.EAut CFSG.ComponentClassification.J2Cover.Models
open CFSG.EvenSporadicStandard.Fin76b CFSG.EvenSporadicStandard.Fin76b.J2
open CertificateChecks.KernelFin76bAut (ET)

@[expose] noncomputable def mulXK (a d : ℕ) : ℕ :=
  if a < 128 then
    (if d < 128 then mtK a d else 128 + mtK a (d - 128))
  else
    (if d < 128 then 128 + mtK (a - 128) (betaIdx d) else mtK (a - 128) (betaIdx (d - 128)))

@[expose] def EL25880 : List ℕ :=
  [85, 88, 11, 1, 81, 94, 18, 32, 40, 57, 124, 115, 80, 95, 86, 93, 46, 122, 108, 117, 70, 83, 23,
    62, 0, 120, 37, 116, 123, 48, 119, 4]

@[expose] def SIG25880 : List ℕ :=
  [0, 11, 18, 1, 32, 57, 120, 117, 83, 40, 23, 122, 116, 93, 119, 115, 124, 48, 62, 123, 37, 4,
    88, 81, 85, 80, 95, 94, 70, 86, 108, 46]

@[expose] noncomputable def lab25880 : Bool :=
  (List.range 32).all (fun a => (List.range 32).all fun b =>
      SIG25880.getD (eMul ET a b) 0 == mulXK (SIG25880.getD a 0) (SIG25880.getD b 0)) &&
    SIG25880.all EL25880.contains && EL25880.all SIG25880.contains &&
    decide (SIG25880.length = 32) && decide SIG25880.Nodup &&
    SIG25880.getD 0 0 == 0 && SIG25880.getD 21 0 == 4

theorem kOuter25880 : CFSG.KC.TC2Outer.outerCheck0 256 innX mulXK 4 = true := by quickRfl

theorem kEL25880 : decide (TableX.eListX 256 innX mulXK 4 = EL25880) = true := by quickRfl

theorem kLab25880 : lab25880 = true := by quickRfl

theorem kFix25880 : EL25880.all (fun a => decide (a < 128) &&
    (!(mulXK a a == 0 && a != 0) || fixP (ELT a) == 11)) = true := by quickRfl

end CertificateChecks.KernelJ2Cover

end
