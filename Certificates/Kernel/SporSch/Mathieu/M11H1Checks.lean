module

public import Certificates.Kernel.SporSch.Mathieu.M11H1Data
public import Certificates.Data.Kernel.Child3
public import Certificates.Data.Kernel.J2Cover
public import Certificates.Data.Kernel.Spor.M11
public import CFSG.LocalAnalysis.EvenSporadicStandard.M11Std.HypOneInputs
import CFSG.Certificates.Kernel.Common.Harness
public import CFSG.LocalAnalysis.EvenSporadicStandard.HypOne.Check
public import CFSG.LocalAnalysis.EvenSporadicStandard.HypOne.Generic
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Huppert.IV.theorem_3_3
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFchapter1section3.Basic
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFchapter2.Basic
public import CFSG.Walter.JRFacts

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSporSch.M11H1

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KS.M11 CFSG.KS.SporSch.MOC
open CFSG.KC.Child3 CFSG.EvenSporadicStandard.M11Std CertificateChecks.KernelSporSch.M11OC

theorem kP : allN centGens1.length (fun j => permOK 11 4 (mask 4) (11 * 4) (M11C1.S j) (M11C1.SI j)) = true := by
  quickRfl

theorem kC : allN 4 (fun j => bAnd(canonK 11 4 (mask 4) (11 * 4) (M11C1.S j),
    canonK 11 4 (mask 4) (11 * 4) (M11C1.SI j))) = true := by quickRfl

theorem kW : allN fourWords1.length (fun i => bAnd(lettersK centGens1.length (fourWords1.getD i []),
    Nat.beq (wordK 11 4 (mask 4) (pidn 11 4) M11C1.S M11C1.SI (fourWords1.getD i []))
      (M11H1R.E (lget M11H1R.OFF i)))) = true := by quickRfl

theorem kO : allN fourWords1.length (fun i =>
    bAnd(canonK 11 4 (mask 4) (11 * 4) (M11H1R.E (lget M11H1R.OFF i)),
      ordIs 11 4 (mask 4) (pidn 11 4) (M11H1R.E (lget M11H1R.OFF i)) (4 - 1))) = true := by
  quickRfl

theorem kOff : offOK M11H1R.CS M11H1R.OFF M11H1R.N = true := by quickRfl

theorem kPos : CFSG.KC.J2Cover.allL (fun c => Nat.blt 0 c) M11H1R.CS = true := by quickRfl

theorem kR : allN M11H1R.N (repK 11 4 M11C1.S M11C1.SI 4 M11H1R.CS M11H1R.OFF M11H1R.CI M11H1R.E
    M11H1R.P M11H1R.L M11H1R.K M11H1R.S M11H1R.SI M11H1R.N 400) = true := by quickRfl

end CertificateChecks.KernelSporSch.M11H1

end
