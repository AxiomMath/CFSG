module

public import Certificates.Kernel.SporSch.Mathieu.M23H1Data
public import Certificates.Data.Kernel.Child3
public import Certificates.Data.Kernel.J2Cover
public import Certificates.Data.Kernel.Spor.M11
public import CFSG.LocalAnalysis.EvenSporadicStandard.HypOne.M23Inputs
import CFSG.Certificates.Kernel.Common.Harness
public import CFSG.LocalAnalysis.EvenSporadicStandard.HypOne.Generic
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Huppert.IV.theorem_3_3
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFchapter1section3.Basic
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFchapter2.Basic
public import CFSG.Walter.JRFacts

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSporSch.M23H1

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KS.M11 CFSG.KS.SporSch.MOC
open CFSG.KC.Child3 CFSG.EvenSporadicStandard.HypOne.M23

theorem cOne23 : canonK 23 5 (mask 5) (23 * 5) One23 = true := by quickRfl

theorem kP : allN centGens1.length (fun j => permOK 23 5 (mask 5) (23 * 5) (M23C1.S j) (M23C1.SI j)) = true := by
  quickRfl

theorem kC : allN 4 (fun j => bAnd(canonK 23 5 (mask 5) (23 * 5) (M23C1.S j),
    canonK 23 5 (mask 5) (23 * 5) (M23C1.SI j))) = true := by quickRfl

theorem kW : allN fourWords1.length (fun i => bAnd(lettersK centGens1.length (fourWords1.getD i []),
    Nat.beq (wordK 23 5 (mask 5) (pidn 23 5) M23C1.S M23C1.SI (fourWords1.getD i []))
      (M23H1R.E (lget M23H1R.OFF i)))) = true := by quickRfl

theorem kO : allN fourWords1.length (fun i =>
    bAnd(canonK 23 5 (mask 5) (23 * 5) (M23H1R.E (lget M23H1R.OFF i)),
      ordIs 23 5 (mask 5) (pidn 23 5) (M23H1R.E (lget M23H1R.OFF i)) (4 - 1))) = true := by
  quickRfl

theorem kOff : offOK M23H1R.CS M23H1R.OFF M23H1R.N = true := by quickRfl

theorem kPos : CFSG.KC.J2Cover.allL (fun c => Nat.blt 0 c) M23H1R.CS = true := by quickRfl

theorem kR : allN M23H1R.N (repK 23 5 M23C1.S M23C1.SI 4 M23H1R.CS M23H1R.OFF M23H1R.CI M23H1R.E
    M23H1R.P M23H1R.L M23H1R.K M23H1R.S M23H1R.SI M23H1R.N 4000) = true := by quickRfl

@[expose] noncomputable def E1P : Nat :=
  abWordK 23 5 (mask 5) (pidn 23 5) (M23Q.S 0) (M23Q.SI 0) (M23Q.S 1) (M23Q.SI 1) wordE1

@[expose] noncomputable def E2P : Nat :=
  abWordK 23 5 (mask 5) (pidn 23 5) (M23Q.S 0) (M23Q.SI 0) (M23Q.S 1) (M23Q.SI 1) wordE2

@[expose] noncomputable def E3P : Nat :=
  abWordK 23 5 (mask 5) (pidn 23 5) (M23Q.S 0) (M23Q.SI 0) (M23Q.S 1) (M23Q.SI 1) wordE3

@[expose] noncomputable def inv2K (x : Nat) : Bool :=
  bAnd(canonK 23 5 (mask 5) (23 * 5) x, ordIs 23 5 (mask 5) (pidn 23 5) x (2 - 1))

@[expose] noncomputable def pm (x y : Nat) : Nat := pcomp 23 5 (mask 5) x y

theorem kA1 : abOK wordE1 = true := by quickRfl
theorem kA2 : abOK wordE2 = true := by quickRfl
theorem kA3 : abOK wordE3 = true := by quickRfl

theorem kC12 : commK 23 5 (mask 5) (23 * 5) E1P E2P = true := by quickRfl
theorem kC13 : commK 23 5 (mask 5) (23 * 5) E1P E3P = true := by quickRfl
theorem kC23 : commK 23 5 (mask 5) (23 * 5) E2P E3P = true := by quickRfl

theorem kO1 : inv2K E1P = true := by quickRfl
theorem kO2 : inv2K E2P = true := by quickRfl
theorem kO3 : inv2K E3P = true := by quickRfl
theorem kO12 : inv2K (pm E1P E2P) = true := by quickRfl
theorem kO13 : inv2K (pm E1P E3P) = true := by quickRfl
theorem kO23 : inv2K (pm E2P E3P) = true := by quickRfl
theorem kO123 : inv2K (pm (pm E1P E2P) E3P) = true := by quickRfl

end CertificateChecks.KernelSporSch.M23H1

end
