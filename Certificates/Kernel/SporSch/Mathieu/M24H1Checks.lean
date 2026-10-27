module

public import Certificates.Kernel.SporSch.Mathieu.M24H1Data
public import Certificates.Data.Kernel.Child3
public import Certificates.Data.Kernel.J2Cover
public import Certificates.Data.Kernel.Spor.M11
public import CFSG.LocalAnalysis.EvenSporadicStandard.HypOne.M24Inputs
import CFSG.Certificates.Kernel.Common.Harness
public import CFSG.LocalAnalysis.EvenSporadicStandard.HypOne.Generic
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Huppert.IV.theorem_3_3
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFchapter1section3.Basic
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFchapter2.Basic
public import CFSG.Walter.JRFacts

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSporSch.M24H1

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KS.M11 CFSG.KS.SporSch.MOC
open CFSG.KC.Child3 CFSG.EvenSporadicStandard.HypOne.M24

theorem cOne24 : canonK 24 5 (mask 5) (24 * 5) One24 = true := by quickRfl

theorem kP1 : allN centGens1.length (fun j => permOK 24 5 (mask 5) (24 * 5) (M24C1.S j) (M24C1.SI j)) = true := by
  quickRfl

theorem kC1 : allN 3 (fun j => bAnd(canonK 24 5 (mask 5) (24 * 5) (M24C1.S j),
    canonK 24 5 (mask 5) (24 * 5) (M24C1.SI j))) = true := by quickRfl

theorem kW1 : allN fourWords1.length (fun i => bAnd(lettersK centGens1.length (fourWords1.getD i []),
    Nat.beq (wordK 24 5 (mask 5) (pidn 24 5) M24C1.S M24C1.SI (fourWords1.getD i []))
      (M24H1R1.E (lget M24H1R1.OFF i)))) = true := by quickRfl

theorem kO1 : allN fourWords1.length (fun i =>
    bAnd(canonK 24 5 (mask 5) (24 * 5) (M24H1R1.E (lget M24H1R1.OFF i)),
      ordIs 24 5 (mask 5) (pidn 24 5) (M24H1R1.E (lget M24H1R1.OFF i)) (4 - 1))) = true := by
  quickRfl

theorem kOff1 : offOK M24H1R1.CS M24H1R1.OFF M24H1R1.N = true := by quickRfl

theorem kPos1 : CFSG.KC.J2Cover.allL (fun c => Nat.blt 0 c) M24H1R1.CS = true := by quickRfl

theorem kR1 : allN M24H1R1.N (repK 24 5 M24C1.S M24C1.SI 3 M24H1R1.CS M24H1R1.OFF M24H1R1.CI
    M24H1R1.E M24H1R1.P M24H1R1.L M24H1R1.K M24H1R1.S M24H1R1.SI M24H1R1.N 4000) = true := by
  quickRfl

theorem kP2 : allN centGens2.length (fun j => permOK 24 5 (mask 5) (24 * 5) (M24C2.S j) (M24C2.SI j)) = true := by
  quickRfl

theorem kC2 : allN 2 (fun j => bAnd(canonK 24 5 (mask 5) (24 * 5) (M24C2.S j),
    canonK 24 5 (mask 5) (24 * 5) (M24C2.SI j))) = true := by quickRfl

theorem kW2 : allN fourWords2.length (fun i => bAnd(lettersK centGens2.length (fourWords2.getD i []),
    Nat.beq (wordK 24 5 (mask 5) (pidn 24 5) M24C2.S M24C2.SI (fourWords2.getD i []))
      (M24H1R2.E (lget M24H1R2.OFF i)))) = true := by quickRfl

theorem kO2 : allN fourWords2.length (fun i =>
    bAnd(canonK 24 5 (mask 5) (24 * 5) (M24H1R2.E (lget M24H1R2.OFF i)),
      ordIs 24 5 (mask 5) (pidn 24 5) (M24H1R2.E (lget M24H1R2.OFF i)) (4 - 1))) = true := by
  quickRfl

theorem kOff2 : offOK M24H1R2.CS M24H1R2.OFF M24H1R2.N = true := by quickRfl

theorem kPos2 : CFSG.KC.J2Cover.allL (fun c => Nat.blt 0 c) M24H1R2.CS = true := by quickRfl

theorem kR2 : allN M24H1R2.N (repK 24 5 M24C2.S M24C2.SI 2 M24H1R2.CS M24H1R2.OFF M24H1R2.CI
    M24H1R2.E M24H1R2.P M24H1R2.L M24H1R2.K M24H1R2.S M24H1R2.SI M24H1R2.N 4000) = true := by
  quickRfl

@[expose] noncomputable def E1P : Nat :=
  abWordK 24 5 (mask 5) (pidn 24 5) (M24Q.S 0) (M24Q.SI 0) (M24Q.S 1) (M24Q.SI 1) wordE1

@[expose] noncomputable def E2P : Nat :=
  abWordK 24 5 (mask 5) (pidn 24 5) (M24Q.S 0) (M24Q.SI 0) (M24Q.S 1) (M24Q.SI 1) wordE2

@[expose] noncomputable def E3P : Nat :=
  abWordK 24 5 (mask 5) (pidn 24 5) (M24Q.S 0) (M24Q.SI 0) (M24Q.S 1) (M24Q.SI 1) wordE3

@[expose] noncomputable def inv2K (x : Nat) : Bool :=
  bAnd(canonK 24 5 (mask 5) (24 * 5) x, ordIs 24 5 (mask 5) (pidn 24 5) x (2 - 1))

@[expose] noncomputable def pm (x y : Nat) : Nat := pcomp 24 5 (mask 5) x y

theorem kA1 : abOK wordE1 = true := by quickRfl
theorem kA2 : abOK wordE2 = true := by quickRfl
theorem kA3 : abOK wordE3 = true := by quickRfl

theorem kC12 : commK 24 5 (mask 5) (24 * 5) E1P E2P = true := by quickRfl
theorem kC13 : commK 24 5 (mask 5) (24 * 5) E1P E3P = true := by quickRfl
theorem kC23 : commK 24 5 (mask 5) (24 * 5) E2P E3P = true := by quickRfl

theorem kE1 : inv2K E1P = true := by quickRfl
theorem kE2 : inv2K E2P = true := by quickRfl
theorem kE3 : inv2K E3P = true := by quickRfl
theorem kE12 : inv2K (pm E1P E2P) = true := by quickRfl
theorem kE13 : inv2K (pm E1P E3P) = true := by quickRfl
theorem kE23 : inv2K (pm E2P E3P) = true := by quickRfl
theorem kE123 : inv2K (pm (pm E1P E2P) E3P) = true := by quickRfl

end CertificateChecks.KernelSporSch.M24H1

end
