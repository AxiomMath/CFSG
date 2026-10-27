module

public import Certificates.Kernel.SporSch.Mathieu.M22H1Data
public import Certificates.Data.Kernel.Child3
public import Certificates.Data.Kernel.J2Cover
public import Certificates.Data.Kernel.Spor.M11
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSporSch.M22H1

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KS.M11 CFSG.KS.SporSch.MOC
open CFSG.KC.Child3 CFSG.EvenSporadicStandard.HypOne.M22 CertificateChecks.KernelSporSch.M22OC
open CFSG.Sporadic.Schreier

@[expose] noncomputable def pp (x y : Nat) : Bool := permOK 22 5 (mask 5) (22 * 5) x y

@[expose] noncomputable def cn (x : Nat) : Bool := canonK 22 5 (mask 5) (22 * 5) x

@[expose] noncomputable def pm (x y : Nat) : Nat := pcomp 22 5 (mask 5) x y

@[expose] noncomputable def pi (x : Nat) : Nat := pinvS 22 5 (mask 5) x

@[expose] noncomputable def inv2K (x : Nat) : Bool :=
  bAnd(cn x, ordIs 22 5 (mask 5) (pidn 22 5) x (2 - 1))

@[expose] noncomputable def ab (wd : List Int) : Nat :=
  abWordK 22 5 (mask 5) (pidn 22 5) (M22Q.S 0) (M22Q.SI 0) (M22Q.S 1) (M22Q.SI 1) wd

@[expose] noncomputable def GA3 (j : Nat) : Nat :=
  bif Nat.beq j 0 then M22Q.S 0 else bif Nat.beq j 1 then M22Q.S 1 else M22D

@[expose] noncomputable def GA3I (j : Nat) : Nat :=
  bif Nat.beq j 0 then M22Q.SI 0 else bif Nat.beq j 1 then M22Q.SI 1 else pi M22D

theorem kGA3 : allN 3 (fun j => bAnd(pp (GA3 j) (GA3I j), bAnd(cn (GA3 j), cn (GA3I j)))) =
    true := by quickRfl

theorem kZ1 : lettersK 3 zWordA = true := by quickRfl

theorem kZ2 : Nat.beq (wordK 22 5 (mask 5) (pidn 22 5) GA3 GA3I zWordA) (M22KA.S 3) = true := by
  quickRfl

theorem kGenA : allN 3 (fun j => Nat.beq (M22KA.S j) (M22C1.S j)) = true := by quickRfl

theorem kGenO1 : allN 3 (fun j => Nat.beq (M22KO1.S j) (M22OC1.S j)) = true := by quickRfl

theorem kGenO1r : Nat.beq (M22KO1.S 3) RO0 = true := by quickRfl

theorem kGenO2 : allN 3 (fun j => Nat.beq (M22KO2.S j) (M22OC2.S j)) = true := by quickRfl

theorem kGenO2r : Nat.beq (M22KO2.S 3) RO1 = true := by quickRfl

theorem kZcomm : commK 22 5 (mask 5) (22 * 5) (M22KA.S 3) (M22Q.S 0) = true := by quickRfl

theorem kZcn : cn (M22KA.S 3) = true := by quickRfl

theorem kZsift : (!siftK 22 5 (mask 5) (22 * 5) (pidn 22 5) M22Q.LR M22Q.TRI M22Q.BP 5 0
    (M22KA.S 3)) = true := by quickRfl

theorem kPI : allN 3 (fun j => bAnd(pp (M22C1.S j) (M22C1.SI j),
    bAnd(cn (M22C1.S j), cn (M22C1.SI j)))) = true := by quickRfl

theorem kWI : allN innerFourWords.length (fun i => bAnd(lettersK 3 (innerFourWords.getD i []),
    Nat.beq (wordK 22 5 (mask 5) (pidn 22 5) M22C1.S M22C1.SI (innerFourWords.getD i []))
      (M22H1RI.E (lget M22H1RI.OFF i)))) = true := by quickRfl

theorem kOI : allN innerFourWords.length (fun i => bAnd(cn (M22H1RI.E (lget M22H1RI.OFF i)),
    ordIs 22 5 (mask 5) (pidn 22 5) (M22H1RI.E (lget M22H1RI.OFF i)) (4 - 1))) = true := by
  quickRfl

theorem kOffI : offOK M22H1RI.CS M22H1RI.OFF M22H1RI.N = true := by quickRfl

theorem kPosI : CFSG.KC.J2Cover.allL (fun c => Nat.blt 0 c) M22H1RI.CS = true := by quickRfl

theorem kRI : allN M22H1RI.N (repK 22 5 M22C1.S M22C1.SI 3 M22H1RI.CS M22H1RI.OFF M22H1RI.CI
    M22H1RI.E M22H1RI.P M22H1RI.L M22H1RI.K M22H1RI.S M22H1RI.SI M22H1RI.N 4000) = true := by
  quickRfl

theorem kPA : allN 4 (fun j => bAnd(pp (M22KA.S j) (M22KA.SI j),
    bAnd(cn (M22KA.S j), cn (M22KA.SI j)))) = true := by quickRfl

theorem kWA : allN kFourWordsA.length (fun i => bAnd(lettersK 4 (kFourWordsA.getD i []),
    Nat.beq (wordK 22 5 (mask 5) (pidn 22 5) M22KA.S M22KA.SI (kFourWordsA.getD i []))
      (M22H1RA.E (lget M22H1RA.OFF i)))) = true := by quickRfl

theorem kOA : allN kFourWordsA.length (fun i => bAnd(cn (M22H1RA.E (lget M22H1RA.OFF i)),
    ordIs 22 5 (mask 5) (pidn 22 5) (M22H1RA.E (lget M22H1RA.OFF i)) (4 - 1))) = true := by
  quickRfl

theorem kOffA : offOK M22H1RA.CS M22H1RA.OFF M22H1RA.N = true := by quickRfl

theorem kPosA : CFSG.KC.J2Cover.allL (fun c => Nat.blt 0 c) M22H1RA.CS = true := by quickRfl

theorem kRA : allN M22H1RA.N (repK 22 5 M22KA.S M22KA.SI 4 M22H1RA.CS M22H1RA.OFF M22H1RA.CI
    M22H1RA.E M22H1RA.P M22H1RA.L M22H1RA.K M22H1RA.S M22H1RA.SI M22H1RA.N 4000) = true := by
  quickRfl

theorem kPO1 : allN 4 (fun j => bAnd(pp (M22KO1.S j) (M22KO1.SI j),
    bAnd(cn (M22KO1.S j), cn (M22KO1.SI j)))) = true := by quickRfl

theorem kWO1 : allN kFourWordsO1.length (fun i => bAnd(lettersK 4 (kFourWordsO1.getD i []),
    Nat.beq (wordK 22 5 (mask 5) (pidn 22 5) M22KO1.S M22KO1.SI (kFourWordsO1.getD i []))
      (M22H1RO1.E (lget M22H1RO1.OFF i)))) = true := by quickRfl

theorem kOO1 : allN kFourWordsO1.length (fun i => bAnd(cn (M22H1RO1.E (lget M22H1RO1.OFF i)),
    ordIs 22 5 (mask 5) (pidn 22 5) (M22H1RO1.E (lget M22H1RO1.OFF i)) (4 - 1))) = true := by
  quickRfl

theorem kOffO1 : offOK M22H1RO1.CS M22H1RO1.OFF M22H1RO1.N = true := by quickRfl

theorem kPosO1 : CFSG.KC.J2Cover.allL (fun c => Nat.blt 0 c) M22H1RO1.CS = true := by quickRfl

theorem kRO1 : allN M22H1RO1.N (repK 22 5 M22KO1.S M22KO1.SI 4 M22H1RO1.CS M22H1RO1.OFF
    M22H1RO1.CI M22H1RO1.E M22H1RO1.P M22H1RO1.L M22H1RO1.K M22H1RO1.S M22H1RO1.SI M22H1RO1.N
    4000) = true := by
  quickRfl

theorem kPO2 : allN 4 (fun j => bAnd(pp (M22KO2.S j) (M22KO2.SI j),
    bAnd(cn (M22KO2.S j), cn (M22KO2.SI j)))) = true := by quickRfl

theorem kWO2 : allN kFourWordsO2.length (fun i => bAnd(lettersK 4 (kFourWordsO2.getD i []),
    Nat.beq (wordK 22 5 (mask 5) (pidn 22 5) M22KO2.S M22KO2.SI (kFourWordsO2.getD i []))
      (M22H1RO2.E (lget M22H1RO2.OFF i)))) = true := by quickRfl

theorem kOO2 : allN kFourWordsO2.length (fun i => bAnd(cn (M22H1RO2.E (lget M22H1RO2.OFF i)),
    ordIs 22 5 (mask 5) (pidn 22 5) (M22H1RO2.E (lget M22H1RO2.OFF i)) (4 - 1))) = true := by
  quickRfl

theorem kOffO2 : offOK M22H1RO2.CS M22H1RO2.OFF M22H1RO2.N = true := by quickRfl

theorem kPosO2 : CFSG.KC.J2Cover.allL (fun c => Nat.blt 0 c) M22H1RO2.CS = true := by quickRfl

theorem kRO2 : allN M22H1RO2.N (repK 22 5 M22KO2.S M22KO2.SI 4 M22H1RO2.CS M22H1RO2.OFF
    M22H1RO2.CI M22H1RO2.E M22H1RO2.P M22H1RO2.L M22H1RO2.K M22H1RO2.S M22H1RO2.SI M22H1RO2.N
    4000) = true := by
  quickRfl

theorem kA1 : abOK wordE1 = true := by quickRfl
theorem kA2 : abOK wordE2 = true := by quickRfl
theorem kA3 : abOK wordE3 = true := by quickRfl
theorem kAL1 : abOK wordL1 = true := by quickRfl
theorem kAL2 : abOK wordL2 = true := by quickRfl

theorem kC12 : commK 22 5 (mask 5) (22 * 5) (ab wordE1) (ab wordE2) = true := by quickRfl
theorem kC13 : commK 22 5 (mask 5) (22 * 5) (ab wordE1) (ab wordE3) = true := by quickRfl
theorem kC23 : commK 22 5 (mask 5) (22 * 5) (ab wordE2) (ab wordE3) = true := by quickRfl

theorem kO1 : inv2K (ab wordE1) = true := by quickRfl
theorem kO2 : inv2K (ab wordE2) = true := by quickRfl
theorem kO3 : inv2K (ab wordE3) = true := by quickRfl
theorem kO12 : inv2K (pm (ab wordE1) (ab wordE2)) = true := by quickRfl
theorem kO13 : inv2K (pm (ab wordE1) (ab wordE3)) = true := by quickRfl
theorem kO23 : inv2K (pm (ab wordE2) (ab wordE3)) = true := by quickRfl
theorem kO123 : inv2K (pm (pm (ab wordE1) (ab wordE2)) (ab wordE3)) = true := by quickRfl

theorem kPL1 : pp (ab wordL1) (pi (ab wordL1)) = true := by quickRfl
theorem kPL2 : pp (ab wordL2) (pi (ab wordL2)) = true := by quickRfl
theorem kPR0 : pp RO0 (pi RO0) = true := by quickRfl
theorem kPR1 : pp RO1 (pi RO1) = true := by quickRfl

theorem kF1 : inv2K (pm (pm (pm (ab wordL1) RO0) (pi (ab wordL1))) (pi RO0)) = true := by quickRfl
theorem kF2 : inv2K (pm (pm (pm (ab wordL2) RO1) (pi (ab wordL2))) (pi RO1)) = true := by quickRfl

end CertificateChecks.KernelSporSch.M22H1

end
