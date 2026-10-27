module

public import Certificates.Kernel.SporSch.Mathieu.M11WData
public import Certificates.Data.Kernel.SporSch.OddWit
public import Certificates.Data.Kernel.SporSch.MathieuBT
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSporSch.M11W

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.M11 CFSG.KS.SporSch.MOC CFSG.KS.SporSch.MBT
open CFSG.KS.SporSch.OddWit CFSG.Sporadic.Schreier
open CertificateChecks.KernelSporSch CertificateChecks.KernelSporSch.M11OC

@[expose] noncomputable def U : Nat := (M11WCK.getD 0 clsD0).R

@[expose] noncomputable def rowsK : List (Nat × Nat × List Nat) :=
  [(3, 9, OG), (5, 5, OG), (11, 11, [])]

theorem bOG : allN 2 (fun i => bAnd(abOK (Certificates.Odd87F3.M11.oddWords.getD i []),
    Nat.beq (abWordK 11 4 (mask 4) (pidn 11 4) (M11Q.S 0) (M11Q.SI 0) (M11Q.S 1) (M11Q.SI 1)
      (Certificates.Odd87F3.M11.oddWords.getD i [])) (OG.getD i 0))) = true := by quickRfl

theorem bA0 : bAnd(abOK Certificates.CF67.M11.wa, Nat.beq (abWordK 11 4 (mask 4) (pidn 11 4)
    (M11Q.S 0) (M11Q.SI 0) (M11Q.S 1) (M11Q.SI 1) Certificates.CF67.M11.wa) A0) = true := by
  quickRfl

theorem bB0 : bAnd(abOK Certificates.CF67.M11.wb, Nat.beq (abWordK 11 4 (mask 4) (pidn 11 4)
    (M11Q.S 0) (M11Q.SI 0) (M11Q.S 1) (M11Q.SI 1) Certificates.CF67.M11.wb) B0) = true := by
  quickRfl

theorem bH : allN 3 (fun j => bAnd(abOK (CFSG.KS.SporSch.MathieuC3.m11Words.getD j []),
    Nat.beq (abWordK 11 4 (mask 4) (pidn 11 4) (M11Q.S 0) (M11Q.SI 0) (M11Q.S 1) (M11Q.SI 1)
      (CFSG.KS.SporSch.MathieuC3.m11Words.getD j [])) (M11CH.S j))) = true := by quickRfl

theorem repU : Nat.beq U R0 = true := by quickRfl

theorem uSq : Nat.beq (pcomp 11 4 (mask 4) U U) (pidn 11 4) = true := by quickRfl

theorem ogComm : allN 2 (fun i => Nat.beq (pcomp 11 4 (mask 4) U (OG.getD i 0))
    (pcomp 11 4 (mask 4) (OG.getD i 0) U)) = true := by quickRfl

theorem ogPow : allN 2 (fun i => Nat.beq (powK 11 4 (mask 4) (pidn 11 4) (OG.getD i 0) 495)
    (pidn 11 4)) = true := by quickRfl

theorem f3 : invCandK 11 4 rowsK (pinvS 11 4 (mask 4) U) (M11WCK.getD 0 clsD0) = true := by
  quickRfl

theorem abFacts : Nat.beq (powK 11 4 (mask 4) (pidn 11 4) A0 3) (pidn 11 4) = true ∧
    Nat.beq (powK 11 4 (mask 4) (pidn 11 4) B0 3) (pidn 11 4) = true ∧
    Nat.beq (pcomp 11 4 (mask 4) A0 B0) (pcomp 11 4 (mask 4) B0 A0) = true ∧
    (Nat.beq A0 (pidn 11 4)).not = true ∧
    allN 3 (fun i => (Nat.beq B0 (powK 11 4 (mask 4) (pidn 11 4) A0 i)).not) = true :=
  ⟨by quickRfl, by quickRfl, by quickRfl, by quickRfl, by quickRfl⟩

theorem abShr : Nat.beq (Nat.shiftRight A0 (11 * 4)) 0 = true ∧
    Nat.beq (Nat.shiftRight B0 (11 * 4)) 0 = true := ⟨by quickRfl, by quickRfl⟩

theorem hComm : allN 3 (fun j => Nat.beq (pcomp 11 4 (mask 4) (M11CH.S j) A0)
    (pcomp 11 4 (mask 4) A0 (M11CH.S j))) = true := by quickRfl

theorem hOrd : Nat.beq (ordK M11CH.LR 2) 18 = true := by quickRfl

theorem cent : Nat.beq (btK 11 4 (mask 4) (11 * 4) M11Q.BP 4 M11Q.LR M11Q.TR M11Q.TRI A0 A0) 18 =
    true := by quickRfl

theorem elems : allN 18 (fun j => powCommK 11 4 B0 9
    (elemK 11 4 (mask 4) (11 * 4) (pidn 11 4) M11CH.LR M11CH.TR 2 j)) = true := by quickRfl

end CertificateChecks.KernelSporSch.M11W

end
