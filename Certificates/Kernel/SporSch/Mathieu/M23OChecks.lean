module

public import Certificates.Kernel.SporSch.Mathieu.M23OData
public import Certificates.Kernel.SporSch.Mathieu.M23Cls
public import Certificates.Data.Kernel.SporSch.OddWit
public import Certificates.Data.Kernel.SporSch.MathieuBT
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSporSch.M23W

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.M11 CFSG.KS.SporSch.MOC CFSG.KS.SporSch.MBT
open CFSG.KS.SporSch.OddWit CFSG.KS.SporSch.M23C3 CFSG.Sporadic.Schreier
open CertificateChecks.KernelSporSch CertificateChecks.KernelSporSch.M23OC

@[expose] noncomputable def U : Nat := (M23CK.getD 0 clsD0).R

@[expose] noncomputable def rowsK : List (Nat × Nat × List Nat) :=
  [(3, 9, OG3), (5, 5, OG5), (7, 7, []), (11, 11, []), (23, 23, [])]

theorem bOG3 : allN 2 (fun i => bAnd(abOK (Certificates.Odd87F3.M23.oddWords3.getD i []),
    Nat.beq (abWordK 23 5 (mask 5) (pidn 23 5) (M23Q.S 0) (M23Q.SI 0) (M23Q.S 1) (M23Q.SI 1)
      (Certificates.Odd87F3.M23.oddWords3.getD i [])) (OG3.getD i 0))) = true := by quickRfl

theorem bOG5 : allN 3 (fun i => bAnd(abOK (Certificates.Odd87F3.M23.oddWords5.getD i []),
    Nat.beq (abWordK 23 5 (mask 5) (pidn 23 5) (M23Q.S 0) (M23Q.SI 0) (M23Q.S 1) (M23Q.SI 1)
      (Certificates.Odd87F3.M23.oddWords5.getD i [])) (OG5.getD i 0))) = true := by quickRfl

theorem bA0 : bAnd(abOK Certificates.CF67.M23.wa, Nat.beq (abWordK 23 5 (mask 5) (pidn 23 5)
    (M23Q.S 0) (M23Q.SI 0) (M23Q.S 1) (M23Q.SI 1) Certificates.CF67.M23.wa) A0) = true := by
  quickRfl

theorem bB0 : bAnd(abOK Certificates.CF67.M23.wb, Nat.beq (abWordK 23 5 (mask 5) (pidn 23 5)
    (M23Q.S 0) (M23Q.SI 0) (M23Q.S 1) (M23Q.SI 1) Certificates.CF67.M23.wb) B0) = true := by
  quickRfl

theorem bH : allN 3 (fun j => bAnd(abOK (c3Words.getD j []), Nat.beq (abWordK 23 5 (mask 5)
    (pidn 23 5) (M23Q.S 0) (M23Q.SI 0) (M23Q.S 1) (M23Q.SI 1) (c3Words.getD j []))
      (M23CH.S j))) = true := by quickRfl

theorem uSq : Nat.beq (pcomp 23 5 (mask 5) U U) (pidn 23 5) = true := by quickRfl

theorem uOrd : Nat.beq (ordC 23 5 (mask 5) U) 2 = true := by quickRfl

theorem ogComm : allN 2 (fun i => Nat.beq (pcomp 23 5 (mask 5) U (OG3.getD i 0))
      (pcomp 23 5 (mask 5) (OG3.getD i 0) U)) = true ∧
    allN 3 (fun i => Nat.beq (pcomp 23 5 (mask 5) U (OG5.getD i 0))
      (pcomp 23 5 (mask 5) (OG5.getD i 0) U)) = true := ⟨by quickRfl, by quickRfl⟩

theorem ogPow : allN 2 (fun i => Nat.beq (powK 23 5 (mask 5) (pidn 23 5) (OG3.getD i 0) 3)
      (pidn 23 5)) = true ∧
    allN 3 (fun i => Nat.beq (powK 23 5 (mask 5) (pidn 23 5) (OG5.getD i 0) 21)
      (pidn 23 5)) = true := ⟨by quickRfl, by quickRfl⟩

theorem f3 : invCandK 23 5 rowsK (pinvS 23 5 (mask 5) U) (M23CK.getD 0 clsD0) = true := by
  quickRfl

theorem abFacts : Nat.beq (powK 23 5 (mask 5) (pidn 23 5) A0 3) (pidn 23 5) = true ∧
    Nat.beq (powK 23 5 (mask 5) (pidn 23 5) B0 3) (pidn 23 5) = true ∧
    Nat.beq (pcomp 23 5 (mask 5) A0 B0) (pcomp 23 5 (mask 5) B0 A0) = true ∧
    (Nat.beq A0 (pidn 23 5)).not = true ∧
    allN 3 (fun i => (Nat.beq B0 (powK 23 5 (mask 5) (pidn 23 5) A0 i)).not) = true :=
  ⟨by quickRfl, by quickRfl, by quickRfl, by quickRfl, by quickRfl⟩

theorem abShr : Nat.beq (Nat.shiftRight A0 (23 * 5)) 0 = true ∧
    Nat.beq (Nat.shiftRight B0 (23 * 5)) 0 = true := ⟨by quickRfl, by quickRfl⟩

theorem hComm : allN 3 (fun j => Nat.beq (pcomp 23 5 (mask 5) (M23CH.S j) A0)
    (pcomp 23 5 (mask 5) A0 (M23CH.S j))) = true := by quickRfl

theorem hOrd : Nat.beq (ordK M23CH.LR 2) 180 = true := by quickRfl

theorem cent : Nat.beq (btK 23 5 (mask 5) (23 * 5) M23Q.BP 6 M23Q.LR M23Q.TR M23Q.TRI A0 A0) 180 =
    true := by quickRfl

theorem elems : allN 180 (fun j => powCommK 23 5 B0 9
    (elemK 23 5 (mask 5) (23 * 5) (pidn 23 5) M23CH.LR M23CH.TR 2 j)) = true := by quickRfl

end CertificateChecks.KernelSporSch.M23W

end
