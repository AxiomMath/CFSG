module

public import Certificates.Kernel.SporSch.Mathieu.M22WData
public import Certificates.Kernel.SporSch.Mathieu.M22Cls
public import Certificates.Kernel.SporSch.Mathieu.M22OData
public import Certificates.Data.Kernel.SporSch.OddWit
public import Certificates.Data.Kernel.SporSch.MathieuBT
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSporSch.M22W

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.M11 CFSG.KS.SporSch.MOC CFSG.KS.SporSch.MBT
open CFSG.KS.SporSch.OddWit CFSG.Sporadic.Schreier
open CertificateChecks.KernelSporSch CertificateChecks.KernelSporSch.M22OC

@[expose] noncomputable def UI : Nat := (M22CK.getD 0 clsD0).R

@[expose] noncomputable def UA : Nat := (M22OCL.getD 0 clsD0).R

@[expose] noncomputable def UB : Nat := (M22OCL.getD 1 clsD0).R

@[expose] noncomputable def rowsIK : List (Nat × Nat × List Nat) :=
  [(3, 9, OGI3), (5, 5, OGI5), (7, 7, []), (11, 11, [])]

@[expose] noncomputable def rowsAK : List (Nat × Nat × List Nat) :=
  [(3, 9, OGA3), (5, 5, OGA5), (7, 7, []), (11, 11, OGA11)]

@[expose] noncomputable def rowsBK : List (Nat × Nat × List Nat) :=
  [(3, 9, OGB3), (5, 5, []), (7, 7, []), (11, 11, [])]

theorem bOGI3 : allN 1 (fun i => bAnd(abOK (Certificates.Odd87F3.M22.oddWordsInn_3.getD i []),
    Nat.beq (abWordK 22 5 (mask 5) (pidn 22 5) (M22Q.S 0) (M22Q.SI 0) (M22Q.S 1) (M22Q.SI 1)
      (Certificates.Odd87F3.M22.oddWordsInn_3.getD i [])) (OGI3.getD i 0))) = true := by
  quickRfl

theorem bOGI5 : allN 2 (fun i => bAnd(abOK (Certificates.Odd87F3.M22.oddWordsInn_5.getD i []),
    Nat.beq (abWordK 22 5 (mask 5) (pidn 22 5) (M22Q.S 0) (M22Q.SI 0) (M22Q.S 1) (M22Q.SI 1)
      (Certificates.Odd87F3.M22.oddWordsInn_5.getD i [])) (OGI5.getD i 0))) = true := by
  quickRfl

theorem bOGA3 : allN 2 (fun i => bAnd(abOK (Certificates.Odd87F3.M22.oddWordsOut1_3.getD i []),
    Nat.beq (abWordK 22 5 (mask 5) (pidn 22 5) (M22Q.S 0) (M22Q.SI 0) (M22Q.S 1) (M22Q.SI 1)
      (Certificates.Odd87F3.M22.oddWordsOut1_3.getD i [])) (OGA3.getD i 0))) = true := by
  quickRfl

theorem bOGA5 : allN 3 (fun i => bAnd(abOK (Certificates.Odd87F3.M22.oddWordsOut1_5.getD i []),
    Nat.beq (abWordK 22 5 (mask 5) (pidn 22 5) (M22Q.S 0) (M22Q.SI 0) (M22Q.S 1) (M22Q.SI 1)
      (Certificates.Odd87F3.M22.oddWordsOut1_5.getD i [])) (OGA5.getD i 0))) = true := by
  quickRfl

theorem bOGA11 : allN 6 (fun i => bAnd(abOK (Certificates.Odd87F3.M22.oddWordsOut1_11.getD i []),
    Nat.beq (abWordK 22 5 (mask 5) (pidn 22 5) (M22Q.S 0) (M22Q.SI 0) (M22Q.S 1) (M22Q.SI 1)
      (Certificates.Odd87F3.M22.oddWordsOut1_11.getD i [])) (OGA11.getD i 0))) = true := by
  quickRfl

theorem bOGB3 : allN 3 (fun i => bAnd(abOK (Certificates.Odd87F3.M22.oddWordsOut2_3.getD i []),
    Nat.beq (abWordK 22 5 (mask 5) (pidn 22 5) (M22Q.S 0) (M22Q.SI 0) (M22Q.S 1) (M22Q.SI 1)
      (Certificates.Odd87F3.M22.oddWordsOut2_3.getD i [])) (OGB3.getD i 0))) = true := by
  quickRfl

theorem bA0 : bAnd(abOK Certificates.CF67.M22.wa, Nat.beq (abWordK 22 5 (mask 5) (pidn 22 5)
    (M22Q.S 0) (M22Q.SI 0) (M22Q.S 1) (M22Q.SI 1) Certificates.CF67.M22.wa) PA0) = true := by
  quickRfl

theorem bB0 : bAnd(abOK Certificates.CF67.M22.wb, Nat.beq (abWordK 22 5 (mask 5) (pidn 22 5)
    (M22Q.S 0) (M22Q.SI 0) (M22Q.S 1) (M22Q.SI 1) Certificates.CF67.M22.wb) PB0) = true := by
  quickRfl

theorem bH : allN 3 (fun j => bAnd(abOK (CFSG.KS.SporSch.MathieuC3.m22Words.getD j []),
    Nat.beq (abWordK 22 5 (mask 5) (pidn 22 5) (M22Q.S 0) (M22Q.SI 0) (M22Q.S 1) (M22Q.SI 1)
      (CFSG.KS.SporSch.MathieuC3.m22Words.getD j [])) (M22CH.S j))) = true := by quickRfl

theorem uSq : Nat.beq (pcomp 22 5 (mask 5) UI UI) (pidn 22 5) = true ∧
    Nat.beq (pcomp 22 5 (mask 5) UA UA) (pidn 22 5) = true ∧
    Nat.beq (pcomp 22 5 (mask 5) UB UB) (pidn 22 5) = true := ⟨by quickRfl, by quickRfl, by quickRfl⟩

theorem ogI : allN 1 (fun i => bAnd(Nat.beq (pcomp 22 5 (mask 5) UI (OGI3.getD i 0))
      (pcomp 22 5 (mask 5) (OGI3.getD i 0) UI),
      Nat.beq (powK 22 5 (mask 5) (pidn 22 5) (OGI3.getD i 0) 3) (pidn 22 5))) = true ∧
    allN 2 (fun i => bAnd(Nat.beq (pcomp 22 5 (mask 5) UI (OGI5.getD i 0))
      (pcomp 22 5 (mask 5) (OGI5.getD i 0) UI),
      Nat.beq (powK 22 5 (mask 5) (pidn 22 5) (OGI5.getD i 0) 3) (pidn 22 5))) = true :=
  ⟨by quickRfl, by quickRfl⟩

theorem ogA : allN 2 (fun i => bAnd(Nat.beq (pcomp 22 5 (mask 5) UA (OGA3.getD i 0))
      (pcomp 22 5 (mask 5) (OGA3.getD i 0) UA),
      Nat.beq (powK 22 5 (mask 5) (pidn 22 5) (OGA3.getD i 0) 5) (pidn 22 5))) = true ∧
    allN 3 (fun i => bAnd(Nat.beq (pcomp 22 5 (mask 5) UA (OGA5.getD i 0))
      (pcomp 22 5 (mask 5) (OGA5.getD i 0) UA),
      Nat.beq (powK 22 5 (mask 5) (pidn 22 5) (OGA5.getD i 0) 5) (pidn 22 5))) = true ∧
    allN 6 (fun i => bAnd(Nat.beq (pcomp 22 5 (mask 5) UA (OGA11.getD i 0))
      (pcomp 22 5 (mask 5) (OGA11.getD i 0) UA),
      Nat.beq (powK 22 5 (mask 5) (pidn 22 5) (OGA11.getD i 0) 5) (pidn 22 5))) = true :=
  ⟨by quickRfl, by quickRfl, by quickRfl⟩

theorem ogB : allN 3 (fun i => bAnd(Nat.beq (pcomp 22 5 (mask 5) UB (OGB3.getD i 0))
      (pcomp 22 5 (mask 5) (OGB3.getD i 0) UB),
      Nat.beq (powK 22 5 (mask 5) (pidn 22 5) (OGB3.getD i 0) 3) (pidn 22 5))) = true := by
  quickRfl

theorem f3I : invCandK 22 5 rowsIK (pinvS 22 5 (mask 5) UI) (M22CK.getD 0 clsD0) = true := by
  quickRfl

theorem f3A0 : invCandK 22 5 rowsAK (pinvS 22 5 (mask 5) UA) (M22OCL.getD 0 clsD0) = true := by
  quickRfl

theorem f3A1 : invCandK 22 5 rowsAK (pinvS 22 5 (mask 5) UA) (M22OCL.getD 1 clsD0) = true := by
  quickRfl

theorem f3B0 : invCandK 22 5 rowsBK (pinvS 22 5 (mask 5) UB) (M22OCL.getD 0 clsD0) = true := by
  quickRfl

theorem f3B1 : invCandK 22 5 rowsBK (pinvS 22 5 (mask 5) UB) (M22OCL.getD 1 clsD0) = true := by
  quickRfl

theorem abFacts : Nat.beq (powK 22 5 (mask 5) (pidn 22 5) PA0 3) (pidn 22 5) = true ∧
    Nat.beq (powK 22 5 (mask 5) (pidn 22 5) PB0 3) (pidn 22 5) = true ∧
    Nat.beq (pcomp 22 5 (mask 5) PA0 PB0) (pcomp 22 5 (mask 5) PB0 PA0) = true ∧
    (Nat.beq PA0 (pidn 22 5)).not = true ∧
    allN 3 (fun i => (Nat.beq PB0 (powK 22 5 (mask 5) (pidn 22 5) PA0 i)).not) = true :=
  ⟨by quickRfl, by quickRfl, by quickRfl, by quickRfl, by quickRfl⟩

theorem abShr : Nat.beq (Nat.shiftRight PA0 (22 * 5)) 0 = true ∧
    Nat.beq (Nat.shiftRight PB0 (22 * 5)) 0 = true := ⟨by quickRfl, by quickRfl⟩

theorem hComm : allN 3 (fun j => Nat.beq (pcomp 22 5 (mask 5) (M22CH.S j) PA0)
    (pcomp 22 5 (mask 5) PA0 (M22CH.S j))) = true := by quickRfl

theorem hOrd : Nat.beq (ordK M22CH.LR 2) 36 = true := by quickRfl

theorem cent : Nat.beq (btK 22 5 (mask 5) (22 * 5) M22Q.BP 5 M22Q.LR M22Q.TR M22Q.TRI PA0 PA0)
    36 = true := by quickRfl

theorem elems : allN 36 (fun j => powCommK 22 5 PB0 9
    (elemK 22 5 (mask 5) (22 * 5) (pidn 22 5) M22CH.LR M22CH.TR 2 j)) = true := by quickRfl

end CertificateChecks.KernelSporSch.M22W

end
