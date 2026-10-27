module

public import Certificates.Kernel.SporSch.Mathieu.M12DWData
public import Certificates.Data.Kernel.SporSch.OddWit
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSporSch.M12DW

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KS.MEnum CFSG.KS.M11 CFSG.KS.SporSch.MOC
open CFSG.KS.SporSch.OddWit CFSG.Sporadic.Schreier
open CertificateChecks.KernelSporSch CertificateChecks.KernelSporSch.M12MOC

@[expose] noncomputable def U1 : Nat := (M12ICL.getD 0 clsD0).R

@[expose] noncomputable def U2 : Nat := (M12ICL.getD 1 clsD0).R

@[expose] noncomputable def rows1K : List (Nat × Nat × List Nat) :=
  [(3, 27, OG13), (5, 5, OG15), (11, 11, [])]

@[expose] noncomputable def rows2K : List (Nat × Nat × List Nat) :=
  [(3, 27, OG23), (5, 5, OG25), (11, 11, [])]

@[expose] noncomputable def rowsSK : List (Nat × Nat × List Nat) :=
  [(3, 27, OGS3), (5, 5, OGS5), (11, 11, OGS11)]

theorem bRep : bAnd(abOK Certificates.Odd87F3.M12.repWordInn1, Nat.beq (abWordK 24 5 (mask 5)
      (pidn 24 5) (M12DQ.S 0) (M12DQ.SI 0) (M12DQ.S 1) (M12DQ.SI 1)
      Certificates.Odd87F3.M12.repWordInn1) U1) = true ∧
    bAnd(abOK Certificates.Odd87F3.M12.repWordInn2, Nat.beq (abWordK 24 5 (mask 5)
      (pidn 24 5) (M12DQ.S 0) (M12DQ.SI 0) (M12DQ.S 1) (M12DQ.SI 1)
      Certificates.Odd87F3.M12.repWordInn2) U2) = true := ⟨by quickRfl, by quickRfl⟩

theorem bOG13 : allN 2 (fun i => bAnd(abOK (Certificates.Odd87F3.M12.oddWordsInn1_3.getD i []),
    Nat.beq (abWordK 24 5 (mask 5) (pidn 24 5) (M12DQ.S 0) (M12DQ.SI 0) (M12DQ.S 1) (M12DQ.SI 1)
      (Certificates.Odd87F3.M12.oddWordsInn1_3.getD i [])) (OG13.getD i 0))) = true := by
  quickRfl

theorem bOG15 : allN 2 (fun i => bAnd(abOK (Certificates.Odd87F3.M12.oddWordsInn1_5.getD i []),
    Nat.beq (abWordK 24 5 (mask 5) (pidn 24 5) (M12DQ.S 0) (M12DQ.SI 0) (M12DQ.S 1) (M12DQ.SI 1)
      (Certificates.Odd87F3.M12.oddWordsInn1_5.getD i [])) (OG15.getD i 0))) = true := by
  quickRfl

theorem bOG23 : allN 1 (fun i => bAnd(abOK (Certificates.Odd87F3.M12.oddWordsInn2_3.getD i []),
    Nat.beq (abWordK 24 5 (mask 5) (pidn 24 5) (M12DQ.S 0) (M12DQ.SI 0) (M12DQ.S 1) (M12DQ.SI 1)
      (Certificates.Odd87F3.M12.oddWordsInn2_3.getD i [])) (OG23.getD i 0))) = true := by
  quickRfl

theorem bOG25 : allN 1 (fun i => bAnd(abOK (Certificates.Odd87F3.M12.oddWordsInn2_5.getD i []),
    Nat.beq (abWordK 24 5 (mask 5) (pidn 24 5) (M12DQ.S 0) (M12DQ.SI 0) (M12DQ.S 1) (M12DQ.SI 1)
      (Certificates.Odd87F3.M12.oddWordsInn2_5.getD i [])) (OG25.getD i 0))) = true := by
  quickRfl

theorem bOGS3 : allN 2 (fun i => bAnd(abOK (Certificates.Odd87F3.M12.oddWordsSig_3.getD i []),
    Nat.beq (abWordK 24 5 (mask 5) (pidn 24 5) (M12DQ.S 0) (M12DQ.SI 0) (M12DQ.S 1) (M12DQ.SI 1)
      (Certificates.Odd87F3.M12.oddWordsSig_3.getD i [])) (OGS3.getD i 0))) = true := by
  quickRfl

theorem bOGS5 : allN 1 (fun i => bAnd(abOK (Certificates.Odd87F3.M12.oddWordsSig_5.getD i []),
    Nat.beq (abWordK 24 5 (mask 5) (pidn 24 5) (M12DQ.S 0) (M12DQ.SI 0) (M12DQ.S 1) (M12DQ.SI 1)
      (Certificates.Odd87F3.M12.oddWordsSig_5.getD i [])) (OGS5.getD i 0))) = true := by
  quickRfl

theorem bOGS11 : allN 2 (fun i => bAnd(abOK (Certificates.Odd87F3.M12.oddWordsSig_11.getD i []),
    Nat.beq (abWordK 24 5 (mask 5) (pidn 24 5) (M12DQ.S 0) (M12DQ.SI 0) (M12DQ.S 1) (M12DQ.SI 1)
      (Certificates.Odd87F3.M12.oddWordsSig_11.getD i [])) (OGS11.getD i 0))) = true := by
  quickRfl

theorem cOne : canonK 24 5 (mask 5) (24 * 5) One = true := by quickRfl

theorem uSq : Nat.beq (pcomp 24 5 (mask 5) U1 U1) (pidn 24 5) = true ∧
    Nat.beq (pcomp 24 5 (mask 5) U2 U2) (pidn 24 5) = true ∧
    Nat.beq (pcomp 24 5 (mask 5) M12S M12S) (pidn 24 5) = true :=
  ⟨by quickRfl, by quickRfl, by quickRfl⟩

theorem og1 : allN 2 (fun i => bAnd(Nat.beq (pcomp 24 5 (mask 5) U1 (OG13.getD i 0))
      (pcomp 24 5 (mask 5) (OG13.getD i 0) U1),
      Nat.beq (powK 24 5 (mask 5) (pidn 24 5) (OG13.getD i 0) 3) (pidn 24 5))) = true ∧
    allN 2 (fun i => bAnd(Nat.beq (pcomp 24 5 (mask 5) U1 (OG15.getD i 0))
      (pcomp 24 5 (mask 5) (OG15.getD i 0) U1),
      Nat.beq (powK 24 5 (mask 5) (pidn 24 5) (OG15.getD i 0) 3) (pidn 24 5))) = true :=
  ⟨by quickRfl, by quickRfl⟩

theorem og2 : allN 1 (fun i => bAnd(Nat.beq (pcomp 24 5 (mask 5) U2 (OG23.getD i 0))
      (pcomp 24 5 (mask 5) (OG23.getD i 0) U2),
      Nat.beq (powK 24 5 (mask 5) (pidn 24 5) (OG23.getD i 0) 5) (pidn 24 5))) = true ∧
    allN 1 (fun i => bAnd(Nat.beq (pcomp 24 5 (mask 5) U2 (OG25.getD i 0))
      (pcomp 24 5 (mask 5) (OG25.getD i 0) U2),
      Nat.beq (powK 24 5 (mask 5) (pidn 24 5) (OG25.getD i 0) 3) (pidn 24 5))) = true :=
  ⟨by quickRfl, by quickRfl⟩

theorem ogS : allN 2 (fun i => bAnd(Nat.beq (pcomp 24 5 (mask 5) M12S (OGS3.getD i 0))
      (pcomp 24 5 (mask 5) (OGS3.getD i 0) M12S),
      Nat.beq (powK 24 5 (mask 5) (pidn 24 5) (OGS3.getD i 0) 5) (pidn 24 5))) = true ∧
    allN 1 (fun i => bAnd(Nat.beq (pcomp 24 5 (mask 5) M12S (OGS5.getD i 0))
      (pcomp 24 5 (mask 5) (OGS5.getD i 0) M12S),
      Nat.beq (powK 24 5 (mask 5) (pidn 24 5) (OGS5.getD i 0) 5) (pidn 24 5))) = true ∧
    allN 2 (fun i => bAnd(Nat.beq (pcomp 24 5 (mask 5) M12S (OGS11.getD i 0))
      (pcomp 24 5 (mask 5) (OGS11.getD i 0) M12S),
      Nat.beq (powK 24 5 (mask 5) (pidn 24 5) (OGS11.getD i 0) 3) (pidn 24 5))) = true :=
  ⟨by quickRfl, by quickRfl, by quickRfl⟩

theorem f310 : invCandK 24 5 rows1K (pinvS 24 5 (mask 5) U1) (M12ICL.getD 0 clsD0) = true := by
  quickRfl

theorem f311 : invCandK 24 5 rows1K (pinvS 24 5 (mask 5) U1) (M12ICL.getD 1 clsD0) = true := by
  quickRfl

theorem f320 : invCandK 24 5 rows2K (pinvS 24 5 (mask 5) U2) (M12ICL.getD 0 clsD0) = true := by
  quickRfl

theorem f321 : invCandK 24 5 rows2K (pinvS 24 5 (mask 5) U2) (M12ICL.getD 1 clsD0) = true := by
  quickRfl

theorem f3S : invCandK 24 5 rowsSK (pinvS 24 5 (mask 5) M12S) (M12SCL.getD 0 clsD0) = true := by
  quickRfl

end CertificateChecks.KernelSporSch.M12DW

end
