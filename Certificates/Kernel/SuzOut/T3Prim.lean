module

public import Certificates.Kernel.SuzOut.T3Data
public import Certificates.Data.GSThmBCatalog7SuzCS
public import CFSG.Certificates.Kernel.Spor.PackWord
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSuzOut.T3P

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KS.PEnum CFSG.KC.BfsPin
open CFSG.ComponentClassification.CatFactsL4U4.SuzCS CertificateChecks.KernelSuzOut

@[expose] noncomputable def KW (w : List Nat) : Nat :=
  wordTabK 100 7 (mask 7) (pidn 100 7) T3X.S w

@[expose] noncomputable def HK (j : Nat) : Nat := KW (hWords.getD j [])

@[expose] noncomputable def UW (w : List Nat) : Nat := wordTabK 100 7 (mask 7) (pidn 100 7) HK w

@[expose] noncomputable def transK (p : Nat) : Bool :=
  (transWords.getD p []).all (fun j => Nat.blt j 5) &&
    Nat.beq (pg 7 (mask 7) (KW (transWords.getD p [])) 0) p

@[expose] noncomputable def hK (w : List Nat) : Bool :=
  w.all (fun j => Nat.blt j 5) && Nat.beq (pg 7 (mask 7) (KW w) 0) 0

@[expose] noncomputable def uK (p : Nat) : Bool :=
  Nat.blt (labList.getD p 0) 3 && ((uWords.getD p []).all (fun j => Nat.blt j 3) &&
    Nat.beq (pg 7 (mask 7) (UW (uWords.getD p [])) (rootList.getD (labList.getD p 0) 0)) p)

theorem ch23001_trans : allN 100 transK = true := by quickRfl

theorem ch23001_h : hWords.all hK = true := by quickRfl

theorem ch23001_u : allN 100 uK = true := by quickRfl

end CertificateChecks.KernelSuzOut.T3P

end
