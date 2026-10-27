module

public import Certificates.Kernel.SporSch.HeT.W2117P
public import Certificates.Kernel.SporSch.HeT.Q2117K
public import Certificates.Kernel.SporSch.Ru.RowsGen
public import CFSG.Certificates.Kernel.Spor.WordChunkSound
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSporSch.HeW17

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KS.Mathieu CFSG.KS.SporSch
open CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.Sporadic.HeldB
open CertificateChecks.KernelSpor CertificateChecks.KernelSporSch

@[expose] noncomputable def WD (j : Nat) : List Int :=
  Bool.rec (motive := fun _ => List Int) (heDerivedV.getD (Nat.sub j 2) [])
    (Bool.rec (motive := fun _ => List Int) heCentW2 heCentW1 (Nat.beq j 0)) (Nat.blt j 2)

@[expose] noncomputable def U : Nat := HeW17U 0

@[expose] noncomputable def UI : Nat := HeW17P 0

@[expose] noncomputable def LC (l : Nat) : Nat :=
  nIf(Nat.beq l 2, U, nIf(Nat.beq l 1, HeC.S 1, HeC.S 0))

@[expose] noncomputable def LCI (l : Nat) : Nat :=
  nIf(Nat.beq l 2, UI, nIf(Nat.beq l 1, HeC.SI 1, HeC.SI 0))

@[expose] noncomputable def V (j i : Nat) : Nat := HeW17V (Nat.add (nget OFF j) (Nat.div i 6))

@[expose] noncomputable def C (j : Nat) : Nat := V j 0

@[expose] noncomputable def CI (j : Nat) : Nat := HeW17P (Nat.add 1 j)

@[expose] noncomputable def D (j : Nat) : Nat := V (Nat.add 2 j) 0

@[expose] noncomputable def LD (l : Nat) : Nat := nIf(Nat.beq l 1, C 1, C 0)

@[expose] noncomputable def LDI (l : Nat) : Nat := nIf(Nat.beq l 1, CI 1, CI 0)

@[expose] noncomputable def LS (j l : Nat) : Nat := nIf(Nat.blt j 2, LC l, LD l)

@[expose] noncomputable def LSI (j l : Nat) : Nat := nIf(Nat.blt j 2, LCI l, LDI l)

@[expose] noncomputable def gk (g : Nat) : Bool :=
  strictB (nget GJ g) (fun j => chunkK 8330 14 (mask 14) (pidn 8330 14) (LS j) (LSI j) (WD j) 6
    (V j) (Nat.mul (nget GC g) 6))

@[expose] noncomputable def cK (j : Nat) : Bool :=
  bAnd(invEqK 8330 14 (mask 14) (8330 * 14) (C j) (CI j),
  bAnd(invEqK 8330 14 (mask 14) (8330 * 14) (CI j) (C j),
  bAnd(commK 8330 14 (mask 14) (8330 * 14) (C j) U,
    allN 98 (fun k => Nat.beq (pg 14 (mask 14) (C j) (nget FU k))
      (nget FU (pg 7 (mask 7) (HeQ17.QC.S j) k))))))

@[expose] noncomputable def dK (j : Nat) : Bool :=
  allN 98 (fun k => Nat.beq (pg 14 (mask 14) (D j) (nget FU k))
    (nget FU (pg 7 (mask 7) (HeQ17.QD.S j) k)))

@[expose] noncomputable def bindK (g : Nat) : Bool :=
  allN 833 (fun i => bind5At 8330 14 HeTb.NR HeTb.NR HeTb.LT HeTb.PT (nget NF (Nat.div g 10))
    (C (Nat.div g 10)) (Nat.add (Nat.mul (Nat.mod g 10) 833) i))

end CertificateChecks.KernelSporSch.HeW17

#kss_each CertificateChecks.KernelSporSch.HeW17K CertificateChecks.KernelSporSch.HeW17.gk 86

#kss_each CertificateChecks.KernelSporSch.HeW17B CertificateChecks.KernelSporSch.HeW17.bindK 20

namespace CertificateChecks.KernelSporSch.HeW17

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KS.Mathieu CFSG.KS.SporSch
open CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.Sporadic.HeldB
open CertificateChecks.KernelSpor CertificateChecks.KernelSporSch

theorem kU5 : Nat.beq (HeO16.pp HeO16.R 5) U = true := by quickRfl

theorem kUI : bAnd(invEqK 8330 14 (mask 14) (8330 * 14) U UI,
    invEqK 8330 14 (mask 14) (8330 * 14) UI U) = true := by quickRfl

theorem kP : bAnd(szOK 8330 14,
    bAnd(allN 3 (fun l => permOK 8330 14 (mask 14) (8330 * 14) (LS 0 l) (LSI 0 l)),
    allN 2 (fun l => permOK 8330 14 (mask 14) (8330 * 14) (LS 2 l) (LSI 2 l)))) = true := by
  quickRfl

theorem kL : bAnd(lettersK 3 (WD 0), bAnd(lettersK 3 (WD 1),
    allN 3 (fun j => lettersK 2 (WD (Nat.add 2 j))))) = true := by quickRfl

theorem kC0 : cK 0 = true := by quickRfl

theorem kC1 : cK 1 = true := by quickRfl

theorem kD : allN 3 dK = true := by quickRfl

theorem kFix : bAnd(Nat.beq (CFSG.KC.HeFixK.fixK 8330 14 U) 98,
    allN 98 (fun k => Nat.beq (pg 14 (mask 14) U (nget FU k)) (nget FU k))) = true := by quickRfl

theorem kNF : allN 2 (fun j => nfValidK 5 HeC.LR (nget NF j)) = true := by quickRfl

theorem kChunks : ∀ j < 5, 0 < nget NC j ∧ (WD j).length ≤ nget NC j * 6 ∧
    ∀ c < nget NC j, nget OFF j + c < 86 ∧ nget GJ (nget OFF j + c) = j ∧
      nget GC (nget OFF j + c) = c := by decide +kernel

theorem kF : heFixU.toList = FU ∧ FU.length = 98 ∧ (∀ x ∈ FU, x < 8330) ∧
    ∀ k < 98 - 1, nget FU k < nget FU (k + 1) := by decide +kernel

end CertificateChecks.KernelSporSch.HeW17

end
