module

public import Certificates.Kernel.SporSch.HeT.B2114P
public import Certificates.Kernel.SporSch.Ru.RowsGen
public import CFSG.Certificates.Kernel.Spor.WordChunkSound
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSporSch.HeB14

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KS.Mathieu
open CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.Sporadic.HeldB
open CertificateChecks.KernelSpor CertificateChecks.KernelSporSch.HeX14

@[expose] noncomputable def WD (j : Nat) : List Int :=
  Bool.rec (motive := fun _ => List Int)
    (Bool.rec (motive := fun _ => List Int) heT1Word (heInnerWords1.getD (Nat.sub j 9) [])
      (Nat.blt j 18))
    (heInnerWords0.getD j []) (Nat.blt j 9)

@[expose] noncomputable def LA (l : Nat) : Nat := nIf(Nat.beq l 1, HeC.S 1, HeC.S 0)

@[expose] noncomputable def LAI (l : Nat) : Nat := nIf(Nat.beq l 1, HeC.SI 1, HeC.SI 0)

@[expose] noncomputable def V (j i : Nat) : Nat := HeB14V (Nat.add (nget OFF j) (Nat.div i 6))

@[expose] noncomputable def T1 : Nat := V 18 0

@[expose] noncomputable def T1I : Nat := HeB14P 0

@[expose] noncomputable def C0 (j : Nat) : Nat := V j 0

@[expose] noncomputable def C0I (j : Nat) : Nat := HeB14P (Nat.add 1 j)

@[expose] noncomputable def C1 (j : Nat) : Nat := V (Nat.add 9 j) 0

@[expose] noncomputable def C1I (j : Nat) : Nat := HeB14P (Nat.add 10 j)

@[expose] noncomputable def LB (l : Nat) : Nat := nIf(Nat.beq l 2, T1, LA l)

@[expose] noncomputable def LBI (l : Nat) : Nat := nIf(Nat.beq l 2, T1I, LAI l)

@[expose] noncomputable def LS (j l : Nat) : Nat :=
  nIf(bAnd(Nat.ble 9 j, Nat.blt j 18), LB l, LA l)

@[expose] noncomputable def LSI (j l : Nat) : Nat :=
  nIf(bAnd(Nat.ble 9 j, Nat.blt j 18), LBI l, LAI l)

@[expose] noncomputable def gk (g : Nat) : Bool :=
  strictB (nget GJ g) (fun j => chunkK 8330 14 (mask 14) (pidn 8330 14) (LS j) (LSI j) (WD j) 6
    (V j) (Nat.mul (nget GC g) 6))

@[expose] noncomputable def c0K (j : Nat) : Bool :=
  bAnd(invEqK 8330 14 (mask 14) (8330 * 14) (C0 j) (C0I j),
  bAnd(invEqK 8330 14 (mask 14) (8330 * 14) (C0I j) (C0 j),
  bAnd(commK 8330 14 (mask 14) (8330 * 14) (C0 j) (HeC.S 0),
    allN 240 (fun k => Nat.beq (pg 14 (mask 14) (C0 j) (nget D0 k))
      (nget D0 (pg 8 (mask 8) (X0Q.S j) k))))))

@[expose] noncomputable def c1K (j : Nat) : Bool :=
  bAnd(invEqK 8330 14 (mask 14) (8330 * 14) (C1 j) (C1I j),
  bAnd(invEqK 8330 14 (mask 14) (8330 * 14) (C1I j) (C1 j),
  bAnd(commK 8330 14 (mask 14) (8330 * 14) (C1 j) T1,
    allN 42 (fun k => Nat.beq (pg 14 (mask 14) (C1 j) (nget D1 k))
      (nget D1 (pg 6 (mask 6) (X1Q.S j) k))))))

end CertificateChecks.KernelSporSch.HeB14

#kss_each CertificateChecks.KernelSporSch.HeB14K CertificateChecks.KernelSporSch.HeB14.gk 144

namespace CertificateChecks.KernelSporSch.HeB14

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KS.Mathieu
open CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.Sporadic.HeldB
open CertificateChecks.KernelSpor CertificateChecks.KernelSporSch.HeX14

theorem kT1 : bAnd(invEqK 8330 14 (mask 14) (8330 * 14) T1 T1I,
    bAnd(invEqK 8330 14 (mask 14) (8330 * 14) T1I T1,
    bAnd(sqIdK 8330 14 (mask 14) (8330 * 14) (pidn 8330 14) T1,
    bAnd(neIdK 8330 14 (mask 14) (8330 * 14) (pidn 8330 14) T1,
    bAnd(sqIdK 8330 14 (mask 14) (8330 * 14) (pidn 8330 14) (HeC.S 0),
    bAnd(neIdK 8330 14 (mask 14) (8330 * 14) (pidn 8330 14) (HeC.S 0),
    bAnd(Nat.beq (C0 0) (HeC.S 0), Nat.beq (C1 0) T1))))))) = true := by quickRfl

theorem kP : bAnd(szOK 8330 14,
    bAnd(allN 2 (fun l => permOK 8330 14 (mask 14) (8330 * 14) (LS 18 l) (LSI 18 l)),
    bAnd(allN 3 (fun l => permOK 8330 14 (mask 14) (8330 * 14) (LA l) (LAI l)),
    allN 3 (fun l => permOK 8330 14 (mask 14) (8330 * 14) (LB l) (LBI l))))) = true := by quickRfl

theorem kL : bAnd(allN 9 (fun j => lettersK 3 (WD j)), bAnd(allN 9 (fun j => lettersK 3 (WD (Nat.add 9 j))),
    lettersK 2 (WD 18))) = true := by quickRfl

theorem kFix : bAnd(allN 240 (fun k => Nat.beq (pg 14 (mask 14) (HeC.S 0) (nget D0 k)) (nget D0 k)),
    allN 42 (fun k => Nat.beq (pg 14 (mask 14) T1 (nget D1 k)) (nget D1 k))) = true := by quickRfl

theorem k00 : c0K 0 = true := by quickRfl
theorem k01 : c0K 1 = true := by quickRfl
theorem k02 : c0K 2 = true := by quickRfl
theorem k03 : c0K 3 = true := by quickRfl
theorem k04 : c0K 4 = true := by quickRfl
theorem k05 : c0K 5 = true := by quickRfl
theorem k06 : c0K 6 = true := by quickRfl
theorem k07 : c0K 7 = true := by quickRfl
theorem k08 : c0K 8 = true := by quickRfl
theorem k10 : c1K 0 = true := by quickRfl
theorem k11 : c1K 1 = true := by quickRfl
theorem k12 : c1K 2 = true := by quickRfl
theorem k13 : c1K 3 = true := by quickRfl
theorem k14 : c1K 4 = true := by quickRfl
theorem k15 : c1K 5 = true := by quickRfl
theorem k16 : c1K 6 = true := by quickRfl
theorem k17 : c1K 7 = true := by quickRfl
theorem k18 : c1K 8 = true := by quickRfl

theorem kChunks : ∀ j < 19, 0 < nget NC j ∧ (WD j).length ≤ nget NC j * 6 ∧
    ∀ c < nget NC j, nget OFF j + c < 144 ∧ nget GJ (nget OFF j + c) = j ∧
      nget GC (nget OFF j + c) = c := by decide +kernel

end CertificateChecks.KernelSporSch.HeB14

end
