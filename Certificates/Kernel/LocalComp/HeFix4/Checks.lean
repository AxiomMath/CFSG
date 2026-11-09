module

public import Certificates.Kernel.LocalComp.HeFix4.Data
public import Certificates.Kernel.Sporadic.He.Chain2112
public import CFSG.Certificates.Kernel.Spor.PackWord
public import Certificates.Data.Kernel.Child3
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000
set_option Elab.async false

namespace CertificateChecks.KernelLC.HeFix4

open CFSG.KC.Enum CFSG.KC.BfsPin CFSG.KS CFSG.KS.Prim CFSG.KS.Raw CFSG.KS.PEnum
open CFSG.Monster.B.Co2.Native CFSG.Certificates.Native CFSG.PSL3Four.Native
open CFSG.Sporadic.HeldB CFSG.Sporadic.SmallOddCore CFSG.ComponentClassification.GrSLit.HeldFix
open CertificateChecks.KernelSpor

@[expose] noncomputable def idP : Nat := pidn 8330 14

@[expose] noncomputable def wT (S : Nat → Nat) (wd : List Nat) : Nat :=
  wordTabK 8330 14 (mask 14) (pidn 8330 14) S wd

@[expose] noncomputable def cP (p q : Nat) : Nat := pcomp 8330 14 (mask 14) p q

@[expose] noncomputable def L1 (k : Nat) : Nat := nIf(Nat.beq k 2, T1P, HeC.S k)

@[expose] noncomputable def L1I (k : Nat) : Nat := nIf(Nat.beq k 2, T1I, HeC.SI k)

@[expose] noncomputable def C1P (j : Nat) : Nat :=
  [0, C1L1, C1L2, C1L3, 0, 0, 0, 0, C1L8].getD j 0

@[expose] noncomputable def wL (idn : Nat) (wd : List Int) : Nat :=
  wordK 8330 14 (mask 14) idn L1 L1I wd

@[expose] def cw (j : Nat) : List Int := heInnerWords1.getD j []

@[expose] noncomputable def TP (g : Nat) : Nat := [T1P, TL1, TL2, TL3, TL4].getD g 0

@[expose] noncomputable def TIP (g : Nat) : Nat := [T1I, TI1, TI2, TI3, TI4].getD g 0

@[expose] noncomputable def B1P (i : Nat) : Nat := [BL0, BL1].getD i 0

@[expose] noncomputable def cjK (s : Nat) : Nat := cP (cP KP s) KI

@[expose] noncomputable def OG (j : Nat) : Nat :=
  nIf(Nat.blt j 8, [OL0, OL1, OL2, OL3, OL4, OL5, OL6, OL7].getD j 0, TP (Nat.sub j 8))

@[expose] noncomputable def cK (p : Nat) : Bool := canonK 8330 14 (mask 14) (8330 * 14) p

@[expose] noncomputable def pK (p q : Nat) : Bool := permOK 8330 14 (mask 14) (8330 * 14) p q

@[expose] noncomputable def kWK (X : Nat) (wd : List Int) (r : Nat) : Bool :=
  bAnd(lettersK 3 wd, bAnd(cK X, Nat.beq (wL X wd) r))

@[expose] noncomputable def kTK (g : Nat) : Bool :=
  bAnd(bIf(Nat.beq g 0, true, Nat.beq (wT C1P (hfTauWords.getD (Nat.sub g 1) [])) (TP g)),
    bAnd(cK (TP g), bAnd(pK (TP g) (TIP g), cK (TIP g))))

@[expose] noncomputable def kJK (j : Nat) : Bool :=
  allN 2 (fun i => [idP, B1P 0, B1P 1, cP (B1P 0) (B1P 1)].any
    (Nat.beq (cP (cP (cjK (HeC.S j)) (B1P i)) (cjK (HeC.SI j)))))

@[expose] noncomputable def kEK (g : Nat) : Bool :=
  [E2P, cP E2P T1P].any (Nat.beq (cP (cP (TP g) E2P) (TIP g)))

@[expose] noncomputable def kOK (j : Nat) : Bool :=
  bAnd(bIf(Nat.blt j 8, Nat.beq (cjK (HeC.S (heStabIdx.getD j 0))) (OG j), true), cK (OG j))

theorem kA : idK 8330 14 (mask 14) = true ∧ cK idP = true ∧
    allN 2 (fun j => permOK 8330 14 (mask 14) (8330 * 14) (HeC.S j) (HeC.SI j)) = true ∧
    pK T1P T1I = true ∧ pK KP KI = true ∧ cK T1P = true ∧ cK KP = true ∧ cK KI = true ∧
    allN 3 (fun k => permOK 8330 14 (mask 14) (8330 * 14) (L1 k) (L1I k)) = true ∧
    Nat.beq (pg 14 (mask 14) KP 0) 7750 = true ∧
    (!Nat.beq (pg 14 (mask 14) (HeC.S 1) 0) 0) = true ∧
    allN 9 (fun j => cK (HeC.S j)) = true ∧ allN 9 (fun j => cK (HeC.SI j)) = true := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> quickRfl
theorem kcT1I : cK T1I = true := by quickRfl
theorem kWT1 : wordEqK 8330 14 (mask 14) idP HeC.S HeC.SI 2 heT1Word T1P = true := by quickRfl
theorem kWKP : wordEqK 8330 14 (mask 14) idP HeC.S HeC.SI 2 hfKWord KP = true := by quickRfl
theorem kP1 : kWK idP (((cw 1).drop 5).take 12) P1 = true := by quickRfl
theorem kC1 : kWK (ppow 8330 14 (mask 14) idP P1 2) ((cw 1).take 5) C1L1 = true := by quickRfl
theorem kP2 : kWK idP (((cw 2).drop 0).take 8) P2 = true := by quickRfl
theorem kC2 : kWK (ppow 8330 14 (mask 14) idP P2 2) ((cw 2).take 0) C1L2 = true := by quickRfl
theorem kL1 : lettersK 3 (cw 1) = true := by quickRfl
theorem kL2 : lettersK 3 (cw 2) = true := by quickRfl
theorem kcP12 : cK P1 = true ∧ cK P2 = true := by
  refine ⟨?_, ?_⟩ <;> quickRfl
theorem kP3 : kWK idP (((cw 3).drop 4).take 10) P3 = true := by quickRfl
theorem kC3 : kWK (ppow 8330 14 (mask 14) idP P3 11) ((cw 3).take 4) C1L3 = true := by quickRfl
theorem kP8 : kWK idP (((cw 8).drop 8).take 18) P8 = true := by quickRfl
theorem kC8 : kWK (ppow 8330 14 (mask 14) idP P8 9) ((cw 8).take 8) C1L8 = true := by quickRfl
theorem kcP : cK P3 = true ∧ cK P8 = true := by
  refine ⟨?_, ?_⟩ <;> quickRfl
theorem kSz : szOK 8330 14 = true := by quickRfl
theorem kL3 : lettersK 3 (cw 3) = true := by quickRfl
theorem kL8 : lettersK 3 (cw 8) = true := by quickRfl
theorem kCc : cK C1L1 = true ∧ cK C1L2 = true ∧ cK C1L3 = true ∧ cK C1L8 = true := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> quickRfl
theorem kT0 : kTK 0 = true := by quickRfl
theorem kT1 : kTK 1 = true := by quickRfl
theorem kT2 : kTK 2 = true := by quickRfl
theorem kT3 : kTK 3 = true := by quickRfl
theorem kT4 : kTK 4 = true := by quickRfl
theorem kB : allN 2 (fun i => Nat.beq (wT TP (hfB1Words.getD i [])) (B1P i)) = true ∧
    Nat.beq (wT TP hfE2Word) E2P = true ∧
    cK (B1P 0) = true ∧ cK (B1P 1) = true ∧ cK E2P = true ∧
    Nat.beq (cP (B1P 0) (B1P 0)) idP = true ∧ Nat.beq (cP (B1P 1) (B1P 1)) idP = true ∧
    Nat.beq (cP (B1P 0) (B1P 1)) (cP (B1P 1) (B1P 0)) = true ∧
    (!Nat.beq (B1P 0) idP) = true ∧ (!Nat.beq (B1P 1) idP) = true ∧
    (!Nat.beq (B1P 1) (B1P 0)) = true ∧
    Nat.beq (cP E2P E2P) idP = true ∧ (!Nat.beq E2P idP) = true ∧ (!Nat.beq E2P T1P) = true := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> quickRfl
theorem kJ0 : kJK 0 = true := by quickRfl
theorem kJ2 : kJK 2 = true := by quickRfl
theorem kJ3 : kJK 3 = true := by quickRfl
theorem kJ4 : kJK 4 = true := by quickRfl
theorem kJ5 : kJK 5 = true := by quickRfl
theorem kJ6 : kJK 6 = true := by quickRfl
theorem kJ7 : kJK 7 = true := by quickRfl
theorem kJ8 : kJK 8 = true := by quickRfl
theorem kE0 : kEK 0 = true := by quickRfl
theorem kE1 : kEK 1 = true := by quickRfl
theorem kE2 : kEK 2 = true := by quickRfl
theorem kE3 : kEK 3 = true := by quickRfl
theorem kE4 : kEK 4 = true := by quickRfl
theorem kO0 : kOK 0 = true := by quickRfl
theorem kO1 : kOK 1 = true := by quickRfl
theorem kO2 : kOK 2 = true := by quickRfl
theorem kO3 : kOK 3 = true := by quickRfl
theorem kO4 : kOK 4 = true := by quickRfl
theorem kO5 : kOK 5 = true := by quickRfl
theorem kO6 : kOK 6 = true := by quickRfl
theorem kO7 : kOK 7 = true := by quickRfl
theorem kO8 : kOK 8 = true := by quickRfl
theorem kO9 : kOK 9 = true := by quickRfl
theorem kO10 : kOK 10 = true := by quickRfl
theorem kO11 : kOK 11 = true := by quickRfl
theorem kO12 : kOK 12 = true := by quickRfl
theorem kF : CFSG.KC.Child3.forestK 8330 14 OG 13 [7750] F.FP F.FL F.FD = true := by quickRfl

end CertificateChecks.KernelLC.HeFix4

end
