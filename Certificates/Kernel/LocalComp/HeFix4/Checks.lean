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

@[expose] noncomputable def iP (p : Nat) : Nat := pinvS 8330 14 (mask 14) p

@[expose] noncomputable def cP (p q : Nat) : Nat := pcomp 8330 14 (mask 14) p q

@[expose] noncomputable def L1 (k : Nat) : Nat := nIf(Nat.beq k 2, T1P, HeC.S k)

@[expose] noncomputable def L1I (k : Nat) : Nat := nIf(Nat.beq k 2, iP T1P, HeC.SI k)

@[expose] noncomputable def C1P (j : Nat) : Nat :=
  [0, C1L1, C1L2, C1L3, 0, 0, 0, 0, C1L8].getD j 0

@[expose] noncomputable def wL (idn : Nat) (wd : List Int) : Nat :=
  wordK 8330 14 (mask 14) idn L1 L1I wd

@[expose] def cw (j : Nat) : List Int := heInnerWords1.getD j []

@[expose] noncomputable def TP (g : Nat) : Nat := [T1P, TL1, TL2, TL3, TL4].getD g 0

@[expose] noncomputable def B1P (i : Nat) : Nat := [BL0, BL1].getD i 0

@[expose] noncomputable def cjK (s : Nat) : Nat := cP (cP KP s) (iP KP)

@[expose] noncomputable def OG (j : Nat) : Nat :=
  nIf(Nat.blt j 8, [OL0, OL1, OL2, OL3, OL4, OL5, OL6, OL7].getD j 0, TP (Nat.sub j 8))

@[expose] noncomputable def cK (p : Nat) : Bool := canonK 8330 14 (mask 14) (8330 * 14) p

@[expose] noncomputable def pK (p : Nat) : Bool := permOK 8330 14 (mask 14) (8330 * 14) p (iP p)

@[expose] noncomputable def kAK : Bool :=
  bAnd(idK 8330 14 (mask 14), bAnd(cK idP,
  bAnd(allN 2 (fun j => permOK 8330 14 (mask 14) (8330 * 14) (HeC.S j) (HeC.SI j)),
  bAnd(pK T1P, bAnd(pK KP, bAnd(cK T1P, bAnd(cK KP, bAnd(cK (iP KP),
  bAnd(allN 3 (fun k => permOK 8330 14 (mask 14) (8330 * 14) (L1 k) (L1I k)),
  bAnd(Nat.beq (pg 14 (mask 14) KP 0) 7750,
  bAnd(!Nat.beq (pg 14 (mask 14) (HeC.S 1) 0) 0,
    allN 9 (fun j => bAnd(cK (HeC.S j), cK (HeC.SI j))))))))))))))

@[expose] noncomputable def kWK (X : Nat) (wd : List Int) (r : Nat) : Bool :=
  bAnd(lettersK 3 wd, bAnd(cK X, Nat.beq (wL X wd) r))

@[expose] noncomputable def kTK (g : Nat) : Bool :=
  bAnd(bIf(Nat.beq g 0, true, Nat.beq (wT C1P (hfTauWords.getD (Nat.sub g 1) [])) (TP g)),
    bAnd(cK (TP g), bAnd(pK (TP g), cK (iP (TP g)))))

@[expose] noncomputable def kBK : Bool :=
  bAnd(allN 2 (fun i => Nat.beq (wT TP (hfB1Words.getD i [])) (B1P i)),
  bAnd(Nat.beq (wT TP hfE2Word) E2P,
  bAnd(cK (B1P 0), bAnd(cK (B1P 1), bAnd(cK E2P,
  bAnd(Nat.beq (cP (B1P 0) (B1P 0)) idP, bAnd(Nat.beq (cP (B1P 1) (B1P 1)) idP,
  bAnd(Nat.beq (cP (B1P 0) (B1P 1)) (cP (B1P 1) (B1P 0)),
  bAnd(!Nat.beq (B1P 0) idP, bAnd(!Nat.beq (B1P 1) idP, bAnd(!Nat.beq (B1P 1) (B1P 0),
  bAnd(Nat.beq (cP E2P E2P) idP, bAnd(!Nat.beq E2P idP, !Nat.beq E2P T1P)))))))))))))

@[expose] noncomputable def kJK (j : Nat) : Bool :=
  allN 2 (fun i => [idP, B1P 0, B1P 1, cP (B1P 0) (B1P 1)].any
    (Nat.beq (cP (cP (cjK (HeC.S j)) (B1P i)) (cjK (HeC.SI j)))))

@[expose] noncomputable def kEK (g : Nat) : Bool :=
  [E2P, cP E2P T1P].any (Nat.beq (cP (cP (TP g) E2P) (iP (TP g))))

@[expose] noncomputable def kOK (j : Nat) : Bool :=
  bAnd(bIf(Nat.blt j 8, Nat.beq (cjK (HeC.S (heStabIdx.getD j 0))) (OG j), true), cK (OG j))

theorem kA : kAK = true := by quickRfl
theorem kWT1 : wordEqK 8330 14 (mask 14) idP HeC.S HeC.SI 2 heT1Word T1P = true := by quickRfl
theorem kWKP : wordEqK 8330 14 (mask 14) idP HeC.S HeC.SI 2 hfKWord KP = true := by quickRfl
theorem kC1 : kWK idP (cw 1) C1L1 = true := by quickRfl
theorem kC2 : kWK idP (cw 2) C1L2 = true := by quickRfl
theorem kC3a : kWK idP (((cw 3).drop 34).drop 40) C3A = true := by quickRfl
theorem kC3b : kWK C3A (((cw 3).drop 34).take 40) C3B = true := by quickRfl
theorem kC3c : kWK C3B ((cw 3).take 34) C1L3 = true := by quickRfl
theorem kC8a : kWK idP (((((cw 8).drop 10).drop 40).drop 40).drop 40) C8A = true := by quickRfl
theorem kC8b : kWK C8A ((((cw 8).drop 10).drop 40).drop 40 |>.take 40) C8B = true := by quickRfl
theorem kC8c : kWK C8B (((cw 8).drop 10).drop 40 |>.take 40) C8C = true := by quickRfl
theorem kC8d : kWK C8C (((cw 8).drop 10).take 40) C8D = true := by quickRfl
theorem kC8e : kWK C8D ((cw 8).take 10) C1L8 = true := by quickRfl
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
theorem kB : kBK = true := by quickRfl
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
