module

public import Certificates.Kernel.CU43Aut.Small
public import Certificates.Kernel.KsEight.Data
public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.TS16RUKsData
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelKsEight

open CFSG.EvenSporadicStandard.Fin76b.U16
open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim
open CertificateChecks.KernelU43B CertificateChecks.KernelCU43Aut

@[expose] noncomputable def ord8K (r : Nat) : Bool :=
  strictB (pc r r) (fun r2 => strictB (pc r2 r2) (fun r4 =>
    bAnd(Nat.beq (pc r4 r4) (pidn 820 10), bIf(Nat.beq r4 (pidn 820 10), false, true))))

@[expose] noncomputable def repK (j : Nat) : Bool :=
  strictB (RK j) (fun r => bAnd(cK r, bAnd(inPK (pc r (TKI ks8Coset[j]!)), ord8K r)))

@[expose] noncomputable def conjK (j : Nat) : Bool :=
  strictB (GJ j) (fun g => strictB (CR (Nat.mul 3 j)) (fun r1 =>
  strictB (CR (Nat.add (Nat.mul 3 j) 1)) (fun r2 =>
  bAnd(cK g, bAnd(inPK g, bAnd(cK r1, bAnd(Nat.beq (pc g (RK j)) (pc r1 g),
  bAnd(Nat.beq r2 (pc r1 r1), Nat.beq (CR (Nat.add (Nat.mul 3 j) 2)) (pc r2 r2)))))))))

theorem ksBind : bindListK 820 10 (RK 0) (ks8Reps[0]!).toList = true ∧
    bindListK 820 10 (RK 1) (ks8Reps[1]!).toList = true ∧
    bindListK 820 10 (RK 2) (ks8Reps[2]!).toList = true ∧
    bindListK 820 10 (RK 3) (ks8Reps[3]!).toList = true ∧
    bindListK 820 10 (RK 4) (ks8Reps[4]!).toList = true ∧
    bindListK 820 10 (RK 5) (ks8Reps[5]!).toList = true ∧
    bindListK 820 10 (RK 6) (ks8Reps[6]!).toList = true ∧
    bindListK 820 10 (RK 7) (ks8Reps[7]!).toList = true := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> quickRfl

theorem ksRep : allN 8 repK = true := by quickRfl

theorem ksConj : allN 5 conjK = true := by quickRfl

end CertificateChecks.KernelKsEight

end
