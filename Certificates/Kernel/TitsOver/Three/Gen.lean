module

public import Certificates.Kernel.TitsOver.Three.Enum
public import Certificates.Kernel.TitsOver.Three.Data
public import Certificates.Kernel.MaxD2.TitsD.Data
public import Certificates.Kernel.Sporadic.Tits.Words2264
public import Certificates.Data.Kernel.TitsOver.Check
public import CFSG.LocalAnalysis.StandardType.TitsThreeOvergroupData
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelTitsOver.Three

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.PEnum CFSG.KS.TitsOver
open CertificateChecks.KernelSpor.Tits2264 CFSG.StandardType.TitsThree
open CertificateChecks.KernelMaxD2

@[expose] noncomputable def genK (i : Nat) : Bool :=
  bIf(Nat.beq (pairData.kind[i]!) 0,
    bAnd(Nat.beq (genWords[i]!).length 2, allN 2 (fun j =>
      wordBK 4 6 (r32 TitsD.PT) (pairLf 11 (mask 11) (PE.G 0) (PE.G 1) (REP (Nat.succ i)) (REPI (Nat.succ i)))
        (pairLf 11 (mask 11) (PGI 0) (PGI 1) (REP (Nat.succ i)) (REPI (Nat.succ i)))
        ((genWords[i]!)[j]!) (pg 11 (mask 11) (Dk j)))), true)

theorem k_gen0 : allN 114 (fun d => genK (Nat.add 0 d)) = true := by quickRfl
theorem k_gen1 : allN 114 (fun d => genK (Nat.add 114 d)) = true := by quickRfl
theorem k_gen2 : allN 114 (fun d => genK (Nat.add 228 d)) = true := by quickRfl
theorem k_gen3 : allN 114 (fun d => genK (Nat.add 342 d)) = true := by quickRfl

end CertificateChecks.KernelTitsOver.Three

end
