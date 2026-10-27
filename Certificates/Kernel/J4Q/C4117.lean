module

public import CFSG.Sporadic.J4.QT2LocMain
public import CFSG.Sporadic.J4.QT2LocCntProof
public import CFSG.Sporadic.J4.QTRankProof
public import CFSG.Sporadic.J4.QTCheck
public import Certificates.Kernel.J4Q.Orbits
import CFSG.Certificates.Kernel.Common.Harness
public import CFSG.Sporadic.J4.QT2LocMainBase
public import CFSG.Sporadic.J4.QTOutChar
public import CFSG.Sporadic.J4Base

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelJ4Q

open CFSG.KC.J4Q CFSG.KD.J4Q CFSG.Sporadic.J4.QT CFSG.Sporadic.J4.QT2

theorem tMasks_chk : andB (Nat.beq (lenK (fstsK (ptsK OR.s0))) 276)
    (andB (distinctK (fstsK (ptsK OR.s0))) (allLtK 2048 (fstsK (ptsK OR.s0)))) = true := by
  quickRfl

open Certificates in
open CFSG in
open CFSG.Sporadic.J4 CFSG.Sporadic.J4.QT CFSG.Sporadic.J4.QT2 in
theorem c4117 : (tMasks.length = 276 ∧ tMasks.Nodup ∧ ∀ c ∈ tMasks, c < 2048)
    ∧ ((orbits.getD 0 (1, [], [])).1 = 1) := by
  obtain ⟨h1, h23⟩ := andB_true tMasks_chk
  obtain ⟨h2, h3⟩ := andB_true h23
  refine ⟨⟨?_, ?_, ?_⟩, rfl⟩
  · rw [tMasks_eq, ← lenK_eq]
    exact Nat.eq_of_beq_eq_true h1
  · rw [tMasks_eq]
    exact nodup_of_distinctK h2
  · rw [tMasks_eq]
    exact allLtK_spec h3

end CertificateChecks.KernelJ4Q

end
