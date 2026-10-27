module

public import CFSG.Sporadic.J4.QT2LocCntNative
public import Certificates.Kernel.J4Q.Mask
import CFSG.Certificates.Kernel.Common.Harness
public import Certificates.Kernel.J4Q.Orbits

public section

namespace CertificateChecks.KernelJ4Q

open CFSG.KC.J4Q CFSG.KD.J4Q CFSG.Sporadic.J4.QT2

theorem mk4010_chk : Nat.beq (mkSet (fstsK (ptsK OR.s0) ++ fstsK (ptsK OR.s1)))
    (mkSet (List.range' 1 2047)) = true := by
  quickRfl

open CFSG CFSG.Sporadic CFSG.Sporadic.J4 CFSG.Sporadic.J4.QT2 in
theorem c4010 : (∀ c < 2048, c = 0 ∨ c ∈ tMasks ∨ c ∈ zMasks) := by
  refine fun c hc => ?_
  rcases Nat.eq_zero_or_pos c with h0 | h0
  · exact Or.inl h0
  · have h := mem_of_mkSet_eq mk4010_chk (List.mem_range'_1.2 ⟨h0, by omega⟩)
    rw [← tMasks_eq, ← zMasks_eq, List.mem_append] at h
    exact Or.inr h

end CertificateChecks.KernelJ4Q

end
