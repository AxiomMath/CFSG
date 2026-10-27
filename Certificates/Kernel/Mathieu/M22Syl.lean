module

public import Certificates.Kernel.Mathieu.RootData
public import Certificates.Kernel.Mathieu.M22Chains
public import CFSG.Certificates.Kernel.Mathieu.SylowSoundK
public import CFSG.Sporadic.Mathieu.M22
import CFSG.Certificates.Kernel.Common.Harness
import Mathlib.Tactic.IntervalCases

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelMathieu

open CFSG.KD.Mathieu CFSG.Monster.B.Mathieu CFSG.KC.MathieuK CFSG.Sporadic.Mathieu

theorem syl22 : ∀ s ∈ m22RecordK.sylows,
    SylowFacts (Subgroup.closure {m22gA, m22gB}) 443520 [m22gA, m22gB] s := by
  obtain ⟨hcard, hA, hB, hAi, hBi, hsz, hsift⟩ := root_of_K (r := m22RecordK) (a := m22gA)
    (b := m22gB) (by norm_num) (by norm_num) (by norm_num) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by quickRfl) (by quickRfl) (by decide +kernel) Root22.c0.ok
    (by decide +kernel)
  have hG : Nat.card (Subgroup.closure {m22gA, m22gB}) = 443520 :=
    hcard.trans (by decide +kernel)
  refine sylows_of_fam (ks := [7, 2, 1, 1, 1]) (BL := m22PB) (by norm_num) (by norm_num) hsz hG
    hA hB hAi hBi hsift (by decide +kernel) P22.all ?_ (by quickRfl) ?_
  · intro s hs
    have hp : m22RecordK.sylows.map (·.prime) = [2, 3, 5, 7, 11] := by decide +kernel
    have := List.mem_map_of_mem (f := (·.prime)) hs
    rw [hp] at this
    simp only [List.mem_cons, List.not_mem_nil, or_false] at this
    rcases this with h | h | h | h | h <;> rw [h] <;> norm_num
  · intro j hj
    have hl : m22RecordK.sylows.length = 5 := by decide +kernel
    rw [hl] at hj
    interval_cases j
    · exact ngOK_of_fam rfl (by decide +kernel) N22s0.all (by quickRfl)
    · exact ngOK_of_fam rfl (by decide +kernel) N22s1.all (by quickRfl)
    · exact ngOK_of_fam rfl (by decide +kernel) N22s2.all (by quickRfl)
    · exact ngOK_of_fam rfl (by decide +kernel) N22s3.all (by quickRfl)
    · exact ngOK_of_fam rfl (by decide +kernel) N22s4.all (by quickRfl)

end CertificateChecks.KernelMathieu

end
