module

public import Certificates.Kernel.Mathieu.RootData
public import Certificates.Kernel.Mathieu.M11Chains
public import CFSG.Certificates.Kernel.Mathieu.SylowSoundK
public import CFSG.Sporadic.Mathieu.M11
import CFSG.Certificates.Kernel.Common.Harness
import Mathlib.Tactic.IntervalCases

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelMathieu

open CFSG.KD.Mathieu CFSG.Monster.B.Mathieu CFSG.KC.MathieuK CFSG.Sporadic.Mathieu

theorem syl11 : ∀ s ∈ m11RecordK.sylows,
    SylowFacts (Subgroup.closure {m11gA, m11gB}) 7920 [m11gA, m11gB] s := by
  obtain ⟨hcard, hA, hB, hAi, hBi, hsz, hsift⟩ := root_of_K (r := m11RecordK) (a := m11gA)
    (b := m11gB) (by norm_num) (by norm_num) (by norm_num) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by quickRfl) (by quickRfl) (by decide +kernel)
    Root11.c0.ok (by decide +kernel)
  have hG : Nat.card (Subgroup.closure {m11gA, m11gB}) = 7920 :=
    hcard.trans (by decide +kernel)
  refine sylows_of_fam (ks := [4, 2, 1, 1]) (BL := m11PB) (by norm_num) (by norm_num) hsz hG
    hA hB hAi hBi hsift (by decide +kernel) P11.all ?_ (by quickRfl) ?_
  · intro s hs
    have hp : m11RecordK.sylows.map (·.prime) = [2, 3, 5, 11] := by decide +kernel
    have := List.mem_map_of_mem (f := (·.prime)) hs
    rw [hp] at this
    simp only [List.mem_cons, List.not_mem_nil, or_false] at this
    rcases this with h | h | h | h <;> rw [h] <;> norm_num
  · intro j hj
    have hl : m11RecordK.sylows.length = 4 := by decide +kernel
    rw [hl] at hj
    interval_cases j
    · exact ngOK_of_fam rfl (by decide +kernel) N11s0.all (by quickRfl)
    · exact ngOK_of_fam rfl (by decide +kernel) N11s1.all (by quickRfl)
    · exact ngOK_of_fam rfl (by decide +kernel) N11s2.all (by quickRfl)
    · exact ngOK_of_fam rfl (by decide +kernel) N11s3.all (by quickRfl)

end CertificateChecks.KernelMathieu

end
