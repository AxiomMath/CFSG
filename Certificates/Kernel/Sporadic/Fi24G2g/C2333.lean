module

public import Certificates.Kernel.Sporadic.Fi24G2g.Triple
public import Certificates.Kernel.Sporadic.Fi24G2g.Reps

public section

namespace CertificateChecks.KernelFi24G2g

open CertificateChecks.KernelFi24 CertificateChecks.KernelFi24G2e TauCeti TauCeti.Sporadic

open CFSG.Sporadic.Fi24 (R tR cls D24)
open CFSG.Sporadic.FischerOddCore (fi23ToR fi23U2 fi23U3)
open CFSG.KD.Fi24G2e (CWL)
open CFSG.Sporadic.FischerOddCore (TripleFacts rep7)

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent


theorem CWL_4 : CWL 4 = [2] := by decide +kernel

theorem CWL_5 : CWL 5 = CFSG.KD.Fi24G2d.W2D := by decide +kernel

theorem CWL_6 : CWL 6 = CFSG.KD.Fi24G2d.W2D := by decide +kernel

theorem outer2333_facts (hP : PtRank) :
    rep7 4 ∈ D24 ∧ TripleFacts (rep7 5) ∧ TripleFacts (rep7 6) := by
  refine ⟨?_, ?_, ?_⟩
  · obtain ⟨c, hc⟩ := conj_rep7 (i := 4) (by norm_num)
    have hl : ρ (wp [2]) = cls (pk (r := 22978) (by norm_num)) := by
      rw [(cls_own hP).2.1]
      simp [wp]
    rw [CWL_4, hl] at hc
    have e : rep7 4 = c⁻¹ * cls (pk (r := 22978) (by norm_num)) * c⁻¹⁻¹ := by
      rw [← hc, inv_inv]
      group
    rw [e]
    exact CFSG.Sporadic.Fi24.conj_mem_D24 _ (CFSG.Sporadic.Fi24.cls_mem _)
  · obtain ⟨c, hc⟩ := conj_rep7 (i := 5) (by norm_num)
    rw [CWL_5] at hc
    exact (tripleFacts_W2D hP).conj hc
  · obtain ⟨c, hc⟩ := conj_rep7 (i := 6) (by norm_num)
    rw [CWL_6] at hc
    exact (tripleFacts_W2D hP).conj hc

end CertificateChecks.KernelFi24G2g

end
