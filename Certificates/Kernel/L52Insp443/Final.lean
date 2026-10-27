module

public import Certificates.Kernel.L52Insp443.EGlue
public import Certificates.Kernel.L52Insp443.ZGlue

public section

set_option maxRecDepth 20000

namespace CertificateChecks.KernelL52I

open CFSG.KC.Ord CFSG.KC.LQT.P CFSG.KC.Misc.GLM CFSG.KC.L52I CFSG.SectionRank.QTK.Insp443.L52
  CFSG.Sporadic.Th CFSG.Sporadic.Th.Native CFSG.Literature.GL52 CFSG.Quasithin.KGC31.Native
  CFSG.SectionRank.QTK.Insp443.PermKit.Native CFSG.Sporadic.Schreier.Native CFSG.Sporadic.Schreier

theorem chkP52_true : chkP52 () = true := by
  rw [chkP52.eq_1]
  simp only [Bool.and_eq_true, beq_iff_eq]
  refine ⟨⟨⟨⟨e16_ok, e64_ok⟩, cand_ok⟩, ?_⟩, zero_count⟩
  rw [List.all_eq_true]
  intro z hz
  rw [List.mem_range] at hz
  rw [beq_iff_eq, spZ_eq hz]
  interval_cases z
  · exact e16_count (by norm_num) ch725109t0 ch725109z0 ch725109zc0
  · exact e16_count (by norm_num) ch725109t1 ch725109z1 ch725109zc1
  · exact e16_count (by norm_num) ch725109t2 ch725109z2 ch725109zc2
  · exact e16_count (by norm_num) ch725109t3 ch725109z3 ch725109zc3
  · exact e16_count (by norm_num) ch725109t4 ch725109z4 ch725109zc4
  · exact e16_count (by norm_num) ch725109t5 ch725109z5 ch725109zc5
  · exact e16_count (by norm_num) ch725109t6 ch725109z6 ch725109zc6

end CertificateChecks.KernelL52I

end
