module

public import Certificates.Kernel.Sporadic.Fi24Sev.DataT
import CFSG.Certificates.Kernel.Common.Harness

public section

namespace CFSG.KD.Fi24Sev.Ck

open CFSG.KD.Fi24Sev CFSG.KD.Fi24Kit

theorem relA_t : CFSG.KD.Fi24Sev.relA = true := by
  have h : relOKT NT wrA wsA = true := by quickRfl
  rw [relOKT_eq] at h
  exact h

theorem relB_t : CFSG.KD.Fi24Sev.relB = true := by
  have h : relOKT NT wrB wsB = true := by quickRfl
  rw [relOKT_eq] at h
  exact h

theorem refA_t : CFSG.KD.Fi24Sev.refA = true := by
  have h : refsOKT NT OL wrA omA repsA rfA = true := by quickRfl
  rw [refsOKT_eq] at h
  exact h

theorem refB_t : CFSG.KD.Fi24Sev.refB = true := by
  have h : refsOKT NT OL wrB omB repsB rfB = true := by quickRfl
  rw [refsOKT_eq] at h
  exact h

theorem baseA_t : CFSG.KD.Fi24Sev.baseA = true := by quickRfl
theorem baseB_t : CFSG.KD.Fi24Sev.baseB = true := by quickRfl
theorem mv4_t : CFSG.KD.Fi24Sev.mv4 = true := by quickRfl
theorem twin_t : CFSG.KD.Fi24Sev.twin = true := by quickRfl

theorem slc_t : CFSG.KD.Fi24Sev.slc = true := by
  have h : slOKT NT sl = true := by quickRfl
  rw [slOKT_eq] at h
  exact h

end CFSG.KD.Fi24Sev.Ck

end
