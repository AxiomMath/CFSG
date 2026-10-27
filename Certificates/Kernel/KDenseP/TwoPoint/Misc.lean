module

public import Certificates.Kernel.KDenseP.TwoPoint.Mono
public import CFSG.Certificates.Kernel.KDenseP.TwoPoint.C6091All
public import CFSG.Certificates.Kernel.KDenseP.TwoPoint.C6094All
public import CFSG.Certificates.Kernel.KDenseP.TwoPoint.C6095All
public import CFSG.Certificates.Kernel.KDenseP.TwoPoint.C6096All

public section

namespace CertificateChecks.KernelKDenseP.TwoPoint

open CFSG.KC CFSG.KC.KDense CFSG.KC.KDenseP CFSG.KC.KDenseP.TwoPoint CFSG.Monster.AxisCount
  CFSG.Monster.Existence

set_option maxRecDepth 100000

theorem c6091 :
    wordLin (wordThreeA ++ wordKA) = wordLin (wordKA ++ wordMonoA) ∧
      wordLin (wordMonoA ++ wordMonoA ++ wordMonoA) = 1 ∧
      wordLin (wordThreeC ++ wordKC) = wordLin (wordKC ++ wordMonoC) ∧
      wordLin (wordMonoC ++ wordMonoC ++ wordMonoC) = 1 := by
  have h := (kd_tp3% CFSG.KD.TP.c6091).1
  simp only [List.forall_mem_cons, List.not_mem_nil, IsEmpty.forall_iff, implies_true, and_true, wordLin_nil] at h
  exact h

theorem c6091v : Native.permValid permMonoA = true ∧ Native.permValid permMonoC = true := by
  have h := kd_tp3v% CFSG.KD.TP.c6091
  exact ⟨(h _ (List.mem_cons_of_mem _ List.mem_cons_self)).1 (.perm permMonoA) (by simp [wordMonoA]),
    (h _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
      List.mem_cons_self)))).1 (.perm permMonoC) (by simp [wordMonoC])⟩

theorem c6094 : wordLin (y433RelW y433F213R) = 1 := by
  have h := (kd_tp3% CFSG.KD.TP.c6094).1
  simp only [List.forall_mem_cons, List.not_mem_nil, IsEmpty.forall_iff, implies_true, and_true, wordLin_nil] at h
  exact h

theorem c6095 : wordLin (y433RelW y433F312R) = wordLin fiWBeta := by
  have h := (kd_tp3% CFSG.KD.TP.c6095).1
  simp only [List.forall_mem_cons, List.not_mem_nil, IsEmpty.forall_iff, implies_true, and_true] at h
  exact h

theorem c6096 : wordLin (y433RelW y433SpiderR) = 1 := by
  have h := (kd_tp3% CFSG.KD.TP.c6096).1
  simp only [List.forall_mem_cons, List.not_mem_nil, IsEmpty.forall_iff, implies_true, and_true, wordLin_nil] at h
  exact h

end CertificateChecks.KernelKDenseP.TwoPoint

end
