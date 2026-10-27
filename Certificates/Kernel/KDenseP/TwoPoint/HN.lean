module

public import Certificates.Kernel.KDenseP.TwoPoint.Mono
public import CFSG.Certificates.Kernel.KDenseP.TwoPoint.C6073All
public import CFSG.Certificates.Kernel.KDenseP.TwoPoint.C6074All
public import CFSG.Certificates.Kernel.KDenseP.TwoPoint.C6075All
public import CFSG.Certificates.Kernel.KDenseP.TwoPoint.C6076All
public import CFSG.Certificates.Kernel.KDenseP.TwoPoint.C6077All
public import CFSG.Certificates.Kernel.KDenseP.TwoPoint.C6078All
public import CFSG.Certificates.Kernel.KDenseP.TwoPoint.C6079All

public section

namespace CertificateChecks.KernelKDenseP.TwoPoint

open CFSG.KC CFSG.KC.KDense CFSG.KC.KDenseP CFSG.KC.KDenseP.TwoPoint CFSG.Monster.AxisCount
  CFSG.Monster.Existence
open CFSG.Sporadic.Bridge.SurjD.Native (hnRels)

set_option maxRecDepth 100000

theorem c6073 :
    wordLin (hnRhoT ++ hnCAlpha) = wordLin (hnCAlpha ++ hnWAlpha) ∧
      wordLin (hnRhoT ++ hnCBeta) = wordLin (hnCBeta ++ hnWBeta) ∧ wordLin hnWAB5 = 1 := by
  have h := (kd_tp3% CFSG.KD.TP.c6073).1
  simp only [List.forall_mem_cons, List.not_mem_nil, IsEmpty.forall_iff, implies_true, and_true, wordLin_nil] at h
  exact h

theorem c6074 :
    (∀ i ∈ List.range 5, wordLin (hnWU[i]! ++ hnWV[i]!) = 1) ∧
      (∀ i ∈ List.range 5, wordLin (hnWAlpha ++ hnWU[i]!) = wordLin (hnWU[i]! ++ hnWAlpha)) ∧
      (∀ i ∈ List.range 5, wordLin (hnWBeta ++ hnWU[i]!) = wordLin (hnWU[i]! ++ hnWBeta)) ∧
      wordLin hnWAB ≠ 1 ∧ wordLin hnWU[4]! ≠ 1 := by
  obtain ⟨he, hn⟩ := kd_tp3% CFSG.KD.TP.c6074
  simp only [List.forall_mem_append, List.forall_mem_map, List.forall_mem_cons,
    List.not_mem_nil, IsEmpty.forall_iff, implies_true, and_true, wordLin_nil] at he hn
  exact ⟨he.1.1, he.1.2, he.2, hn.1, hn.2⟩

theorem c6075 :
    ∀ i ∈ [4, 5, 6, 7, 10, 11, 12], wordLin (hnRelW hnRels[i]!) = 1 := by
  simpa only [hnR, List.forall_mem_map, wordLin_nil] using (kd_tp3% CFSG.KD.TP.c6075).1

theorem c6076 :
    ∀ i ∈ [0, 1, 2, 3, 8, 9], wordLin (hnRelW hnRels[i]!) = 1 := by
  simpa only [hnR, List.forall_mem_map, wordLin_nil] using (kd_tp3% CFSG.KD.TP.c6076).1

theorem c6077 :
    ∀ i ∈ [13, 14, 15], wordLin (hnRelW hnRels[i]!) = 1 := by
  simpa only [hnR, List.forall_mem_map, wordLin_nil] using (kd_tp3% CFSG.KD.TP.c6077).1

theorem c6078 :
    ∀ i ∈ [16, 17, 18], wordLin (hnRelW hnRels[i]!) = 1 := by
  simpa only [hnR, List.forall_mem_map, wordLin_nil] using (kd_tp3% CFSG.KD.TP.c6078).1

theorem c6079 :
    wordLin (hnXWord ++ hnCW) = wordLin (hnCW ++ hnWW) := by
  have h := (kd_tp3% CFSG.KD.TP.c6079).1
  simp only [List.forall_mem_cons, List.not_mem_nil, IsEmpty.forall_iff, implies_true, and_true] at h
  exact h

end CertificateChecks.KernelKDenseP.TwoPoint

end
