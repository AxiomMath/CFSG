module

public import Certificates.Kernel.KDenseP.TwoPoint.Mono
public import CFSG.Certificates.Kernel.KDenseP.TwoPoint.C6080All
public import CFSG.Certificates.Kernel.KDenseP.TwoPoint.C6081All
public import CFSG.Certificates.Kernel.KDenseP.TwoPoint.C6082All
public import CFSG.Certificates.Kernel.KDenseP.TwoPoint.C6083All
public import CFSG.Certificates.Kernel.KDenseP.TwoPoint.C6084All
public import CFSG.Certificates.Kernel.KDenseP.TwoPoint.C6085All
public import CFSG.Certificates.Kernel.KDenseP.TwoPoint.C6086All
public import CFSG.Certificates.Kernel.KDenseP.TwoPoint.C6087All
public import CFSG.Certificates.Kernel.KDenseP.TwoPoint.C6088All
public import CFSG.Certificates.Kernel.KDenseP.TwoPoint.C6089All
public import CFSG.Certificates.Kernel.KDenseP.TwoPoint.C6090All

public section

namespace CertificateChecks.KernelKDenseP.TwoPoint

open CFSG.KC CFSG.KC.KDense CFSG.KC.KDenseP CFSG.KC.KDenseP.TwoPoint CFSG.Monster.AxisCount
  CFSG.Monster.Existence

set_option maxRecDepth 100000

theorem c6080 :
    ∀ i ∈ List.range 8, wordLin (thWAlpha ++ thWU[i]!) = wordLin (thWU[i]! ++ thWAlpha) := by
  simpa only [List.forall_mem_map] using (kd_tp3% CFSG.KD.TP.c6080).1

theorem c6081 :
    ∀ i ∈ List.range 8, wordLin (thWBeta ++ thWU[i]!) = wordLin (thWU[i]! ++ thWBeta) := by
  simpa only [List.forall_mem_map] using (kd_tp3% CFSG.KD.TP.c6081).1

theorem c6082 :
    (wordLin (thRhoT ++ thCAlpha) = wordLin (thCAlpha ++ thWAlpha) ∧
      wordLin (thRhoT ++ thCBeta) = wordLin (thCBeta ++ thWBeta)) ∧
      wordLin (wordThreeC ++ thWG) = wordLin (thWG ++ thWAB) := by
  have h := (kd_tp3% CFSG.KD.TP.c6082).1
  simp only [List.forall_mem_cons, List.not_mem_nil, IsEmpty.forall_iff, implies_true, and_true] at h
  exact ⟨⟨h.1, h.2.1⟩, h.2.2⟩

theorem c6083 :
    (∀ i ∈ List.range 8, wordLin (thWU[i]! ++ thWV[i]!) = 1) ∧ wordLin thWAB3 = 1 ∧
      wordLin thWAB ≠ 1 ∧ wordLin thWS7 = 1 ∧ wordLin thWU[5]! ≠ 1 := by
  obtain ⟨he, hn⟩ := kd_tp3% CFSG.KD.TP.c6083
  have hn := ne_of_tauP hn
  simp only [List.forall_mem_append, List.forall_mem_map, List.forall_mem_cons,
    List.not_mem_nil, IsEmpty.forall_iff, implies_true, and_true, wordLin_nil] at he hn
  exact ⟨he.1, he.2.1, hn.1, he.2.2, hn.2⟩

theorem c6084 :
    ∀ i ∈ [13], wordLin (thRelW TauCeti.Sporadic.Thompson.presentation.relatorLetters[i]!) = 1 := by
  simpa only [thR, List.forall_mem_map, wordLin_nil] using (kd_tp3% CFSG.KD.TP.c6084).1

theorem c6085 :
    ∀ i ∈ [0, 2, 33, 35],
      wordLin (thRelW TauCeti.Sporadic.Thompson.presentation.relatorLetters[i]!) = 1 := by
  simpa only [thR, List.forall_mem_map, wordLin_nil] using (kd_tp3% CFSG.KD.TP.c6085).1

theorem c6086 :
    ∀ i ∈ [7, 14, 38],
      wordLin (thRelW TauCeti.Sporadic.Thompson.presentation.relatorLetters[i]!) = 1 := by
  simpa only [thR, List.forall_mem_map, wordLin_nil] using (kd_tp3% CFSG.KD.TP.c6086).1

theorem c6087 :
    ∀ i ∈ [5, 32, 37],
      wordLin (thRelW TauCeti.Sporadic.Thompson.presentation.relatorLetters[i]!) = 1 := by
  simpa only [thR, List.forall_mem_map, wordLin_nil] using (kd_tp3% CFSG.KD.TP.c6087).1

theorem c6088 :
    ∀ i ∈ [3, 8, 9, 16, 19, 22],
      wordLin (thRelW TauCeti.Sporadic.Thompson.presentation.relatorLetters[i]!) = 1 := by
  simpa only [thR, List.forall_mem_map, wordLin_nil] using (kd_tp3% CFSG.KD.TP.c6088).1

theorem c6089 :
    ∀ i ∈ [1, 10, 12, 18, 24, 25, 26, 28, 30, 31, 34, 36],
      wordLin (thRelW TauCeti.Sporadic.Thompson.presentation.relatorLetters[i]!) = 1 := by
  simpa only [thR, List.forall_mem_map, wordLin_nil] using (kd_tp3% CFSG.KD.TP.c6089).1

theorem c6090 :
    ∀ i ∈ [4, 6, 11, 15, 17, 20, 21, 23, 27, 29],
      wordLin (thRelW TauCeti.Sporadic.Thompson.presentation.relatorLetters[i]!) = 1 := by
  simpa only [thR, List.forall_mem_map, wordLin_nil] using (kd_tp3% CFSG.KD.TP.c6090).1

end CertificateChecks.KernelKDenseP.TwoPoint

end
