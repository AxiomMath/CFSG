
module

public import Certificates.Kernel.KDenseP.TwoPoint.Mono
public import CFSG.Certificates.Kernel.KDenseP.TwoPoint.C6046All
public import CFSG.Certificates.Kernel.KDenseP.TwoPoint.C6047All
public import CFSG.Certificates.Kernel.KDenseP.TwoPoint.C6048All
public import CFSG.Certificates.Kernel.KDenseP.TwoPoint.C6049All
public import CFSG.Certificates.Kernel.KDenseP.TwoPoint.C6050All
public import CFSG.Certificates.Kernel.KDenseP.TwoPoint.C6051All
public import CFSG.Certificates.Kernel.KDenseP.TwoPoint.C6052All
public import CFSG.Certificates.Kernel.KDenseP.TwoPoint.C6053All
public import CFSG.Certificates.Kernel.KDenseP.TwoPoint.C6054All
public import CFSG.Certificates.Kernel.KDenseP.TwoPoint.C6055All
public import CFSG.Certificates.Kernel.KDenseP.TwoPoint.C6056All
public import CFSG.Certificates.Kernel.KDenseP.TwoPoint.C6057All
public import CFSG.Certificates.Kernel.KDenseP.TwoPoint.C6058All
public import CFSG.Certificates.Kernel.KDenseP.TwoPoint.C6059All
public import CFSG.Certificates.Kernel.KDenseP.TwoPoint.C6060All
public import CFSG.Certificates.Kernel.KDenseP.TwoPoint.C6061All
public import CFSG.Certificates.Kernel.KDenseP.TwoPoint.C6092All
public import CFSG.Certificates.Kernel.KDenseP.TwoPoint.C6093All

public section

namespace CertificateChecks.KernelKDenseP.TwoPoint

open CFSG.KC CFSG.KC.KDense CFSG.KC.KDenseP CFSG.KC.KDenseP.TwoPoint CFSG.Monster.AxisCount
  CFSG.Monster.Existence
open CFSG.Sporadic.Bridge.Fi23GPL.Native (rels)

set_option maxRecDepth 100000

theorem c6046 :
    wordLin (fiRhoT ++ fiCGamma) = wordLin (fiCGamma ++ fiWU[0]!) ∧
      wordLin (fiRhoT ++ fiCDelta) = wordLin (fiCDelta ++ fiWDelta) := by
  have h := (kd_tp3% CFSG.KD.TP.c6046).1
  simp only [List.forall_mem_cons, List.not_mem_nil, IsEmpty.forall_iff, implies_true, and_true] at h
  exact h

theorem c6047 :
    wordLin (fiRhoT ++ fiCAlpha) = wordLin (fiCAlpha ++ fiWAlpha) ∧
      wordLin (fiWAB ++ fiCThreeA) = wordLin (fiCThreeA ++ wordThreeA) := by
  have h := (kd_tp3% CFSG.KD.TP.c6047).1
  simp only [List.forall_mem_cons, List.not_mem_nil, IsEmpty.forall_iff, implies_true, and_true] at h
  exact h

theorem c6048 :
    (∀ i ∈ List.range 10, wordLin (fiWAlpha ++ fiWU[i]!) = wordLin (fiWU[i]! ++ fiWAlpha)) ∧
      (∀ i ∈ List.range 10, wordLin (fiWBeta ++ fiWU[i]!) = wordLin (fiWU[i]! ++ fiWBeta)) ∧
      wordLin (fiWAlpha ++ fiWAlpha) = 1 ∧ wordLin (fiWBeta ++ fiWBeta) = 1 ∧
      wordLin (fiWAB ++ fiWAB ++ fiWAB) = 1 ∧ wordLin fiWAB ≠ 1 ∧ wordLin fiWU[3]! ≠ 1 := by
  obtain ⟨he, hn⟩ := kd_tp3% CFSG.KD.TP.c6048
  have hn := ne_of_tauP hn
  simp only [List.forall_mem_append, List.forall_mem_map, List.forall_mem_cons,
    List.not_mem_nil, IsEmpty.forall_iff, implies_true, and_true, wordLin_nil] at he hn
  exact ⟨he.1.1, he.1.2, he.2.1, he.2.2.1, he.2.2.2, hn.1, hn.2⟩

theorem c6049 :
    ∀ i ∈ [0, 7, 9, 17, 21, 26, 41, 47, 48, 52], wordLin (fiRelW rels[i]!) = 1 := by
  simpa only [fiRels, List.forall_mem_map, wordLin_nil] using (kd_tp3% CFSG.KD.TP.c6049).1

theorem c6050 :
    ∀ i ∈ [4, 11, 14, 22, 29, 35, 38, 45, 53], wordLin (fiRelW rels[i]!) = 1 := by
  simpa only [fiRels, List.forall_mem_map, wordLin_nil] using (kd_tp3% CFSG.KD.TP.c6050).1

theorem c6051 :
    ∀ i ∈ [5, 13, 24, 27, 31, 37, 39, 40, 49], wordLin (fiRelW rels[i]!) = 1 := by
  simpa only [fiRels, List.forall_mem_map, wordLin_nil] using (kd_tp3% CFSG.KD.TP.c6051).1

theorem c6052 :
    ∀ i ∈ [1, 3, 16, 20, 28, 32, 46, 51], wordLin (fiRelW rels[i]!) = 1 := by
  simpa only [fiRels, List.forall_mem_map, wordLin_nil] using (kd_tp3% CFSG.KD.TP.c6052).1

theorem c6053 :
    ∀ i ∈ [10, 12, 15, 25, 33, 34, 36, 42, 50, 54], wordLin (fiRelW rels[i]!) = 1 := by
  simpa only [fiRels, List.forall_mem_map, wordLin_nil] using (kd_tp3% CFSG.KD.TP.c6053).1

theorem c6054 :
    ∀ i ∈ [2, 6, 8, 18, 19, 23, 30, 43, 44], wordLin (fiRelW rels[i]!) = 1 := by
  simpa only [fiRels, List.forall_mem_map, wordLin_nil] using (kd_tp3% CFSG.KD.TP.c6054).1

theorem rel5556 :
    wordLin (fiRelW rels[55]!) = 1 ∧ wordLin (fiRelW rels[56]!) = 1 := by
  refine ⟨?_, ?_⟩
  · have e := KernelKDense.Y443.eq_of_three (w₁ := fiRelW rels[55]!) (w₂ := []) fun x hx => by
      interval_cases x
      · exact kd_one% CFSG.KD.TP.c6055 [(0, 0)] 0
      · exact kd_one% CFSG.KD.TP.c6056 [(1, 0)] 0
      · exact kd_one% CFSG.KD.TP.c6057 [(2, 0)] 0
    rwa [wordLin_nil] at e
  · exact ((kd_tp3% CFSG.KD.TP.c6058).1 _ (List.mem_map_of_mem List.mem_cons_self)).trans wordLin_nil

theorem c6055 :
    wordLin (fiRelW rels[55]!) = 1 ∧ wordLin (fiRelW rels[56]!) = 1 := rel5556

theorem c6056 :
    wordLin (fiRelW rels[55]!) = 1 ∧ wordLin (fiRelW rels[56]!) = 1 := rel5556

theorem c6057 :
    wordLin (fiRelW rels[55]!) = 1 ∧ wordLin (fiRelW rels[56]!) = 1 := rel5556

theorem c6058 :
    wordLin (fiRelW rels[55]!) = 1 ∧ wordLin (fiRelW rels[56]!) = 1 := rel5556

theorem c6059 :
    ∀ i ∈ [0, 1, 2, 3, 4, 5, 6, 7, 9],
      wordLin (s4WGamma ++ fiWU[i]!) = wordLin (fiWU[i]! ++ s4WGamma) := by
  simpa only [List.forall_mem_map] using (kd_tp3% CFSG.KD.TP.c6059).1

theorem c6060 :
    wordLin (fiRhoT ++ s4CGamma) = wordLin (s4CGamma ++ s4WGamma) ∧
      wordLin (fiRhoT ++ s4CBetaGamma) = wordLin (s4CBetaGamma ++ s4WBetaGamma) := by
  have h := (kd_tp3% CFSG.KD.TP.c6060).1
  simp only [List.forall_mem_cons, List.not_mem_nil, IsEmpty.forall_iff, implies_true, and_true] at h
  exact h

theorem c6061 :
    wordLin (s4WGamma ++ s4WGamma) = 1 ∧ wordLin (fiWU[8]! ++ fiWU[8]!) = 1 ∧
      wordLin (s4WGamma ++ fiWBeta) = wordLin (fiWBeta ++ s4WGamma) ∧
      wordLin (s4WE8Gamma ++ s4WE8Gamma ++ s4WE8Gamma) = 1 ∧
      wordLin (s4WAlphaGamma ++ s4WAlphaGamma ++ s4WAlphaGamma) = 1 ∧
      wordLin s4WE8Gamma ≠ 1 ∧ wordLin s4WAlphaGamma ≠ 1 := by
  obtain ⟨he, hn⟩ := kd_tp3% CFSG.KD.TP.c6061
  simp only [List.forall_mem_cons, List.not_mem_nil, IsEmpty.forall_iff, implies_true, and_true, wordLin_nil] at he hn
  exact ⟨he.1, he.2.1, he.2.2.1, he.2.2.2.1, he.2.2.2.2, hn.1, hn.2⟩

theorem c6092 :
    wordLin (fiRhoT ++ fiCAlphaGamma) = wordLin (fiCAlphaGamma ++ fiWAlphaGamma) := by
  have h := (kd_tp3% CFSG.KD.TP.c6092).1
  simp only [List.forall_mem_cons, List.not_mem_nil, IsEmpty.forall_iff, implies_true, and_true] at h
  exact h

theorem c6093 :
    wordLin (fiRhoT ++ fiCT2) = wordLin (fiCT2 ++ fiWT2) ∧
      wordLin (gxXWord ++ fiCT2Alpha) = wordLin (fiCT2Alpha ++ (fiWT2 ++ fiWAlpha)) := by
  have h := (kd_tp3% CFSG.KD.TP.c6093).1
  simp only [List.forall_mem_cons, List.not_mem_nil, IsEmpty.forall_iff, implies_true, and_true] at h
  exact h

end CertificateChecks.KernelKDenseP.TwoPoint

end
