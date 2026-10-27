module

public import Certificates.Kernel.KDenseP.TwoPoint.Mono
public import CFSG.Certificates.Kernel.KDenseP.TwoPoint.C6063All
public import CFSG.Certificates.Kernel.KDenseP.TwoPoint.C6064All
public import CFSG.Certificates.Kernel.KDenseP.TwoPoint.C6065All
public import CFSG.Certificates.Kernel.KDenseP.TwoPoint.C6066All
public import CFSG.Certificates.Kernel.KDenseP.TwoPoint.C6067All
public import CFSG.Certificates.Kernel.KDenseP.TwoPoint.C6068All
public import CFSG.Certificates.Kernel.KDenseP.TwoPoint.C6069All
public import CFSG.Certificates.Kernel.KDenseP.TwoPoint.C6070All
public import CFSG.Certificates.Kernel.KDenseP.TwoPoint.C6071All
public import CFSG.Certificates.Kernel.KDenseP.TwoPoint.C6072All

public section

namespace CertificateChecks.KernelKDenseP.TwoPoint

open CFSG.KC CFSG.KC.KDense CFSG.KC.KDenseP CFSG.KC.KDenseP.TwoPoint CFSG.Monster.AxisCount
  CFSG.Monster.B.Short CFSG.Monster.Existence

set_option maxRecDepth 100000

theorem mem_gxNode_alpha {j : ℕ} (h9 : j ≠ 9) : (yW j ++ fiWAlpha, yW j) ∈ gxNode j := by
  unfold gxNode
  rw [ite_eq_right h9]
  exact List.mem_append_left _ (List.mem_singleton_self _)

theorem mem_gxNode_bp (j : ℕ) : (yW j ++ bpW, yW j) ∈ gxNode j := by
  unfold gxNode
  exact List.mem_append_right _ (List.mem_singleton_self _)

theorem gx_ok {js : List ℕ}
    (h : ∀ e ∈ js.flatMap gxNode, wordLin e.1 aStar ≠ wordLin e.2 aStar) :
    ∀ j ∈ js, (j ≠ 9 → wordLin (yW j ++ fiWAlpha) aStar ≠ wordLin (yW j) aStar) ∧
      wordLin (yW j ++ bpW) aStar ≠ wordLin (yW j) aStar := fun j hj =>
  ⟨fun h9 => h _ (List.mem_flatMap.2 ⟨j, hj, mem_gxNode_alpha h9⟩),
    h _ (List.mem_flatMap.2 ⟨j, hj, mem_gxNode_bp j⟩)⟩

theorem c6063 :
    ∀ j ∈ [2, 3, 4, 5], wordLin (yW j ++ fiWAlpha) aStar ≠ wordLin (yW j) aStar ∧
      wordLin (yW j ++ bpW) aStar ≠ wordLin (yW j) aStar := fun j hj =>
  have h := gx_ok (kd_axis% CFSG.KD.TP.c6063 17 p6063) j hj
  ⟨h.1 (by simp at hj; omega), h.2⟩

theorem c6064 :
    ∀ j ∈ [6, 7, 8], wordLin (yW j ++ fiWAlpha) aStar ≠ wordLin (yW j) aStar ∧
      wordLin (yW j ++ bpW) aStar ≠ wordLin (yW j) aStar := fun j hj =>
  have h := gx_ok (kd_axis% CFSG.KD.TP.c6064 18 p6064) j hj
  ⟨h.1 (by simp at hj; omega), h.2⟩

theorem c6065 :
    wordLin (yW 9 ++ bpW) aStar ≠ wordLin (yW 9) aStar ∧
      wordLin (yW 10 ++ fiWAlpha) aStar ≠ wordLin (yW 10) aStar ∧
      wordLin (yW 10 ++ bpW) aStar ≠ wordLin (yW 10) aStar :=
  have h := gx_ok (kd_axis% CFSG.KD.TP.c6065 19 p6065)
  ⟨(h 9 (by simp)).2, (h 10 (by simp)).1 (by decide), (h 10 (by simp)).2⟩

theorem c6066 :
    ∀ j ∈ [11, 12], wordLin (yW j ++ fiWAlpha) aStar ≠ wordLin (yW j) aStar ∧
      wordLin (yW j ++ bpW) aStar ≠ wordLin (yW j) aStar := fun j hj =>
  have h := gx_ok (kd_axis% CFSG.KD.TP.c6066 19 p6066) j hj
  ⟨h.1 (by simp at hj; omega), h.2⟩

theorem c6067 :
    ∀ j ∈ [13, 14], wordLin (yW j ++ fiWAlpha) aStar ≠ wordLin (yW j) aStar ∧
      wordLin (yW j ++ bpW) aStar ≠ wordLin (yW j) aStar := fun j hj =>
  have h := gx_ok (kd_axis% CFSG.KD.TP.c6067 26 p6067) j hj
  ⟨h.1 (by simp at hj; omega), h.2⟩

theorem c6068 :
    ∀ j ∈ [15, 16], wordLin (yW j ++ fiWAlpha) aStar ≠ wordLin (yW j) aStar ∧
      wordLin (yW j ++ bpW) aStar ≠ wordLin (yW j) aStar := fun j hj =>
  have h := gx_ok (kd_axis% CFSG.KD.TP.c6068 20 p6068) j hj
  ⟨h.1 (by simp at hj; omega), h.2⟩

theorem c6069 :
    ∀ j ∈ [17, 18], wordLin (yW j ++ fiWAlpha) aStar ≠ wordLin (yW j) aStar ∧
      wordLin (yW j ++ bpW) aStar ≠ wordLin (yW j) aStar := fun j hj =>
  have h := gx_ok (kd_axis% CFSG.KD.TP.c6069 24 p6069) j hj
  ⟨h.1 (by simp at hj; omega), h.2⟩

theorem c6070 :
    ∀ j ∈ [19, 20], wordLin (yW j ++ fiWAlpha) aStar ≠ wordLin (yW j) aStar ∧
      wordLin (yW j ++ bpW) aStar ≠ wordLin (yW j) aStar := fun j hj =>
  have h := gx_ok (kd_axis% CFSG.KD.TP.c6070 17 p6070) j hj
  ⟨h.1 (by simp at hj; omega), h.2⟩

theorem c6071 :
    ∀ j ∈ [21, 22], wordLin (yW j ++ fiWAlpha) aStar ≠ wordLin (yW j) aStar ∧
      wordLin (yW j ++ bpW) aStar ≠ wordLin (yW j) aStar := by
  have h := kd_axis% CFSG.KD.TP.c6071 21 p6071
  simp only [p6071, List.forall_mem_append] at h
  obtain ⟨⟨h1, h2⟩, h3⟩ := h
  intro j hj
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hj
  rcases hj with rfl | rfl
  · exact ⟨apply_ne_of_tauP h1 _ List.mem_cons_self, h2 _ List.mem_cons_self⟩
  · exact ⟨h3 _ (mem_gxNode_alpha (by decide)), h3 _ (mem_gxNode_bp 22)⟩

theorem c6072 :
    wordLin (gxXWord ++ gxCW9) = wordLin (gxCW9 ++ gxProdWord (gxXList 9)) := by
  have h := (kd_tp3% CFSG.KD.TP.c6072 24).1
  simp only [List.forall_mem_cons, List.not_mem_nil, IsEmpty.forall_iff, implies_true, and_true] at h
  exact h

end CertificateChecks.KernelKDenseP.TwoPoint

end
