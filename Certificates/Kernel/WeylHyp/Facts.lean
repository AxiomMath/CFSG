module

public import Certificates.Kernel.WeylHyp.Small
public import Certificates.Kernel.WeylHyp.E7_0
public import Certificates.Kernel.WeylHyp.E7_1
public import Certificates.Kernel.WeylHyp.E7_2
public import Certificates.Kernel.WeylHyp.E8h_0
public import Certificates.Kernel.WeylHyp.E8h_1
public import Certificates.Kernel.WeylHyp.E8h_2
public import Certificates.Kernel.WeylHyp.E8h_3
public import Certificates.Kernel.WeylHyp.E8h_4
public import Certificates.Kernel.WeylHyp.E8h_5
public import Certificates.Kernel.WeylHyp.E8h_6
public import Certificates.Kernel.WeylHyp.E8h_7
public import Certificates.Kernel.WeylHyp.E8h_8
public import Certificates.Kernel.WeylHyp.E8h_9
public import Certificates.Kernel.WeylHyp.E8h_10
public import Certificates.Kernel.WeylHyp.E8h_11
public import Certificates.Kernel.WeylHyp.E8h_12
public import Certificates.Kernel.WeylHyp.E8h_13
public import Certificates.Kernel.WeylHyp.E8h_14
public import Certificates.Kernel.WeylHyp.E8h_15
public import Certificates.Kernel.WeylHyp.E8h_16

public section

namespace CertificateChecks.KernelWeylHyp

open CFSG.HardMathSupport.Timmesfeld.CrossChar.SmallQ3.Native CFSG.Blueprint.Chevalley
  Timmesfeld.Co1Leaf

theorem all_of_slices {α : Type} (l : List α) (p : α → Bool) (n : Nat) (hl : l.length ≤ 40 * n)
    (h : ∀ k < n, ((l.drop (40 * k)).take 40).all p = true) : l.all p = true := by
  rw [List.all_eq_true]
  intro x hx
  obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hx
  have hs := List.all_eq_true.1 (h (i / 40) (by omega))
  have hj : i % 40 < ((l.drop (40 * (i / 40))).take 40).length := by
    simp only [List.length_take, List.length_drop]
    omega
  have e : ((l.drop (40 * (i / 40))).take 40)[i % 40] = l[i] := by
    simp only [List.getElem_take, List.getElem_drop, Nat.div_add_mod]
  rw [← e]
  exact hs _ (List.getElem_mem hj)

theorem e7_all : ∀ k < 30, sliceOK .E7 k = true := by
  intro k hk
  rw [sliceOK_E7]
  have hk' : k = 10 * (k / 10) + k % 10 := (Nat.div_add_mod k 10).symm
  have hr : k % 10 < 10 := Nat.mod_lt _ (by decide)
  have hq : k / 10 < 3 := by omega
  rw [hk']
  generalize k / 10 = q at hq
  generalize k % 10 = s at hr
  interval_cases q
  · exact E7_0.H.all s hr
  · exact E7_1.H.all s hr
  · exact E7_2.H.all s hr

theorem e8_all : ∀ k < 90, sliceOK .E8 k = true := by
  intro k hk
  rw [sliceOK_E8]
  by_cases hl : 80 ≤ k
  · have h10 : k - 80 < 10 := by omega
    have h := E8h_16.H.all (k - 80) h10
    rwa [E8h_16.f, Nat.add_sub_cancel' hl] at h
  have hk' : k = 5 * (k / 5) + k % 5 := (Nat.div_add_mod k 5).symm
  have hr : k % 5 < 5 := Nat.mod_lt _ (by decide)
  have hq : k / 5 < 16 := by omega
  rw [hk']
  generalize k / 5 = q at hq
  generalize k % 5 = s at hr
  interval_cases q
  · exact E8h_0.H.all s hr
  · exact E8h_1.H.all s hr
  · exact E8h_2.H.all s hr
  · exact E8h_3.H.all s hr
  · exact E8h_4.H.all s hr
  · exact E8h_5.H.all s hr
  · exact E8h_6.H.all s hr
  · exact E8h_7.H.all s hr
  · exact E8h_8.H.all s hr
  · exact E8h_9.H.all s hr
  · exact E8h_10.H.all s hr
  · exact E8h_11.H.all s hr
  · exact E8h_12.H.all s hr
  · exact E8h_13.H.all s hr
  · exact E8h_14.H.all s hr
  · exact E8h_15.H.all s hr

theorem hypE7 : hypOK .E7 = true := by
  have h : ((normVecs 3 7).all (famAt .E7) && famOK0 (gramL .E7) (rootsN .E7) (simpleL .E7)
      ((simpleL .E7).map fun e => formB (gramL .E7) e e) (stdBasis 7)) = true := by
    simp only [Bool.and_eq_true]
    exact ⟨all_of_slices _ _ 30 len7 e7_all, std7⟩
  exact h

theorem hypE8 : hypOK .E8 = true := by
  have h : ((normVecs 3 8).all (famAt .E8) && famOK0 (gramL .E8) (rootsN .E8) (simpleL .E8)
      ((simpleL .E8).map fun e => formB (gramL .E8) e e) (stdBasis 8)) = true := by
    simp only [Bool.and_eq_true]
    exact ⟨all_of_slices _ _ 90 len8 e8_all, std8⟩
  exact h

end CertificateChecks.KernelWeylHyp

end
