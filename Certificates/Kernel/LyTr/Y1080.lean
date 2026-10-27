module

public import Certificates.Kernel.LyTr.Tau
public import Certificates.Kernel.LyTr.Checks1080
public import Certificates.Kernel.LyTr.ChecksR1ClA
public import Certificates.Kernel.LyTr.ChecksR1ClB
public import Certificates.Kernel.LyTr.ChecksR1ClC
public import Certificates.Kernel.LyTr.ChecksR1ClD
public import Certificates.Kernel.LyTr.ChecksR1ClE

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelLyTr

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KS.PEnum CFSG.KS.MulH CFSG.KC.BfsPin
open CFSG.Sporadic.Th.Native CFSG.Sporadic.Schreier.Native CFSG.Sporadic.SmallOddCore
open CFSG.Sporadic.SmallOddCore.Native CFSG.Sporadic.Recognition.LyonsSims

theorem y0 : C11 (SH.F 0) ∧ i11 (SH.F 0) (SH.F 0) = true ∧
    Nat.beq (p11 (SH.F 0) (SH.F 0)) id11 = true ∧
    ∀ j < 5, C11 (R1I j) ∧ i11 (R1.GI j) (R1I j) = true := by
  have h := k_y0
  simp only [bAnd_iff] at h
  obtain ⟨a1, a2, a3, a4⟩ := h
  refine ⟨a1, a2, a3, fun j hj => ?_⟩
  have e := allN_spec a4 j hj
  simp only [bAnd_iff] at e
  exact e

theorem sigT : Ly1080.sigmaTab = tabT (unpack 1080 11 (SH.F 0)) := by
  have h := CFSG.KC.Misc.HexFlat.hexT_sound SH.all (by norm_num) 0 (by norm_num)
  rw [← SH.eq, Nat.mul_zero] at h
  exact tab_of_nat h

theorem r1gc {j : Nat} (hj : j < 5) : C11 (R1.GI j) := (base11.2.2.2.2.1 j hj).1

theorem txy1080IT {j : Nat} (hj : j < 5) :
    Ly1080.txyInvTabs[j]! = tabT (unpack 1080 11 (R1I j)) := by
  have hs : Ly1080.txyWords.length = 5 := by decide
  unfold Ly1080.txyInvTabs
  rw [get_map (by simp [Ly1080.txyTabs, hs]; omega), txy1080T hj,
    invT_unpack (by norm_num) (y0.2.2.2 j hj).2]

theorem tab_ok11 {X Xi : Nat} (hX : C11 X) (hXi : C11 Xi) (h : i11 X Xi = true) :
    permOK 1080 (tabT (unpack 1080 11 X)) = true ∧
      invOK 1080 (tabT (unpack 1080 11 X)) (invT 1080 (tabT (unpack 1080 11 X))) = true := by
  rw [invT_unpack (by norm_num) h]
  exact ⟨permOK_unpack hX h, invOK_unpack hX hXi h⟩

theorem sz_u1080 : Ly1080.uTabs.size = 4 := by simp [Ly1080.uTabs]

theorem sz_txy1080 : Ly1080.txyTabs.size = 5 := by
  have hs : Ly1080.txyWords.length = 5 := by decide
  simp [Ly1080.txyTabs, hs]

theorem tablesOK1080_of : Ly1080.tablesOK = true := by
  have hw : Ly1080.wordsOK = true := by decide +kernel
  obtain ⟨hs, hsi, hss, hr⟩ := y0
  unfold Ly1080.tablesOK
  simp only [sz_u1080, sz_txy1080, hw, beq_self_eq_true, Bool.true_and, Bool.and_eq_true,
    List.all_eq_true, List.mem_append, List.mem_singleton]
  refine ⟨?_, ?_⟩
  · intro T hT
    rcases hT with (hT | hT) | hT
    · obtain ⟨j, hj, rfl⟩ := mem_toList_get hT
      rw [sz_u1080] at hj
      rw [uT hj]
      exact tab_ok11 (base11.2.2.2.1 j hj).1 (base11.2.2.2.1 j hj).2.1 (base11.2.2.2.1 j hj).2.2
    · rw [hT, sigT]
      exact tab_ok11 hs hs hsi
    · obtain ⟨j, hj, rfl⟩ := mem_toList_get hT
      rw [sz_txy1080] at hj
      rw [txy1080T hj]
      exact tab_ok11 (r1gc hj) (hr j hj).1 (hr j hj).2
  · rw [sigT, compT_unpack hs hs, hid11, tblEq_unpack (canonK_pcomp hs hs) base11.2.1]
    exact hss

theorem erelWords_ok : ∀ i < 4, ∀ l ∈ Ly1080.erelWords.getD i [], l ≠ 0 ∧ l.natAbs ≤ 4 := by
  decide

theorem erelOK1080_of : Ly1080.erelOK = true := by
  have hl : Ly1080.erelWords.length = 4 := by decide
  have hs := y0.1
  unfold Ly1080.erelOK
  simp only [hl, beq_self_eq_true, Bool.true_and, List.all_eq_true, List.mem_range]
  intro i hi
  have hw := wordT_eqK hid11 base11.2.1 (gens := Ly1080.uLet) (G := LU)
    (Ly1080.erelWords.getD i []) fun l hl =>
      uLetT (erelWords_ok i hi l hl).1 (erelWords_ok i hi l hl).2
  have e : Ly1080.erelWords[i]! = Ly1080.erelWords.getD i [] := by
    simp [List.getD_eq_getElem?_getD, getElem!_def, hl, hi]
  have hu := (base11.2.2.2.1 i hi).1
  rw [e, hw.1, sigT, uT hi, conjT_unpack hs hs hu,
    tblEq_unpack (canonK_pcomp (canonK_pcomp hs hu) hs) hw.2]
  exact allN_spec k_erel i hi

theorem abLetT (l : Int) : Ly1080.abLet l = tabT (unpack 1080 11 (LAB l)) ∧ C11 (LAB l) := by
  unfold Ly1080.abLet LAB
  split_ifs
  · exact ⟨uT (by norm_num), (base11.2.2.2.1 0 (by norm_num)).1⟩
  · exact ⟨uT (by norm_num), (base11.2.2.2.1 3 (by norm_num)).1⟩
  · exact ⟨uIT (by norm_num), (base11.2.2.2.1 0 (by norm_num)).2.1⟩
  · exact ⟨uIT (by norm_num), (base11.2.2.2.1 3 (by norm_num)).2.1⟩

theorem genOK1080_of : Ly1080.genOK = true := by
  have hl : Ly1080.genWords.length = 2 := by decide
  have h := k_gen
  simp only [bAnd_iff] at h
  have w0 := wordT_eqK hid11 base11.2.1 (gens := Ly1080.abLet) (G := LAB)
    (Ly1080.genWords.getD 0 []) fun l _ => abLetT l
  have w1 := wordT_eqK hid11 base11.2.1 (gens := Ly1080.abLet) (G := LAB)
    (Ly1080.genWords.getD 1 []) fun l _ => abLetT l
  have e0 : Ly1080.genWords[0]! = Ly1080.genWords.getD 0 [] := by
    simp [List.getD_eq_getElem?_getD, getElem!_def, hl]
  have e1 : Ly1080.genWords[1]! = Ly1080.genWords.getD 1 [] := by
    simp [List.getD_eq_getElem?_getD, getElem!_def, hl]
  unfold Ly1080.genOK
  rw [hl, e0, e1, w0.1, w1.1, uT (by norm_num), uT (by norm_num),
    tblEq_unpack (base11.2.2.2.1 1 (by norm_num)).1 w0.2,
    tblEq_unpack (base11.2.2.2.1 2 (by norm_num)).1 w1.2, h.1, h.2]
  rfl

theorem txyLet1080T {l : Int} (h0 : l ≠ 0) (h5 : l.natAbs ≤ 5) :
    Ly1080.txyLet l = tabT (unpack 1080 11 (LY l)) ∧ C11 (LY l) := by
  unfold Ly1080.txyLet LY
  by_cases hl : 0 < l
  · simp only [hl, ↓reduceIte]
    have hj : l.toNat - 1 < 5 := by omega
    exact ⟨txy1080T hj, r1gc hj⟩
  · simp only [hl, ↓reduceIte]
    have hj : (-l).toNat - 1 < 5 := by omega
    exact ⟨txy1080IT hj, (y0.2.2.2 _ hj).1⟩

theorem sigmaTxyOK1080_of : Ly1080.sigmaTxyOK = true := by
  have hl : Ly1080.sigmaTxyWords.length = 5 := by decide
  have hs := y0.1
  unfold Ly1080.sigmaTxyOK
  simp only [hl, beq_self_eq_true, Bool.true_and, List.all_eq_true, List.mem_range]
  intro j hj
  have hw := wordT_eqK hid11 base11.2.1 (gens := Ly1080.txyLet) (G := LY)
    (Ly1080.sigmaTxyWords.getD j []) fun l hl =>
      txyLet1080T (sigmaWords_ok j hj l hl).1 (sigmaWords_ok j hj l hl).2
  have e : Ly1080.sigmaTxyWords[j]! = Ly1080.sigmaTxyWords.getD j [] := by
    simp [List.getD_eq_getElem?_getD, getElem!_def, hl, hj]
  have ht := r1gc hj
  rw [e, hw.1, sigT, txy1080T hj, conjT_unpack hs hs ht,
    tblEq_unpack (canonK_pcomp (canonK_pcomp hs ht) hs) hw.2]
  exact allN_spec k_sigt j hj

theorem txy1080_invs : ∀ j < 5, invEqK 1080 11 (mask 11) (1080 * 11) (R1.GI j) (R1I j) = true ∧
    canonK 1080 11 (mask 11) (1080 * 11) (R1I j) = true :=
  fun j hj => ⟨(y0.2.2.2 j hj).2, (y0.2.2.2 j hj).1⟩

theorem r1_cl : ∀ c < R1.cnt * (5 + 5), findPtK R1.cnt R1.T
    (prodQK 1080 11 (mask 11) (5 + 5) R1.T (bothK 5 R1.GI R1I)) R1Cl c = true := by
  have hc := base11.2.2.2.2.2.1
  intro c hcl
  have hc' : c < Nat.mul R1.cnt 10 := by change c < R1.cnt * 10; omega
  have hs : c / 1944 < 20 := by omega
  have h1 : 1944 * (c / 1944) ≤ c := Nat.mul_div_le c 1944
  have h2 : c < 1944 * (c / 1944) + 1944 := by omega
  generalize c / 1944 = s at hs h1 h2
  interval_cases s
  · exact slK_spec k_r1cl0 c (by omega) (by omega) hc'
  · exact slK_spec k_r1cl1 c (by omega) (by omega) hc'
  · exact slK_spec k_r1cl2 c (by omega) (by omega) hc'
  · exact slK_spec k_r1cl3 c (by omega) (by omega) hc'
  · exact slK_spec k_r1cl4 c (by omega) (by omega) hc'
  · exact slK_spec k_r1cl5 c (by omega) (by omega) hc'
  · exact slK_spec k_r1cl6 c (by omega) (by omega) hc'
  · exact slK_spec k_r1cl7 c (by omega) (by omega) hc'
  · exact slK_spec k_r1cl8 c (by omega) (by omega) hc'
  · exact slK_spec k_r1cl9 c (by omega) (by omega) hc'
  · exact slK_spec k_r1cl10 c (by omega) (by omega) hc'
  · exact slK_spec k_r1cl11 c (by omega) (by omega) hc'
  · exact slK_spec k_r1cl12 c (by omega) (by omega) hc'
  · exact slK_spec k_r1cl13 c (by omega) (by omega) hc'
  · exact slK_spec k_r1cl14 c (by omega) (by omega) hc'
  · exact slK_spec k_r1cl15 c (by omega) (by omega) hc'
  · exact slK_spec k_r1cl16 c (by omega) (by omega) hc'
  · exact slK_spec k_r1cl17 c (by omega) (by omega) hc'
  · exact slK_spec k_r1cl18 c (by omega) (by omega) hc'
  · exact slK_spec k_r1cl19 c (by omega) (by omega) hc'

theorem txyEnumOK1080_of : Ly1080.txyEnumOK = true :=
  enumOK_of base11.1 r1G txy1080_tabs txy1080_invs base11.2.2.2.2.2.2 r1_pe r1_hs r1_cl
    base11.2.2.2.2.2.1

end CertificateChecks.KernelLyTr

end
