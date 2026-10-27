module

public import Certificates.Kernel.Om2K.Orbit

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelOm2

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KC.BfsPin CFSG.KC.SetOrb
open CFSG.Monster.B.Co2.Native CFSG.RankThree.Native CFSG.Monster.B.Fischer
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.Twin1711.Om2Data
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.Twin1711.Om2Check
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.Twin1711.Om1Check (reflTab keyF)


abbrev gT : Array (Array Nat) := (wT.map (wY LY)).toArray

theorem gT_size : gT.size = 8 := by simp [gT, wT_len]

theorem gT_get {k : Nat} (hk : k < 8) : gT[k]! = unpack 480 9 (TG.G k) := by
  rw [getElem!_pos _ k (by rw [gT_size]; exact hk)]
  simp only [gT, List.getElem_toArray, List.getElem_map]
  rw [← List.getD_eq_getElem _ [] (by rw [wT_len]; exact hk)]
  exact tg_eq hk

theorem subOK_spec {N R : Nat} {X Y E D : Nat → Nat} (h : subOK N X Y E D R = true) :
    (∀ i < N, closK 9 48 8 N TG.G Orb.C Orb.M X E i = true) ∧
      (∀ i < N, treeK 9 48 8 TG.G Orb.C Orb.M X D i = true) ∧
      (∀ i < N, Y (X i) = i ∧ X i < 6300) ∧ imgK 9 48 R (Orb.C 0) = Orb.M (X 0) := by
  unfold subOK at h
  obtain ⟨h1, h2⟩ := band h
  obtain ⟨h2, h3⟩ := band h2
  obtain ⟨h3, h4⟩ := band h3
  refine ⟨allN_spec h1, allN_spec h2, fun i hi => ?_, Nat.eq_of_beq_eq_true h4⟩
  obtain ⟨a, b⟩ := band (allN_spec h3 i hi)
  exact ⟨Nat.eq_of_beq_eq_true a, Nat.blt_eq.mp b⟩

theorem transOK_spec {N R : Nat} {X Y E D : Nat → Nat} (h : transOK N X Y E D R = true) :
    (∀ i < N, closK 9 48 9 N (tgR R) Orb.C Orb.M X E i = true) ∧
      (∀ i < N, treeK 9 48 9 (tgR R) Orb.C Orb.M X D i = true) ∧
      (∀ i < N, Y (X i) = i ∧ X i < 6300) ∧ X 0 = 0 := by
  unfold transOK at h
  obtain ⟨h1, h2⟩ := band h
  obtain ⟨h2, h3⟩ := band h2
  obtain ⟨h3, h4⟩ := band h3
  refine ⟨allN_spec h1, allN_spec h2, fun i hi => ?_, Nat.eq_of_beq_eq_true h4⟩
  obtain ⟨a, b⟩ := band (allN_spec h3 i hi)
  exact ⟨Nat.eq_of_beq_eq_true a, Nat.blt_eq.mp b⟩

theorem sub_cert {N R : Nat} {X Y E D : Nat → Nat} {w : List Nat} (h : subOK N X Y E D R = true)
    (hR : wY LY w = unpack 480 9 R) (hRok : okK R = true) (h0 : 0 < N) (hf : N ≤ 6301) :
    arrCertOK (fun k F => actFY gT[k]! F) gT.size validFY keyF (actFY (wY LY w) (fCodeY (wY LY wT0)))
        (arrBfs (fun k F => actFY gT[k]! F) gT.size keyF
          (actFY (wY LY w) (fCodeY (wY LY wT0))) 6301) = true ∧
      ∀ x, x ∈ (arrBfs (fun k F => actFY gT[k]! F) gT.size keyF
          (actFY (wY LY w) (fCodeY (wY LY wT0))) 6301).pts ↔ ∃ i < N, V (X i) = x := by
  obtain ⟨hcl, htr, hinv, hr⟩ := subOK_spec h
  have hroot : V (X 0) = actFY (wY LY w) (fCodeY (wY LY wT0)) := by
    rw [hR, F0_eq]
    exact (act_eq hRok (by norm_num) (hinv 0 h0).2 hr).symm
  rw [gT_size]
  obtain ⟨c1, c2, -⟩ := cert_of (fun k hk => gT_get hk) (fun k hk => tg_ok hk)
    (fun i hi => (hinv i hi).2) hcl htr (fun i hi => (hinv i hi).1) h0 hroot hf
  exact ⟨c1, c2⟩

theorem push_get (a : Array (Array Nat)) (x : Array Nat) {k : Nat} (hk : k < a.size + 1) :
    (a.push x)[k]! = if k < a.size then a[k]! else x := by
  rw [getElem!_pos _ k (by simpa using hk), Array.getElem_push]
  split
  · next h => rw [getElem!_pos _ k h]
  · rfl

theorem trans_cert {N R : Nat} {X Y E D : Nat → Nat} {w : List Nat} (h : transOK N X Y E D R = true)
    (hR : wY LY w = unpack 480 9 R) (hRok : okK R = true) (h0 : 0 < N) (hf : N ≤ 6301) :
    arrCertOK (fun k F => actFY (gT.push (wY LY w))[k]! F) (gT.push (wY LY w)).size validFY keyF
        (fCodeY (wY LY wT0))
        (arrBfs (fun k F => actFY (gT.push (wY LY w))[k]! F) (gT.push (wY LY w)).size keyF
          (fCodeY (wY LY wT0)) 6301) = true ∧
      (arrBfs (fun k F => actFY (gT.push (wY LY w))[k]! F) (gT.push (wY LY w)).size keyF
          (fCodeY (wY LY wT0)) 6301).pts.size = N := by
  obtain ⟨hcl, htr, hinv, hx0⟩ := transOK_spec h
  have hs : (gT.push (wY LY w)).size = 9 := by rw [Array.size_push, gT_size]
  have hget : ∀ k < 9, (gT.push (wY LY w))[k]! = unpack 480 9 (tgR R k) := by
    intro k hk
    rw [push_get _ _ (by rw [gT_size]; exact hk), gT_size]
    by_cases h8 : k < 8
    · rw [if_pos h8, gT_get h8]
      have e : Nat.blt k 8 = true := Nat.blt_eq.mpr h8
      unfold tgR
      rw [e]
    · rw [if_neg h8, hR]
      have e : Nat.blt k 8 = false := by
        cases e' : Nat.blt k 8
        · rfl
        · exact absurd (Nat.blt_eq.mp e') h8
      unfold tgR
      rw [e]
  have hok : ∀ k < 9, okK (tgR R k) = true := by
    intro k hk
    by_cases h8 : k < 8
    · have e : Nat.blt k 8 = true := Nat.blt_eq.mpr h8
      unfold tgR
      rw [e]
      exact tg_ok h8
    · have e : Nat.blt k 8 = false := by
        cases e' : Nat.blt k 8
        · rfl
        · exact absurd (Nat.blt_eq.mp e') h8
      unfold tgR
      rw [e]
      exact hRok
  have hroot : V (X 0) = fCodeY (wY LY wT0) := by rw [hx0, F0_eq]
  rw [hs]
  obtain ⟨c1, -, c3⟩ := cert_of hget hok (fun i hi => (hinv i hi).2) hcl htr
    (fun i hi => (hinv i hi).1) h0 hroot hf
  exact ⟨c1, c3⟩

theorem subAt {s : Nat} (hs : s < 12) :
    arrCertOK (fun k F => actFY gT[k]! F) gT.size validFY keyF
        (actFY (wY LY (wSub.getD s [])) (fCodeY (wY LY wT0)))
        (arrBfs (fun k F => actFY gT[k]! F) gT.size keyF
          (actFY (wY LY (wSub.getD s [])) (fCodeY (wY LY wT0))) 6301) = true := by
  interval_cases s
  · exact (sub_cert kSub0 (ws_eq (by norm_num)) (ws_ok (by norm_num)) (by decide) (by decide)).1
  · exact (sub_cert kSub1 (ws_eq (by norm_num)) (ws_ok (by norm_num)) (by decide) (by decide)).1
  · exact (sub_cert kSub2 (ws_eq (by norm_num)) (ws_ok (by norm_num)) (by decide) (by decide)).1
  · exact (sub_cert kSub3 (ws_eq (by norm_num)) (ws_ok (by norm_num)) (by decide) (by decide)).1
  · exact (sub_cert kSub4 (ws_eq (by norm_num)) (ws_ok (by norm_num)) (by decide) (by decide)).1
  · exact (sub_cert kSub5 (ws_eq (by norm_num)) (ws_ok (by norm_num)) (by decide) (by decide)).1
  · exact (sub_cert kSub6 (ws_eq (by norm_num)) (ws_ok (by norm_num)) (by decide) (by decide)).1
  · exact (sub_cert kSub7 (ws_eq (by norm_num)) (ws_ok (by norm_num)) (by decide) (by decide)).1
  · exact (sub_cert kSub8 (ws_eq (by norm_num)) (ws_ok (by norm_num)) (by decide) (by decide)).1
  · exact (sub_cert kSub9 (ws_eq (by norm_num)) (ws_ok (by norm_num)) (by decide) (by decide)).1
  · exact (sub_cert kSub10 (ws_eq (by norm_num)) (ws_ok (by norm_num)) (by decide) (by decide)).1
  · exact (sub_cert kSub11 (ws_eq (by norm_num)) (ws_ok (by norm_num)) (by decide) (by decide)).1

theorem transAt {s : Nat} (hs : s < 12) :
    orbSizeY (gT.push (wY LY (wSub.getD s []))) (fCodeY (wY LY wT0)) 6300 = true := by
  unfold orbSizeY orbFY
  simp only [Bool.and_eq_true, beq_iff_eq]
  interval_cases s
  · exact trans_cert kTr0 (ws_eq (by norm_num)) (ws_ok (by norm_num)) (by decide) (by decide)
  · exact trans_cert kTr1 (ws_eq (by norm_num)) (ws_ok (by norm_num)) (by decide) (by decide)
  · exact trans_cert kTr2 (ws_eq (by norm_num)) (ws_ok (by norm_num)) (by decide) (by decide)
  · exact trans_cert kTr3 (ws_eq (by norm_num)) (ws_ok (by norm_num)) (by decide) (by decide)
  · exact trans_cert kTr4 (ws_eq (by norm_num)) (ws_ok (by norm_num)) (by decide) (by decide)
  · exact trans_cert kTr5 (ws_eq (by norm_num)) (ws_ok (by norm_num)) (by decide) (by decide)
  · exact trans_cert kTr6 (ws_eq (by norm_num)) (ws_ok (by norm_num)) (by decide) (by decide)
  · exact trans_cert kTr7 (ws_eq (by norm_num)) (ws_ok (by norm_num)) (by decide) (by decide)
  · exact trans_cert kTr8 (ws_eq (by norm_num)) (ws_ok (by norm_num)) (by decide) (by decide)
  · exact trans_cert kTr9 (ws_eq (by norm_num)) (ws_ok (by norm_num)) (by decide) (by decide)
  · exact trans_cert kTr10 (ws_eq (by norm_num)) (ws_ok (by norm_num)) (by decide) (by decide)
  · exact trans_cert kTr11 (ws_eq (by norm_num)) (ws_ok (by norm_num)) (by decide) (by decide)

theorem cov_sub {N R s j : Nat} {X Y E D : Nat → Nat} (h : subOK N X Y E D R = true)
    (hs : s < 12) (hR : wY LY (wSub.getD s []) = unpack 480 9 R) (hRok : okK R = true)
    (h0 : 0 < N) (hf : N ≤ 6301) (hj : inSub N X Y j = true) :
    (wSub.map fun w => arrBfs (fun k F => actFY gT[k]! F) gT.size keyF
        (actFY (wY LY w) (fCodeY (wY LY wT0))) 6301).any (inCertY · (V j)) = true := by
  unfold inSub at hj
  simp only [Bool.and_eq_true, beq_iff_eq] at hj
  obtain ⟨h1, h2⟩ := hj
  have hm := ((sub_cert h hR hRok h0 hf).2 (V j)).2 ⟨_, Nat.blt_eq.mp h1, congrArg V (Nat.eq_of_beq_eq_true h2)⟩
  rw [List.any_map, List.any_eq_true]
  refine ⟨wSub.getD s [], ?_, ?_⟩
  · rw [List.getD_eq_getElem _ _ (by rw [wSub_len]; exact hs)]
    exact List.getElem_mem _
  · unfold inCertY
    rw [Function.comp_apply, List.any_eq_true]
    exact ⟨V j, Array.mem_toList_iff.2 hm, beq_self_eq_true _⟩

theorem sub_k : subCheckY (reflTab ()) = true := by
  unfold subCheckY subCertsY
  simp only [Bool.and_eq_true]
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · rw [List.all_eq_true]
    intro p hp
    obtain ⟨s, hs, rfl⟩ := List.mem_iff_getElem.1 hp
    have hs12 : s < 12 := by simpa [wSub_len] using hs
    rw [List.getElem_zip, List.getElem_map]
    unfold orbFY
    have e := subAt hs12
    rw [List.getD_eq_getElem _ _ (by rw [wSub_len]; exact hs12)] at e
    exact e
  · rw [List.all_eq_true]
    intro F hF
    rw [Array.mem_toList_iff] at hF
    unfold orbFY at hF
    rw [F0_eq, genY_size] at hF
    obtain ⟨j, hj, rfl⟩ := (main_cert.2.1 F).1 hF
    have hc := allN_spec kCov j hj
    unfold covK at hc
    simp only [Bool.or_eq_true, or_assoc] at hc
    simp only [Bool.or_eq_true]
    unfold orbFY
    rcases hc with h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · rw [F0_eq, Nat.eq_of_beq_eq_true h]
      exact Or.inl (Or.inl (beq_self_eq_true _))
    · obtain ⟨k, hk, e⟩ := List.any_eq_true.1 h
      rw [List.mem_range] at hk
      refine Or.inl (Or.inr (List.any_eq_true.2 ⟨wFuse0.getD k [], ?_, ?_⟩))
      · rw [List.getD_eq_getElem _ _ (by rw [wFuse0_len]; exact hk)]
        exact List.getElem_mem _
      · rw [fu_eq hk, F0_eq, act_eq (fu_ok hk) (by norm_num) hj (Nat.eq_of_beq_eq_true e)]
        exact beq_self_eq_true _
    · exact Or.inr (cov_sub kSub0 (by norm_num) (ws_eq (by norm_num)) (ws_ok (by norm_num))
        (by decide) (by decide) h)
    · exact Or.inr (cov_sub kSub1 (by norm_num) (ws_eq (by norm_num)) (ws_ok (by norm_num))
        (by decide) (by decide) h)
    · exact Or.inr (cov_sub kSub2 (by norm_num) (ws_eq (by norm_num)) (ws_ok (by norm_num))
        (by decide) (by decide) h)
    · exact Or.inr (cov_sub kSub3 (by norm_num) (ws_eq (by norm_num)) (ws_ok (by norm_num))
        (by decide) (by decide) h)
    · exact Or.inr (cov_sub kSub4 (by norm_num) (ws_eq (by norm_num)) (ws_ok (by norm_num))
        (by decide) (by decide) h)
    · exact Or.inr (cov_sub kSub5 (by norm_num) (ws_eq (by norm_num)) (ws_ok (by norm_num))
        (by decide) (by decide) h)
    · exact Or.inr (cov_sub kSub6 (by norm_num) (ws_eq (by norm_num)) (ws_ok (by norm_num))
        (by decide) (by decide) h)
    · exact Or.inr (cov_sub kSub7 (by norm_num) (ws_eq (by norm_num)) (ws_ok (by norm_num))
        (by decide) (by decide) h)
    · exact Or.inr (cov_sub kSub8 (by norm_num) (ws_eq (by norm_num)) (ws_ok (by norm_num))
        (by decide) (by decide) h)
    · exact Or.inr (cov_sub kSub9 (by norm_num) (ws_eq (by norm_num)) (ws_ok (by norm_num))
        (by decide) (by decide) h)
    · exact Or.inr (cov_sub kSub10 (by norm_num) (ws_eq (by norm_num)) (ws_ok (by norm_num))
        (by decide) (by decide) h)
    · exact Or.inr (cov_sub kSub11 (by norm_num) (ws_eq (by norm_num)) (ws_ok (by norm_num))
        (by decide) (by decide) h)
  · rw [List.all_eq_true]
    intro w hw
    obtain ⟨s, hs, rfl⟩ := mem_getD hw
    rw [wSub_len] at hs
    exact transAt hs

end CertificateChecks.KernelOm2

end
