module

public import Certificates.Kernel.SmithEK.GlueFp
public import CFSG.LargeExtraspecial.S14SMKTransCand

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CertificateChecks.KernelSmithEK

open Subgroup Module CFSG.SmithE CFSG.SmithE.K CFSG.F4.Native CFSG.Fischer CFSG.Fischer.Native
  CFSG.Sporadic.Th CFSG.Sporadic.Th.Native CFSG.KC.Misc.O73 CFSG.LargeExtraspecial.S14.SMK
  CFSG.LargeExtraspecial.SMod20 CFSG.RankThree.OrthogonalInvolutions

attribute [local irreducible] CFSG.F4.Native.uPts CFSG.F4.Native.uPos perpTab uaPts

theorem rec_facts : ∀ k < 29, (pd.RR.getD k []).getD 0 0 < 5 ∧
    ((pd.RR.getD k []).getD 2 0 = 2 →
      2 ≤ (pd.RR.getD k []).getD 0 0 ∧ (pd.RR.getD k []).getD 1 0 = 19) := by
  decide +kernel

theorem rec_cover : ∀ j < 5, ∀ r ∈ pd.RP.getD j [], ∃ k < 29,
    (pd.RR.getD k []).getD 0 0 = j ∧ (pd.RR.getD k []).getD 1 0 = r := by
  decide +kernel

theorem rp_zero : pd.RP.getD 0 [] = [1, 3, 19] := by
  decide +kernel

theorem rep_ok {k : ℕ} (hk : k < 29) :
    cdRepK CFSG.KD.Misc.Xi.TP (po.PL.getD 0 []) pd.LT po.PL pb.P wd.W (pd.RR.getD k []) = true := by
  interval_cases k
  · exact c21276rep_0
  · exact c21276rep_1
  · exact c21276rep_2
  · exact c21276rep_3
  · exact c21276rep_4
  · exact c21276rep_5
  · exact c21276rep_6
  · exact c21276rep_7
  · exact c21276rep_8
  · exact c21276rep_9
  · exact c21276rep_10
  · exact c21276rep_11
  · exact c21276rep_12
  · exact c21276rep_13
  · exact c21276rep_14
  · exact c21276rep_15
  · exact c21276rep_16
  · exact c21276rep_17
  · exact c21276rep_18
  · exact c21276rep_19
  · exact c21276rep_20
  · exact c21276rep_21
  · exact c21276rep_22
  · exact c21276rep_23
  · exact c21276rep_24
  · exact c21276rep_25
  · exact c21276rep_26
  · exact c21276rep_27
  · exact c21276rep_28

set_option maxRecDepth 8000 in
theorem red_ok {j : ℕ} (hj : j < 4) :
    (Nat.beq (lenK (pd.RD.getD j [])) 512 &&
      cdRedAll CFSG.KD.Misc.Xi.TP (po.PL.getD 0 []) (pd.LT.getD (Nat.succ j) 0) po.CO
        (pd.SA.getD (Nat.succ j) []) (pd.RP.getD (Nat.succ j) []) (pd.RD.getD j []) 0) = true := by
  match j, hj with
  | 0, _ => exact c21276red_0
  | 1, _ => exact c21276red_1
  | 2, _ => exact c21276red_2
  | 3, _ => exact c21276red_3

theorem mem_wPlane_of_uaMem {i q : ℕ} (hi : i < 891) (hq : q < 693)
    (h : uaMem uaPts[i]! q = true) : (⟨q, hq⟩ : Fin 693) ∈ wPlane i := by
  obtain ⟨k, hk, he⟩ := anyIn_eq_true.1 h
  rw [beq_iff_eq] at he
  exact ⟨k, hk, Fin.ext ((wPt_val hi hk).trans he)⟩

variable
  {A : CFSG.LargeExtraspecial.SMod20.V ≃ₗ[ZMod 2] CFSG.LargeExtraspecial.SMod20.V} {π : Equiv.Perm (Fin 693)}

theorem image_of_pl {j a i i' : ℕ} (hj : j < 5)
    (hc : IsTab (candT tvTabs uaPts[0]! (liftTab tvTabs j) a) π)
    (h : cdPlK CFSG.KD.Misc.Xi.TP (po.PL.getD 0 []) (pd.LT.getD j 0) a po.PL pb.P i i' = true) :
    i < 891 ∧ i' < 891 ∧ ⇑π '' wPlane i = wPlane i' := by
  obtain ⟨hi, hi', -⟩ := cdPlK_sound h
  refine ⟨hi, hi', image_wPlane_eq hi hi' fun k hk => ?_⟩
  have hm := plane_img hj h hk
  rw [← wPt_val hi hk, hc] at hm
  exact mem_wPlane_of_uaMem hi' (π (wPt i k)).2 hm

theorem vec_mem (h : InvHyp A π) {i i' : ℕ} (hi : i < 891) (hi' : i' < 891)
    (him : ⇑π '' wPlane i = wPlane i') :
    decode (wd.W.getD i' 0 ^^^ wd.W.getD i 0) ∈ commSpace A := by
  have e : decode (wd.W.getD i' 0 ^^^ wd.W.getD i 0) = A (wtV i) - wtV i := by
    rw [decode_xor, ← wtArr_wd hi', ← wtArr_wd hi, CFSG.LargeExtraspecial.SMod20.wtArr_get hi', CFSG.LargeExtraspecial.SMod20.wtArr_get hi,
      sub_eq_add_V,
      h.wtV_eq hi hi' him]
    rfl
  rw [e]
  exact sub_mem_commSpace A _

theorem rep_concl {k : ℕ} (hk : k < 29) (h : InvHyp A π)
    (hc : IsTab (candT tvTabs uaPts[0]! (liftTab tvTabs ((pd.RR.getD k []).getD 0 0))
      ((pd.RR.getD k []).getD 1 0)) π) : InvConcl A π := by
  obtain ⟨hj, hfp⟩ := rec_facts k hk
  obtain ⟨hlen, hpairs, hind, h0, h1, h2⟩ := cdRepK_sound (rep_ok hk)
  have hbs : ∀ v ∈ cdVecs wd.W ((pd.RR.getD k []).drop 5), decode v ∈ commSpace A := by
    intro v hv
    obtain ⟨i, i', hpl, rfl⟩ := cdPairs_vecs hpairs v hv
    obtain ⟨hi, hi', him⟩ := image_of_pl hj hc hpl
    exact vec_mem h hi hi' him
  have h5 := le_finrank_of_indepOK hbs hind
  rw [cdVecs_length, hlen] at h5
  refine ⟨by omega, fun q hpol hwt hsing => ?_⟩
  rcases h2 with ht | ht | ht
  ·
    exfalso
    obtain ⟨hpl, hfB⟩ := h0 ht
    obtain ⟨hi, hi', him⟩ := image_of_pl hj hc hpl
    have hq := hsing _ (vec_mem h hi hi' him)
    have e1 := hwt _ hi'
    have e2 := hwt _ hi
    rw [wtV, ← CFSG.LargeExtraspecial.SMod20.wtArr_get hi', wtArr_wd hi'] at e1
    rw [wtV, ← CFSG.LargeExtraspecial.SMod20.wtArr_get hi, wtArr_wd hi] at e2
    rw [decode_xor, QuadraticMap.map_add (⇑q), hpol, fModel_decode, hfB, e1, e2] at hq
    exact absurd hq (by decide)
  ·
    left
    obtain ⟨he, hfix⟩ := h1 ht
    refine ⟨_, he, mem_UA_of_fix h.norm he fun p hp => ?_⟩
    obtain ⟨m, hm, rfl⟩ := hp
    have e := plane_fix hj he hfix hm
    rw [← wPt_val he hm, hc] at e
    exact Fin.ext e
  ·
    right
    obtain ⟨hj2, ha⟩ := hfp ht
    rw [ha] at hc
    exact fp_rep hj2 hj h hc

theorem isTab_candT {j : ℕ} {s : Equiv.Perm (Fin 693)} (hs : IsTab (liftTab tvTabs j) s)
    (a : ℕ) : IsTab (candT tvTabs uaPts[0]! (liftTab tvTabs j) a) (uaPsi 0 a * s) := by
  intro x
  rw [candT, getElem!_pos _ x.val (by simp), Array.getElem_ofFn]
  simp only
  rw [hs x, Equiv.Perm.mul_apply, uaPsi_apply (by norm_num)]

theorem rep_lift {j r : ℕ} (hj : j < 5) (hr : r ∈ pd.RP.getD j []) (h : InvHyp A π)
    {s : Equiv.Perm (Fin 693)} (hs : IsTab (liftTab tvTabs j) s) (he : π = uaPsi 0 r * s) :
    InvConcl A π := by
  obtain ⟨k, hk, hk0, hk1⟩ := rec_cover j hj r hr
  subst he
  refine rep_concl hk h ?_
  rw [hk0, hk1]
  exact isTab_candT hs r

theorem lift_of_cand {j a : ℕ} (hj : j < 5)
    (hc : IsTab (candT tvTabs uaPts[0]! (liftTab tvTabs j) a) π) :
    IsTab (liftTab tvTabs j) (uaPsi 0 a * π) := by
  intro x
  have hL := liftTab_get hj x.2
  have hlt : (liftTab tvTabs j)[x.val]! < 693 := by
    rw [hL.1]
    exact hL.2
  have hx : π x = uaPsi 0 a ⟨(liftTab tvTabs j)[x.val]!, hlt⟩ := by
    apply Fin.ext
    rw [← hc x, uaPsi_apply (by norm_num), candT, getElem!_pos _ x.val (by simp),
      Array.getElem_ofFn]
  rw [Equiv.Perm.mul_apply, hx, ← Equiv.Perm.mul_apply, uaPsi_mul_self (by norm_num),
    Equiv.Perm.one_apply]

theorem lift_image {j : ℕ} (hj : j < 5) {s : Equiv.Perm (Fin 693)}
    (hs : IsTab (liftTab tvTabs j) s) : ⇑s '' wPlane 0 = wPlane 0 := by
  refine image_wPlane_eq (by norm_num) (by norm_num) fun k hk => ?_
  obtain ⟨hlen, hlt, hS⟩ := cdSaK_sound (sa_ok hj)
  have hk' : k < (pd.SA.getD j []).length := by
    rw [hlen]
    exact hk
  have hSk : (pd.SA.getD j []).getD k 0 < 21 := by
    rw [List.getD_eq_getElem _ _ hk']
    exact hlt _ (List.getElem_mem hk')
  refine ⟨_, hSk, Fin.ext ?_⟩
  rw [wPt_val (by norm_num) hSk, ← pl0_get hSk, hS k hk, ← hs (wPt 0 k),
    wPt_val (by norm_num) hk, ← pl0_get hk, (liftTab_get hj (pl0_lt hk)).1]

theorem sArr_lift {j : ℕ} {s : Equiv.Perm (Fin 693)} (hs : IsTab (liftTab tvTabs j) s) :
    sArr 0 s = sArrT uaPts[0]! (liftTab tvTabs j) := by
  refine Array.ext (by rw [sArr_size, sArrT, Array.size_ofFn]) fun k hk _ => ?_
  have hk' : k < 21 := by rwa [sArr_size] at hk
  rw [sArr_getElem]
  simp only [sArrT, Array.getElem_ofFn]
  rw [← wPt_val (by norm_num) hk', hs]

theorem conj_cand {j : ℕ} (hj : j < 5) {s : Equiv.Perm (Fin 693)}
    (hs : IsTab (liftTab tvTabs j) s) (hsP : IsPolarAut s) (a b : ℕ) :
    uaPsi 0 b * (uaPsi 0 a * s) * (uaPsi 0 b)⁻¹ =
      uaPsi 0 (a ^^^ b ^^^ amK po.CO (pd.SA.getD j []) b) * s := by
  have hc := conj_uaPsi (i := 0) (by norm_num) hsP (lift_image hj hs) b
  rw [sArr_lift hs, collAmat_lift hj] at hc
  have hx : ∀ x y, uaPsi 0 (x ^^^ y) = uaPsi 0 x * uaPsi 0 y := uaPsi_xor (by norm_num)
  have hb : (uaPsi 0 b)⁻¹ = uaPsi 0 b := inv_eq_of_mul_eq_one_right (uaPsi_mul_self (by norm_num) b)
  have hab : uaPsi 0 b * uaPsi 0 a = uaPsi 0 a * uaPsi 0 b := by
    rw [← hx, ← hx, Nat.xor_comm]
  rw [hx, hx, ← hc, hb]
  calc uaPsi 0 b * (uaPsi 0 a * s) * uaPsi 0 b
      = uaPsi 0 b * uaPsi 0 a * (s * uaPsi 0 b * s⁻¹) * s := by group
    _ = uaPsi 0 a * uaPsi 0 b * (s * uaPsi 0 b * s⁻¹) * s := by rw [hab]

theorem cand_concl_lift {j a : ℕ} (hj : j < 5) (ha : a < 512) {s : Equiv.Perm (Fin 693)}
    (hs : IsTab (liftTab tvTabs j) s) (hsP : IsPolarAut s) (h : InvHyp A (uaPsi 0 a * s)) :
    InvConcl A (uaPsi 0 a * s) := by
  rcases Nat.eq_zero_or_pos j with rfl | hj1
  ·
    have hs1 : s = 1 := Equiv.ext fun x => Fin.ext (by
      have e := hs x
      rw [show liftTab tvTabs 0 = idTab from rfl, idTab_get x.2] at e
      exact e.symm)
    subst hs1
    rw [mul_one] at h ⊢
    by_cases ha0 : a = 0
    · subst ha0
      exact absurd (uaPsi_zero 0) h.ne_one
    obtain ⟨g, hg, hga⟩ := exists_conj_uaRoot ha
    have hroot : uaRoot (uaCls collS2 a) ∈ pd.RP.getD 0 [] := by
      rw [rp_zero]
      unfold uaCls
      split_ifs <;> simp_all [uaRoot]
    have hgT : g⁻¹ ∈ T46 := T46.inv_mem hg.1
    apply invConcl_of_conj ⟨g⁻¹, hgT⟩
    refine rep_lift hj hroot (h.conjT ⟨g⁻¹, hgT⟩) (s := 1) hs ?_
    change g⁻¹ * uaPsi 0 a * g⁻¹⁻¹ = _
    rw [hga]
    group
  ·
    obtain ⟨j', rfl⟩ : ∃ j', j = Nat.succ j' := ⟨j - 1, by omega⟩
    have hred := red_ok (j := j') (by omega)
    rw [Bool.and_eq_true, Nat.beq_eq, lenK_eq] at hred
    have he := cdRedAll_sound hred.2 a (by rw [hred.1]; exact ha)
    rw [Nat.zero_add] at he
    rcases cdRedK_sound he with ⟨x, hx, hne⟩ | ⟨b, hb, r, hr, hrr⟩
    ·
      exfalso
      apply hne
      have hc := isTab_candT hs a
      have e1 := candT_lift hj a hx
      have e2 := candT_lift hj a (cdImg_lt hj a hx)
      have p1 := hc ⟨x, hx⟩
      have p2 := hc ((uaPsi 0 a * s) ⟨x, hx⟩)
      rw [← Equiv.Perm.mul_apply, h.mul_self, Equiv.Perm.one_apply] at p2
      rw [← e2, ← e1, p1, p2]
    ·
      have hbT : uaPsi 0 b ∈ T46 := UA_le_T46 (uaPsi_mem_UA b)
      apply invConcl_of_conj ⟨uaPsi 0 b, hbT⟩
      refine rep_lift hj hr (h.conjT ⟨uaPsi 0 b, hbT⟩) hs ?_
      change uaPsi 0 b * (uaPsi 0 a * s) * (uaPsi 0 b)⁻¹ = _
      rw [conj_cand hj hs hsP a b, hrr]

theorem cand_concl {j a : ℕ} (hj : j < 5) (ha : a < 512) (h : InvHyp A π)
    (hc : IsTab (candT tvTabs uaPts[0]! (liftTab tvTabs j) a) π) : InvConcl A π := by
  have hs := lift_of_cand hj hc
  have hπ : π = uaPsi 0 a * (uaPsi 0 a * π) := by
    rw [← mul_assoc, uaPsi_mul_self (by norm_num), one_mul]
  have hsP : IsPolarAut (uaPsi 0 a * π) :=
    (isPolarAut_of_mem (UA_le_T46 (uaPsi_mem_UA a))).mul (isPolarAut_of_mem_normalizer h.norm)
  rw [hπ] at h ⊢
  exact cand_concl_lift hj ha hs hsP h

end CertificateChecks.KernelSmithEK
