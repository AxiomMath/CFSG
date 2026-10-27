module

public import Certificates.Kernel.Om2K.Base
public import Certificates.Kernel.Om2K.ChecksR
public import CFSG.Certificates.Kernel.LocalCompCoordSound
public import CFSG.Certificates.Kernel.SetOrbSound

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelOm2

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KC.BfsPin
open CFSG.Monster.B.Co2.Native CFSG.RankThree.Native
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.Twin1711.Om2Data
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.Twin1711.Om2Check
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.Twin1711.Om1Check (reflTab eA)
open CertificateChecks.KernelLC.E8 (FT NEG)

theorem allLt_true {n : Nat} {p : Nat → Bool} :
    CFSG.Monster.B.Co2.Native.allLt n p = true ↔ ∀ i < n, p i = true := by
  unfold CFSG.Monster.B.Co2.Native.allLt
  rw [Nat.all_eq_finRange_all, List.all_eq_true]
  exact ⟨fun h i hi => h ⟨i, hi⟩ (List.mem_finRange _), fun h i _ => h i i.2⟩

abbrev LY : Array (Array Nat) := lettersY (reflTab ())

theorem el_ok {k : Nat} (hk : k < 7) : okK (EL.G k) = true := allN_spec kOkE k hk

theorem el_eq {k : Nat} (hk : k < 7) : wY LY (elW.getD k []) = unpack 480 9 (EL.G k) := by
  rw [(wY_eq _ (by interval_cases k <;> decide)).1, Nat.eq_of_beq_eq_true (allN_spec kEL k hk)]

theorem t0_eq : wY LY wT0 = unpack 480 9 (EL.G 0) := el_eq (k := 0) (by norm_num)
theorem i0_eq : wY LY wI0 = unpack 480 9 (EL.G 1) := el_eq (k := 1) (by norm_num)
theorem j0_eq : wY LY wJ0 = unpack 480 9 (EL.G 2) := el_eq (k := 2) (by norm_num)
theorem tc_eq : wY LY wTc = unpack 480 9 (EL.G 3) := el_eq (k := 3) (by norm_num)
theorem fc_eq : wY LY wFuseC = unpack 480 9 (EL.G 4) := el_eq (k := 4) (by norm_num)
theorem la_eq : wY LY wLiftA = unpack 480 9 (EL.G 5) := el_eq (k := 5) (by norm_num)
theorem lb_eq : wY LY wLiftB = unpack 480 9 (EL.G 6) := el_eq (k := 6) (by norm_num)

theorem cnE {k : Nat} (hk : k < 7) : Cn (EL.G k) := (okK_iff (el_ok hk)).1

theorem tg_ok {k : Nat} (hk : k < 8) : okK (TG.G k) = true := allN_spec kOkTG k hk

theorem fu_ok {k : Nat} (hk : k < 3) : okK (FU.G k) = true := allN_spec kOkFU k hk

theorem ws_ok {k : Nat} (hk : k < 12) : okK (WS.G k) = true := allN_spec kOkWS k hk

theorem wT_lt : ∀ w ∈ wT, ∀ l ∈ w, l < 16 := by decide
theorem wSub_lt : ∀ w ∈ wSub, ∀ l ∈ w, l < 16 := by decide
theorem wFuse0_lt : ∀ w ∈ wFuse0, ∀ l ∈ w, l < 16 := by decide
theorem wCc_lt : ∀ w ∈ wCc, ∀ l ∈ w, l < 16 := by decide
theorem wCR_lt : ∀ w ∈ wCR, ∀ l ∈ w, l < 16 := by decide

theorem tab_eq {ws : List (List Nat)} {G : Nat → Nat} (hlt : ∀ w ∈ ws, ∀ l ∈ w, l < 16)
    (hG : ∀ k < ws.length, Nat.beq (G k) (wYK (ws.getD k [])) = true) {k : Nat}
    (hk : k < ws.length) : wY LY (ws.getD k []) = unpack 480 9 (G k) := by
  have hm : ws.getD k [] ∈ ws := by
    rw [List.getD_eq_getElem _ _ hk]
    exact List.getElem_mem _
  rw [(wY_eq _ (hlt _ hm)).1, Nat.eq_of_beq_eq_true (hG k hk)]

theorem mem_getD {ws : List (List Nat)} {w : List Nat} (hw : w ∈ ws) :
    ∃ k < ws.length, ws.getD k [] = w := by
  obtain ⟨k, hk, e⟩ := List.mem_iff_getElem.1 hw
  exact ⟨k, hk, by rw [List.getD_eq_getElem _ _ hk, e]⟩

theorem wT_len : wT.length = 8 := by decide
theorem wSub_len : wSub.length = 12 := by decide
theorem wFuse0_len : wFuse0.length = 3 := by decide
theorem wCc_len : wCc.length = 5 := by decide
theorem wCR_len : wCR.length = 2 := by decide

theorem tg_eq {k : Nat} (hk : k < 8) : wY LY (wT.getD k []) = unpack 480 9 (TG.G k) :=
  tab_eq wT_lt (fun k hk => allN_spec kTG k (wT_len ▸ hk)) (wT_len ▸ hk)

theorem ws_eq {k : Nat} (hk : k < 12) : wY LY (wSub.getD k []) = unpack 480 9 (WS.G k) :=
  tab_eq wSub_lt (fun k hk => allN_spec kWS k (wSub_len ▸ hk)) (wSub_len ▸ hk)

theorem fu_eq {k : Nat} (hk : k < 3) : wY LY (wFuse0.getD k []) = unpack 480 9 (FU.G k) :=
  tab_eq wFuse0_lt (fun k hk => allN_spec kFU k (wFuse0_len ▸ hk)) (wFuse0_len ▸ hk)

theorem cc_eq {k : Nat} (hk : k < 5) : wY LY (wCc.getD k []) = unpack 480 9 (CC.G k) :=
  tab_eq wCc_lt (fun k hk => allN_spec kCC k (wCc_len ▸ hk)) (wCc_len ▸ hk)

theorem cr_eq {k : Nat} (hk : k < 2) : wY LY (wCR.getD k []) = unpack 480 9 (CRG.G k) :=
  tab_eq wCR_lt (fun k hk => allN_spec kCRg k (wCR_len ▸ hk)) (wCR_len ▸ hk)

theorem eA_eq {m : Nat} (hm : m < 256) : eA m = unpack 240 8 (FT m) := by
  have h := (CFSG.KLC.E8.frame_tabs CertificateChecks.KernelLC.E8.bind
    CertificateChecks.KernelLC.E8.sorted CertificateChecks.KernelLC.E8.froots
    CertificateChecks.KernelLC.E8.ft0 CertificateChecks.KernelLC.E8.hft kHF).1 m hm
  rw [CFSG.KLC.E8.frameArrs_get hm] at h
  exact h

theorem fst_eq {X Y : Nat} (h : allN 240 (fun i => Nat.beq (pg 9 511 X i) (pg 8 255 Y i)) = true) :
    eqA 240 (fstA (unpack 480 9 X)) (unpack 240 8 Y) = true := by
  unfold eqA
  rw [allLt_true]
  intro i hi
  have e := Nat.eq_of_beq_eq_true (allN_spec h i hi)
  have h1 : (fstA (unpack 480 9 X))[i]! = pg 9 (mask 9) X i := by
    unfold fstA
    rw [getElem!_pos _ i (by simp [unpack]; omega)]
    simp [unpack]
  rw [h1, CFSG.KC.SetOrb.unpack_get hi]
  exact beq_iff_eq.2 e

theorem cA_ok {k : Nat} (hk : k < 3) : okK (cAK k) = true := allN_spec kCA k hk

theorem cA_eq {k : Nat} (hk : k < 3) : cA k = unpack 480 9 (cAK k) := by
  have hn := CertificateChecks.KernelLC.E8.neg_eq
  interval_cases k
  · rw [cA, if_pos rfl, hn, idA2_eq, pairA_eq kNEG cn_pid2]
    rfl
  · rw [cA, if_neg (by decide), if_pos rfl, hn, idA2_eq, pairA_eq cn_pid2 kNEG]
    rfl
  · rw [cA, if_neg (by decide), if_neg (by decide), hn, pairA_eq kNEG kNEG]
    rfl

theorem cA_cn {k : Nat} (hk : k < 3) : Cn (cAK k) := (okK_iff (cA_ok hk)).1

theorem cn_cj {g y : Nat} (hg : okK g = true) (hy : Cn y) : Cn (cj g y) :=
  cn_pc (okK_iff hg).1 (cn_pc hy (okK_iff hg).2.2)

theorem conjA_cj {g y : Nat} (hg : okK g = true) (hy : Cn y) :
    conjA 480 (unpack 480 9 g) (unpack 480 9 y) = unpack 480 9 (cj g y) := conjA_pc hg hy

theorem q8_eq {X Y : Nat} (hX : Cn X) (hY : Cn Y) :
    q8ListY (unpack 480 9 X) (unpack 480 9 Y) = (q8K X Y).map (unpack 480 9) := by
  unfold q8ListY q8K
  dsimp only
  have c2 := cn_pc hX hX
  rw [compA_pc hX hX, compA_pc c2 hX, compA_pc hY hX, compA_pc hY c2,
    compA_pc hY (cn_pc c2 hX), idA_eq]
  rfl

theorem q8_cn {X Y : Nat} (hX : Cn X) (hY : Cn Y) : ∀ b ∈ q8K X Y, Cn b := by
  have c2 := cn_pc hX hX
  intro b hb
  simp only [q8K, List.mem_cons, List.not_mem_nil, or_false] at hb
  rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact kPid
  · exact hX
  · exact c2
  · exact cn_pc c2 hX
  · exact hY
  · exact cn_pc hY hX
  · exact cn_pc hY c2
  · exact cn_pc hY (cn_pc c2 hX)

theorem inLY_eq {L : List Nat} {A : Nat} (hL : ∀ b ∈ L, Cn b) (hA : Cn A) :
    inLY (L.map (unpack 480 9)) (unpack 480 9 A) = L.any (Nat.beq A) := by
  unfold inLY
  rw [List.any_map]
  apply Bool.eq_iff_iff.2
  simp only [List.any_eq_true, Function.comp]
  refine exists_congr fun b => and_congr_right fun hb => ?_
  rw [eqA_pc hA (hL b hb)]

theorem commY_eq {X Y : Nat} (hX : Cn X) (hY : Cn Y) :
    commY (unpack 480 9 X) (unpack 480 9 Y) = Nat.beq (pc X Y) (pc Y X) := by
  unfold commY
  rw [compA_pc hX hY, compA_pc hY hX, eqA_pc (cn_pc hX hY) (cn_pc hY hX)]

theorem rel_k : relCheckY (reflTab ()) = true := by
  have c0 := cnE (k := 0) (by norm_num)
  have c1 := cnE (k := 1) (by norm_num)
  have c2 := cnE (k := 2) (by norm_num)
  have c3 := cnE (k := 3) (by norm_num)
  have c5 := cnE (k := 5) (by norm_num)
  have c6 := cnE (k := 6) (by norm_num)
  have ca1 := cA_cn (k := 1) (by norm_num)
  have hq := q8_cn c1 c2
  unfold relCheckY
  simp only [Bool.and_eq_true]
  refine ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨?_, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩
  · rw [t0_eq, eA_eq (by norm_num)]
    exact fst_eq kR1
  · rw [t0_eq, compA_pc c0 c0, idA_eq, eqA_pc (cn_pc c0 c0) kPid]
    exact kR2
  · rw [t0_eq, i0_eq, j0_eq]
    unfold q8RelY
    simp only [Bool.and_eq_true]
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · rw [compA_pc c1 c1, eqA_pc (cn_pc c1 c1) c0]
      exact kR3a
    · rw [compA_pc c2 c2, eqA_pc (cn_pc c2 c2) c0]
      exact kR3b
    · rw [conjA_cj (el_ok (k := 2) (by norm_num)) c1, invCand_pinv (el_ok (k := 1) (by norm_num)),
        eqA_pc (cn_cj (el_ok (k := 2) (by norm_num)) c1) (okK_iff (el_ok (k := 1) (by norm_num))).2.2]
      exact kR3c
  · rw [List.all_eq_true]
    intro k hk
    rw [List.mem_range] at hk
    rw [fu_eq hk, t0_eq, conjA_cj (fu_ok hk) c0, cA_eq hk, compA_pc c0 (cA_cn hk),
      eqA_pc (cn_cj (fu_ok hk) c0) (cn_pc c0 (cA_cn hk))]
    exact allN_spec kR4 k hk
  · rw [List.all_eq_true]
    intro w hw
    obtain ⟨k, hk, rfl⟩ := mem_getD hw
    rw [wT_len] at hk
    have ok := tg_ok hk
    simp only [Bool.and_eq_true]
    rw [tg_eq hk, t0_eq, i0_eq, j0_eq, q8_eq c1 c2, commY_eq (okK_iff ok).1 c0,
      conjA_cj ok c1, conjA_cj ok c2, inLY_eq hq (cn_cj ok c1), inLY_eq hq (cn_cj ok c2)]
    exact ⟨⟨allN_spec kR5a k hk, allN_spec kR5b k hk⟩, allN_spec kR5c k hk⟩
  · rw [tc_eq, eA_eq (by norm_num)]
    exact fst_eq kR6
  · rw [tc_eq, compA_pc c3 c3, idA_eq, eqA_pc (cn_pc c3 c3) kPid]
    exact kR7
  · rw [fc_eq, tc_eq, conjA_cj (el_ok (k := 4) (by norm_num)) c3, cA_eq (by norm_num),
      compA_pc c3 ca1, eqA_pc (cn_cj (el_ok (k := 4) (by norm_num)) c3) (cn_pc c3 ca1)]
    exact kR8
  · rw [List.all_eq_true]
    intro w hw
    obtain ⟨k, hk, rfl⟩ := mem_getD hw
    rw [wCc_len] at hk
    have ok := allN_spec kOkC k hk
    rw [cc_eq hk, tc_eq, commY_eq (okK_iff ok).1 c3]
    exact allN_spec kR9 k hk
  · rw [la_eq, eA_eq (by norm_num)]
    exact fst_eq kR10a
  · rw [lb_eq, eA_eq (by norm_num)]
    exact fst_eq kR10b
  · simp only [List.all_cons, List.all_nil, Bool.and_true, Bool.and_eq_true]
    have hk := fun k (hk : k < 2) => band (allN_spec kR11 k hk)
    have h0 := hk 0 (by norm_num)
    have h1 := hk 1 (by norm_num)
    rw [la_eq, lb_eq, cA_eq (by norm_num), compA_pc c5 c5, compA_pc c6 c6, compA_pc c5 ca1,
      compA_pc c6 ca1, compA_pc (cn_pc c5 ca1) (cn_pc c5 ca1),
      compA_pc (cn_pc c6 ca1) (cn_pc c6 ca1), idA_eq, eqA_pc (cn_pc c5 c5) kPid,
      eqA_pc (cn_pc c6 c6) kPid, eqA_pc (cn_pc (cn_pc c5 ca1) (cn_pc c5 ca1)) kPid,
      eqA_pc (cn_pc (cn_pc c6 ca1) (cn_pc c6 ca1)) kPid]
    exact ⟨⟨h0.1, h0.2⟩, ⟨h1.1, h1.2⟩⟩
  · rw [List.all_eq_true]
    intro w hw
    obtain ⟨k, hk, rfl⟩ := mem_getD hw
    rw [wCR_len] at hk
    have ok := allN_spec kOkR k hk
    have h := band (allN_spec kR12 k hk)
    simp only [Bool.and_eq_true]
    rw [cr_eq hk, i0_eq, j0_eq, commY_eq (okK_iff ok).1 c1, commY_eq (okK_iff ok).1 c2]
    exact ⟨h.1, h.2⟩

theorem r0_k : r0CheckY (reflTab ()) = true := by
  have c1 := cnE (k := 1) (by norm_num)
  have c2 := cnE (k := 2) (by norm_num)
  have hq := q8_cn c1 c2
  have hok : ∀ a ∈ q8K (EL.G 1) (EL.G 2), okK a = true := List.all_eq_true.1 kQ8a
  unfold r0CheckY
  simp only [Bool.and_eq_true]
  rw [i0_eq, j0_eq, q8_eq c1 c2]
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · rw [List.all_map, List.all_eq_true]
    intro a ha
    exact validA_ok (hok a ha)
  · rw [List.all_map, List.all_eq_true]
    intro a ha
    rw [Function.comp_apply, List.all_map, List.all_eq_true]
    intro b hb
    rw [Function.comp_apply, compA_pc (hq a ha) (hq b hb), inLY_eq hq (cn_pc (hq a ha) (hq b hb))]
    exact List.all_eq_true.1 (List.all_eq_true.1 kQ8b a ha) b hb
  · rw [List.all_map, List.all_eq_true]
    intro a ha
    rw [Function.comp_apply, invCand_pinv (hok a ha), inLY_eq hq (okK_iff (hok a ha)).2.2]
    exact List.all_eq_true.1 kQ8c a ha

end CertificateChecks.KernelOm2

end
