
module

public import Certificates.Kernel.OmegaEight.SA3009K
public import Certificates.Kernel.OmegaEight.Aut
public import CFSG.Certificates.Kernel.O8SASound
public import CFSG.Certificates.Kernel.BfsPinUnpack

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelO8

open CFSG.KC.Enum CFSG.KC.O8 CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.EvenSmallLie.OmegaEight
  CFSG.Monster.B.Co2.Native CFSG.Certificates.Native
open CFSG.KC.BfsPin (compA_unpack invCand_unpack canonK_pcomp)
open CFSG.KLC.E8 (strictB_eq')

theorem fld_eq (r o w : Nat) : Nat.land (Nat.shiftRight r o) (2 ^ w - 1) = r / 2 ^ o % 2 ^ w := by
  change (r >>> o) &&& (2 ^ w - 1) = _
  rw [Nat.and_two_pow_sub_one_eq_mod, Nat.shiftRight_eq_div_pow]

theorem saAtK_eq (SC i : Nat) : saAtK SC i = SC / 2 ^ (64 * i) % 2 ^ 64 := fld_eq SC (64 * i) 64

theorem ix13_eq (T i : Nat) : ix13 T i = T / 2 ^ (13 * i) % 8192 := fld_eq T (13 * i) 13

theorem saMat_eq (i : Nat) : saMat i = saAtK saCodes i := (saAtK_eq _ _).symm
theorem saGen_eq (l : Nat) : saGen l = ix13 saGenT l := (ix13_eq _ _).symm
theorem saMul_eq (i l : Nat) : saMul i l = ix13 saMulT (Nat.add (Nat.mul 5 i) l) :=
  (ix13_eq _ _).symm
theorem saPar_eq (i : Nat) : saPar i = ix13 saParT i := (ix13_eq _ _).symm
theorem saLab_eq (i : Nat) : saLab i = Nat.land (Nat.shiftRight saLabT (Nat.mul 3 i)) 7 :=
  (fld_eq saLabT (3 * i) 3).symm
theorem yIdx_eq (j : Nat) : yIdx j = ix13 yIdxT j := (ix13_eq _ _).symm
theorem rgCode_eq (j l : Nat) : rgCode j l = saAtK rgT (Nat.add (Nat.mul 5 j) l) :=
  (saAtK_eq _ _).symm
theorem rgInv_eq (j l : Nat) : rgInv j l = saAtK rgInvT (Nat.add (Nat.mul 5 j) l) :=
  (saAtK_eq _ _).symm

theorem invW_eq (i : Nat) : invW i =
    (Nat.land (Nat.shiftRight invWT (Nat.add (Nat.mul 32 i) 26)) 63,
      Nat.land (Nat.shiftRight invWT (Nat.add (Nat.mul 32 i) 13)) 8191,
      Nat.land (Nat.shiftRight invWT (Nat.mul 32 i)) 8191) :=
  Prod.ext (fld_eq invWT (32 * i + 26) 6).symm
    (Prod.ext (fld_eq invWT (32 * i + 13) 13).symm (fld_eq invWT (32 * i) 13).symm)

theorem idK_eq : CFSG.KC.O8.idK = idCode := by decide +kernel

theorem blt_true {a b : Nat} (h : a < b) : Nat.blt a b = true := Nat.blt_eq.mpr h
theorem of_blt {a b : Nat} (h : Nat.blt a b = true) : a < b := Nat.blt_eq.mp h
theorem ble_true {a b : Nat} (h : a ≤ b) : Nat.ble a b = true := Nat.ble_eq.mpr h
theorem beq_false {a b : Nat} (h : a ≠ b) : Nat.beq a b = false :=
  Bool.eq_false_iff.2 fun e => h (Nat.eq_of_beq_eq_true e)
theorem beq_true {a b : Nat} (h : a = b) : Nat.beq a b = true := h ▸ Nat.beq_refl a

theorem forall_of_blocks {f : Nat → Bool} {B k r : Nat} (h : ∀ s < k, allBlk (B * s) f B = true)
    (hr : allBlk (B * k) f r = true) : ∀ i < B * k + r, f i = true := by
  intro i hi
  rcases Nat.lt_or_ge i (B * k) with h1 | h1
  · have hB : 0 < B := Nat.pos_of_ne_zero fun e => by simp [e] at h1
    have hs : i / B < k := Nat.div_lt_of_lt_mul h1
    have := allBlk_spec (h (i / B) hs) (i % B) (Nat.mod_lt i hB)
    rwa [Nat.add_eq, Nat.div_add_mod] at this
  · have := allBlk_spec hr (i - B * k) (by omega)
    rwa [Nat.add_eq, Nat.add_sub_cancel' h1] at this

theorem ns_bind : ∀ p < 120, nsArr[p]! = pg 8 255 NSP p := by decide +kernel

theorem ni_bind : ∀ v < 256, nsIdx[v]! = pg 8 255 NIP v := by decide +kernel

theorem perm_of_head {n w kS kO nb BP : Nat} {PS PSI : Nat → Nat} {D : List (List Int)}
    (h : headK n w (mask w) (n * w) (pidn n w) PS PSI kS kO D nb BP = true) :
    allN kS (fun j => permOK n w (mask w) (n * w) (PS j) (PSI j)) = true := by
  unfold headK at h
  simp only [bAnd_iff] at h
  exact h.2.2.2.2.1

theorem wordEqK_of {S SI : Nat → Nat} {kS : Nat} {wd : List Int} (h : lettersK kS wd = true) :
    wordEqK 360 9 (mask 9) (pidn 360 9) S SI kS wd (wordK 360 9 (mask 9) (pidn 360 9) S SI wd) =
      true := by
  unfold wordEqK
  rw [h, Nat.beq_refl]
  rfl

theorem sylowGens_bind : sylowGens.size = 5 ∧ ∀ j < 5, sylowGens[j]! = unpack 360 9 (SY.S j) := by
  refine ⟨sylowGens_size, fun j hj => ?_⟩
  rw [sylowGens_getElem! hj, genAP.2 _ (sylowIdx_lt hj), Nat.eq_of_beq_eq_true (allN_spec kGenSY j hj)]

theorem genArrs_bindQ : genArrs.size = 10 ∧ ∀ j < 10, genArrs[j]! = unpack 360 9 (AQ.S j) :=
  ⟨genAP.1, fun j hj => by rw [genAP.2 j hj, Nat.eq_of_beq_eq_true (allN_spec kGenAQ j hj)]⟩

theorem sylowS_bind : sylowS.size = 8 ∧ ∀ j < 8, sylowS[j]! = unpack 360 9 (SY.S j) :=
  pushWords_eq sylowGens_bind SY.head

theorem autS_bind : autS.size = 18 ∧ ∀ j < 18, autS[j]! = unpack 360 9 (AQ.S j) :=
  pushWords_eq genArrs_bindQ AQ.head

theorem omegaS_bind : omegaS.size = 17 ∧ ∀ j < 17, omegaS[j]! = unpack 360 9 (OmP.S j) :=
  ⟨chainOmP.1.2.2.2.1, chainOmP.1.2.2.2.2.1⟩

theorem sylowW_eq {wd : List Int} (h : lettersK 8 wd = true) : sylowW wd = unpack 360 9 (wS wd) :=
  (wordEqK_sound sylowS_bind (perm_of_head SY.head) (wordEqK_of h)).1

theorem autW_eq {wd : List Int} (h : lettersK 18 wd = true) : autW wd = unpack 360 9 (wA wd) :=
  (wordEqK_sound autS_bind (perm_of_head AQ.head) (wordEqK_of h)).1

theorem omegaW_eq {wd : List Int} (h : lettersK 17 wd = true) : omegaW wd = unpack 360 9 (wO wd) :=
  (wordEqK_sound omegaS_bind (perm_of_head OmP.head) (wordEqK_of h)).1

theorem compA_pc {p q : Nat} (hp : cn p = true) (hq : cn q = true) :
    compA 360 (unpack 360 9 p) (unpack 360 9 q) = unpack 360 9 (pc p q) := compA_unpack hp hq

theorem cn_pc {p q : Nat} (hp : cn p = true) (hq : cn q = true) : cn (pc p q) = true :=
  canonK_pcomp hp hq

theorem invCand_pinv {p : Nat} (h : permOK 360 9 (mask 9) (360 * 9) p (pinv p) = true) :
    invCand 360 (unpack 360 9 p) = unpack 360 9 (pinv p) := invCand_unpack h

theorem conjArr_cj {c x : Nat} (hc : cn c = true) (hci : cn (pinv c) = true)
    (hp : permOK 360 9 (mask 9) (360 * 9) c (pinv c) = true) (hx : cn x = true) :
    conjArr (unpack 360 9 c) (unpack 360 9 x) = unpack 360 9 (cj c x) := by
  unfold conjArr
  rw [invCand_pinv hp, compA_pc hc hx, compA_pc (cn_pc hc hx) hci]
  rfl

theorem getD_map_of_lt {α β : Type} (f : α → β) {l : List α} (d : α) (d' : β) {j : Nat}
    (h : j < l.length) : (l.map f).getD j d' = f (l.getD j d) := by
  simp [List.getD_eq_getElem?_getD, h]

theorem rgLen_eq : ∀ j < 38, rgLen j = 4 := by decide

theorem repGens_length {j : Nat} (hj : j < 38) : (repGens j).length = 5 := by
  have := rgLen_eq j hj
  unfold rgLen at this
  rw [repGens, List.length_append, List.length_map, this]
  rfl

theorem repArrs_get {j : Nat} (hj : j < 38) (h : lettersK 8 (repWords.getD j []) = true) :
    repArrs.getD j #[] = unpack 360 9 (wS (repWords.getD j [])) := by
  rw [repArrs, getD_map_of_lt sylowW [] #[] (by simp [repWords]; omega), sylowW_eq h]

theorem rgJ_ok : ∀ j < 38, rgJ j = true :=
  forall_of_blocks (B := 8) (k := 4) (fun s hs => by
    interval_cases s
    exacts [kRg0, kRg1, kRg2, kRg3]) kRg4

theorem fiveJ_ok : ∀ j < 38, fiveJ j = true :=
  forall_of_blocks (B := 4) (k := 9) (fun s hs => by
    interval_cases s
    exacts [kFive0, kFive1, kFive2, kFive3, kFive4, kFive5, kFive6, kFive7, kFive8]) kFive9

theorem closed_ok : ∀ i < 8192, saClosedAt saCodes saMulT saGenT i = true :=
  forall_of_blocks (B := 1024) (k := 8) (r := 0) (fun s hs => by
    interval_cases s
    exacts [kClosed0, kClosed1, kClosed2, kClosed3, kClosed4, kClosed5, kClosed6, kClosed7]) rfl

theorem invol_ok : ∀ i < 8192, involAt saCodes yIdxT invWT i = true :=
  forall_of_blocks (B := 2048) (k := 4) (r := 0) (fun s hs => by
    interval_cases s
    exacts [kInvol0, kInvol1, kInvol2, kInvol3]) rfl

theorem repGens_get {j l : Nat} (hj : j < 38) (hl : l < 5) :
    (repGens j).getD l #[] = unpack 360 9 (rgK j l) ∧ rgOK j l = true := by
  have hlen := rgLen_eq j hj
  have hr := allN_spec (rgJ_ok j hj) l hl
  rw [ble_true (by omega : l ≤ rgLen j)] at hr
  refine ⟨?_, hr⟩
  unfold rgOK at hr
  simp only [bAnd_iff] at hr
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, -⟩ := hr
  have e1 : (cent0Words.getD (repTypes.getD j 0) []).length = 4 := hlen
  rcases Nat.lt_or_ge l 4 with h | h
  · rw [repGens, List.getD_append _ _ _ _ (by rw [List.length_map, e1]; exact h),
      getD_map_of_lt _ [] #[] (by rw [e1]; exact h),
      conjArrs, getD_map_of_lt autW [] #[] (by simp [conjWords]; omega), autW_eq h1, omegaW_eq h2,
      conjArr_cj h3 h4 h5 h6]
    unfold rgK
    rw [blt_true (by omega : l < rgLen j)]
  · have hl4 : l = 4 := by omega
    subst hl4
    have hk := allN_spec kReps j hj
    simp only [bAnd_iff] at hk
    rw [repGens, List.getD_append_right _ _ _ _ (by rw [List.length_map, e1]), List.length_map, e1,
      Nat.sub_self, List.getD_cons_zero, repArrs_get hj hk.2.1]
    unfold rgK
    rw [hlen]
    rfl

theorem acts_of {P M : Nat} (h : actsK NSP NIP P M = true) : ActsOn0 (unpack 360 9 P) M :=
  actsK_sound ns_bind ni_bind h

theorem cw_letters : ∀ v ∈ cw, ∀ l ∈ v, l < 5 := by decide

theorem sorted_mono {f : Nat → Nat} (h : ∀ a < 8191, f a < f (a + 1)) :
    ∀ b < 8192, ∀ a < b, f a < f b := by
  intro b
  induction b with
  | zero => intro _ a ha; omega
  | succ b ih =>
    intro hb a ha
    rcases Nat.lt_or_ge a b with h1 | h1
    · exact (ih (by omega) a h1).trans (h b (by omega))
    · have : a = b := by omega
      subst this
      exact h a (by omega)

theorem sa_facts_k : SAFacts where
  gens l hl := by
    have h := allN_spec kGens l hl
    simp only [bAnd_iff, Nat.blt_eq] at h
    rw [saGen_eq, saMat_eq, sylowGens_getElem! hl, genAP.2 _ (sylowIdx_lt hl)]
    exact ⟨h.1, acts_of h.2⟩
  id0 := by rw [saMat_eq, Nat.eq_of_beq_eq_true kId, idK_eq]
  closed i hi l hl := by
    have h := closed_ok i hi
    unfold saClosedAt at h
    simp only [strictB_eq'] at h
    have h2 := Nat.eq_of_beq_eq_true (allN_spec h l hl)
    rw [matMulK_eq] at h2
    simp only [saMat_eq, saGen_eq, saMul_eq]
    exact h2
  tree i hi h0 := by
    have h := allN_spec kTree i hi
    unfold saTreeAt at h
    rw [beq_false (by omega : i ≠ 0)] at h
    simp only [strictB_eq', bAnd_iff, Nat.blt_eq, Nat.beq_eq] at h
    rw [saPar_eq, saLab_eq, saMul_eq]
    exact h
  distinct i hi k hk e := by
    have hs : ∀ a < 8192, ix13 saSPI a < 8192 ∧ ix13 saSP (ix13 saSPI a) = a ∧
        (a < 8191 → saAtK saCodes (ix13 saSP a) < saAtK saCodes (ix13 saSP (a + 1))) := by
      intro a ha
      have h := allN_spec kSortSA a ha
      unfold saSortAt at h
      simp only [bAnd_iff, Nat.blt_eq, Nat.beq_eq] at h
      refine ⟨h.1, h.2.1, fun h' => ?_⟩
      have h3 := h.2.2
      rw [blt_true h'] at h3
      exact of_blt h3
    have hm := sorted_mono (f := fun a => saAtK saCodes (ix13 saSP a)) fun a ha => (hs a (by omega)).2.2 ha
    obtain ⟨hi1, hi2, -⟩ := hs i hi
    obtain ⟨hk1, hk2, -⟩ := hs k hk
    rw [saMat_eq, saMat_eq, ← hi2, ← hk2] at e
    rcases Nat.lt_trichotomy (ix13 saSPI i) (ix13 saSPI k) with h | h | h
    · exact absurd e (Nat.ne_of_lt (hm _ hk1 _ h))
    · rw [← hi2, ← hk2, h]
    · exact absurd e (Nat.ne_of_gt (hm _ hi1 _ h))
  span := by decide +kernel
  reps j hj := by
    have h := allN_spec kReps j hj
    simp only [bAnd_iff] at h
    rw [yIdx_eq, saMat_eq, repArrs_get hj h.2.1]
    exact ⟨of_blt h.1, acts_of h.2.2.2⟩
  invol i hi h0 hsq := by
    have h := invol_ok i hi
    unfold involAt at h
    rw [saMat_eq, ← matMulK_eq, ← idK_eq] at hsq
    simp only [strictB_eq'] at h
    rw [beq_false h0, beq_true hsq] at h
    simp only [bAnd_iff, Nat.blt_eq, Nat.beq_eq] at h
    obtain ⟨h1, h2, h3, h4, h5⟩ := h
    rw [invW_eq]
    simp only [saMat_eq, yIdx_eq, ← matMulK_eq, ← idK_eq]
    exact ⟨h1, h2, h3, h4, h5⟩
  rg j hj l hl := by
    rw [repGens_length hj] at hl
    obtain ⟨e, h⟩ := repGens_get hj hl
    unfold rgOK at h
    simp only [bAnd_iff] at h
    rw [e, invCand_pinv h.2.2.2.2.2.2.2.1, rgCode_eq, rgInv_eq]
    exact ⟨acts_of h.2.2.2.2.2.2.2.2.1, acts_of h.2.2.2.2.2.2.2.2.2⟩
  five j hj i hi h1 h2 h3 := by
    have h := allN_spec (fiveJ_ok j hj) i hi
    unfold fiveAt at h
    simp only [saMat_eq, yIdx_eq, ← matMulK_eq, ← idK_eq] at h1 h2 h3
    simp only [strictB_eq'] at h
    rw [beq_false h1, beq_true h2, beq_true h3] at h
    simp only at h
    obtain ⟨vs, hl, hm, hp⟩ := greedyK_sound _ _ _ cw [] [] rfl List.Pairwise.nil h
    have eG : (fun l => saAtK rgT (Nat.add (Nat.mul 5 j) l)) = rgCode j :=
      funext fun l => (rgCode_eq j l).symm
    have eGi : (fun l => saAtK rgInvT (Nat.add (Nat.mul 5 j) l)) = rgInv j :=
      funext fun l => (rgInv_eq j l).symm
    rw [eG, eGi] at hp
    refine ⟨vs, hl, fun v hv l hl' => ?_, ?_⟩
    · rw [repGens_length hj]
      rcases hm v hv with h' | h'
      · exact absurd h' List.not_mem_nil
      · exact cw_letters v h' l hl'
    · simpa [rgConj, saMat_eq] using hp

end CertificateChecks.KernelO8

end
