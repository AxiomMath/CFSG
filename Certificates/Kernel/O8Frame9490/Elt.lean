module

public import Certificates.Kernel.O8Frame9490.Glue
import CFSG.Certificates.Kernel.Spor.LevelTrSound

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelO8F

open CFSG.KC.Enum CFSG.KC.O8 CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CertificateChecks.KernelO8
open CFSG.KC.O8F CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Omega8Frame
open CFSG.EvenSmallLie.OmegaEightMinus CFSG.Monster.B.Co2.Native CFSG.Certificates.Native
open CFSG.KC.Misc.PairCount (unpack_get)

theorem lev_facts {i : Nat} (hi : i < 3) :
    j0Levels[i]!.pts.size = 3 ∧ ∀ k < 3, j0Levels[i]!.tr[k]! = unpack 136 8 (trJ i k) := by
  obtain ⟨h1, h2⟩ := levelTr_sound bindsJ J.head J.hl (i := i) hi
  have hr : rcnt (J.LR i) = 3 := Nat.eq_of_beq_eq_true (band (allN_spec kTR i hi)).1
  rw [hr] at h1 h2
  exact ⟨h1, h2⟩

theorem trJ_cn {i k : Nat} (hi : i < 3) (hk : k < 3) : cnM (trJ i k) = true :=
  allN_spec (band (allN_spec kTR i hi)).2 k hk

theorem prod3_eq {a b c : Nat} (ha : a < 3) (hb : b < 3) (hc : c < 3) :
    prod3 136 j0Levels a b c = unpack 136 8 (x3 a b c) ∧ cnM (x3 a b c) = true := by
  have c0 := trJ_cn (i := 0) (by norm_num) ha
  have c1 := trJ_cn (i := 1) (by norm_num) hb
  have c2 := trJ_cn (i := 2) (by norm_num) hc
  have e : prod3 136 j0Levels a b c = compA 136 (compA 136 (unpack 136 8 (trJ 0 a))
      (unpack 136 8 (trJ 1 b))) (unpack 136 8 (trJ 2 c)) := by
    unfold prod3 tr3
    conv_rhs => unfold compA
    refine congrArg (Array.ofFn (n := 136)) (funext fun p => ?_)
    rw [(lev_facts (i := 0) (by norm_num)).2 a ha, (lev_facts (i := 1) (by norm_num)).2 b hb,
      (lev_facts (i := 2) (by norm_num)).2 c hc, getElem!_ofFn136 (cn_lt c2 p.2)]
  rw [e, compA_pcM c0 c1, compA_pcM (cn_pcM c0 c1) c2]
  exact ⟨rfl, cn_pcM (cn_pcM c0 c1) c2⟩

theorem cand_letters : ∀ w ∈ candWords, ∀ i ∈ w, i < 3 := by decide

theorem word_ok {w : List Nat} (hw : w ∈ candWords) : okK (nWK w) = true :=
  List.all_eq_true.1 kWords w hw

theorem nWordA_eq : ∀ w : List Nat, (∀ i ∈ w, i < 3) →
    nWordA w = unpack 136 8 (nWK w) ∧ cnM (nWK w) = true
  | [], _ => ⟨idA_eq, cn_id⟩
  | i :: w, h => by
    obtain ⟨e, ho⟩ := ng_eq (h i (List.mem_cons_self ..))
    obtain ⟨e', hc⟩ := nWordA_eq w fun j hj => h j (List.mem_cons_of_mem _ hj)
    have hn : nWK (i :: w) = pcM (NGK i) (nWK w) := rfl
    rw [hn]
    refine ⟨?_, cn_pcM (okK_iff ho).1 hc⟩
    change compA 136 nGens[i]! (nWordA w) = _
    rw [e, e', compA_pcM (okK_iff ho).1 hc]

theorem conj_eq {w : List Nat} (hw : w ∈ candWords) {X : Nat} (hx : cnM X = true) :
    conjA (nWordA w) (unpack 136 8 X) = unpack 136 8 (cjM (nWK w) X) := by
  rw [(nWordA_eq w (cand_letters w hw)).1]
  exact conjA_cjM (word_ok hw) hx

theorem samePt_eq {Y Y' : Nat} (hY : cnM Y = true) (hY' : okK Y' = true) :
    samePt (unpack 136 8 Y) (unpack 136 8 Y') = (Nat.beq Y Y' || Nat.beq Y (pinvM Y')) := by
  obtain ⟨c1, c2, c3⟩ := okK_iff hY'
  unfold samePt
  rw [invCand_pinvM c2, eqA_pcM hY c1, eqA_pcM hY c3]

theorem pickGo_eq {X : Nat} (hX : cnM X = true)
    (hc : ∀ w ∈ candWords, okK (cjM (nWK w) X) = true) :
    ∀ ws : List (List Nat), (∀ w ∈ ws, w ∈ candWords) → ∀ (seen : List Nat) (acc : List (List Nat)),
      (∀ y ∈ seen, okK y = true) →
      pickGo (unpack 136 8 X) ws (seen.map (unpack 136 8)) acc = pickGoK X ws seen acc
  | [], _, seen, acc, _ => by
    rw [pickGo, pickGoK]
  | w :: ws, hws, seen, acc, hs => by
    have hw := hws w (List.mem_cons_self ..)
    have hr : ∀ v ∈ ws, v ∈ candWords := fun v hv => hws v (List.mem_cons_of_mem _ hv)
    have hy := hc w hw
    have hany : (seen.map (unpack 136 8)).any (samePt (unpack 136 8 (cjM (nWK w) X))) =
        seen.any (fun y' => Nat.beq (cjM (nWK w) X) y' || Nat.beq (cjM (nWK w) X) (pinvM y')) := by
      rw [List.any_map]
      apply Bool.eq_iff_iff.2
      simp only [List.any_eq_true, Function.comp]
      constructor
      · rintro ⟨y, hy', e⟩
        exact ⟨y, hy', by rw [← samePt_eq (okK_iff hy).1 (hs y hy')]; exact e⟩
      · rintro ⟨y, hy', e⟩
        exact ⟨y, hy', by rw [samePt_eq (okK_iff hy).1 (hs y hy')]; exact e⟩
    rw [pickGo, pickGoK]
    simp only [conj_eq hw hX]
    by_cases h4 : acc.length = 4
    · rw [if_pos h4, if_pos h4]
    · rw [if_neg h4, if_neg h4, hany]
      by_cases ha : seen.any (fun y' => Nat.beq (cjM (nWK w) X) y' ||
          Nat.beq (cjM (nWK w) X) (pinvM y')) = true
      · rw [if_pos ha, if_pos ha]
        exact pickGo_eq hX hc ws hr seen acc hs
      · rw [if_neg ha, if_neg ha]
        have := pickGo_eq hX hc ws hr (cjM (nWK w) X :: seen) (w :: acc) (by
          intro y hy'
          rcases List.mem_cons.1 hy' with e | e
          · rw [e]
            exact hy
          · exact hs y e)
        rw [List.map_cons] at this
        exact this

theorem pickGoK_mem {X : Nat} : ∀ (ws : List (List Nat)) (seen : List Nat) (acc : List (List Nat))
    (v : List Nat), v ∈ pickGoK X ws seen acc → v ∈ ws ∨ v ∈ acc
  | [], seen, acc, v, h => by
    rw [pickGoK, List.mem_reverse] at h
    exact Or.inr h
  | w :: ws, seen, acc, v, h => by
    rw [pickGoK] at h
    split_ifs at h with h4 ha
    · rw [List.mem_reverse] at h
      exact Or.inr h
    · rcases pickGoK_mem ws seen acc v h with e | e
      · exact Or.inl (List.mem_cons_of_mem _ e)
      · exact Or.inr e
    · rcases pickGoK_mem ws _ _ v h with e | e
      · exact Or.inl (List.mem_cons_of_mem _ e)
      · rcases List.mem_cons.1 e with e | e
        · rw [e]
          exact Or.inl (List.mem_cons_self ..)
        · exact Or.inr e

theorem beq_nat (k l : Nat) : (k == l) = Nat.beq k l := by
  cases h : Nat.beq k l
  · have := Nat.ne_of_beq_eq_false h
    simp [this]
  · simp [Nat.eq_of_beq_eq_true h]

theorem sepOK_of {X : Nat} (hX : okK X = true)
    (hc : ∀ w ∈ candWords, okK (cjM (nWK w) X) = true) {ws : List (List Nat)}
    (hws : ∀ w ∈ ws, w ∈ candWords) (h : sepK X ws = true) : sepOK (unpack 136 8 X) ws = true := by
  obtain ⟨c1, c2, c3⟩ := okK_iff hX
  unfold sepK at h
  simp only [Bool.and_eq_true] at h
  obtain ⟨⟨h1, h2⟩, h3⟩ := h
  have hl : ws.length = 4 := by simpa using h1
  unfold sepOK
  simp only [Bool.and_eq_true]
  refine ⟨⟨h1, h2⟩, ?_⟩
  rw [allLt_true]
  intro k hk
  rw [allLt_true]
  intro l hl'
  have e := allN_spec (allN_spec h3 k hk) l hl'
  have mk : ws[k]! ∈ candWords := by
    rw [getElem!_pos ws k (by omega)]
    exact hws _ (List.getElem_mem _)
  have ml : ws[l]! ∈ candWords := by
    rw [getElem!_pos ws l (by omega)]
    exact hws _ (List.getElem_mem _)
  rw [beq_nat, conj_eq mk c1, conj_eq ml c1, invCand_pinvM c2, conj_eq ml c3,
    eqA_pcM (cn_cj (word_ok mk) c1) (cn_cj (word_ok ml) c1),
    eqA_pcM (cn_cj (word_ok mk) c1) (cn_cj (word_ok ml) c3)]
  exact e

theorem notSix_eq {X : Nat} (hX : cnM X = true) : notSix (unpack 136 8 X) = notSixK X := by
  apply Bool.eq_iff_iff.2
  unfold notSix notSixK
  rw [allLt_true, List.all_eq_true]
  simp only [List.mem_range]
  refine forall_congr' fun k => ⟨fun h hk => ?_, fun h hk => ?_⟩
  · rw [← eqA_pcM hX (six_eq hk).2, ← (six_eq hk).1]
    exact h hk
  · rw [(six_eq hk).1, eqA_pcM hX (six_eq hk).2]
    exact h hk

theorem zArr_eq : zArr = unpack 136 8 ZK := by
  have b0 := (okK_iff (bk_ok (i := 0) (by norm_num))).1
  have b1 := (okK_iff (bk_ok (i := 1) (by norm_num))).1
  have b2 := (okK_iff (bk_ok (i := 2) (by norm_num))).1
  change compA 136 (compA 136 betaArrs[0]! betaArrs[1]!) betaArrs[2]! = _
  rw [beta_eq (i := 0) (by norm_num), beta_eq (i := 1) (by norm_num),
    beta_eq (i := 2) (by norm_num), compA_pcM b0 b1, compA_pcM (cn_pcM b0 b1) b2]
  rfl

theorem elt_k : CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Omega8Frame.eltCheck = true := by
  unfold CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Omega8Frame.eltCheck
  dsimp only
  have s0 := (lev_facts (i := 0) (by norm_num)).1
  have s1 := (lev_facts (i := 1) (by norm_num)).1
  have s2 := (lev_facts (i := 2) (by norm_num)).1
  rw [s0, s1, s2, allLt_true]
  intro a ha
  rw [allLt_true]
  intro b hb
  rw [allLt_true]
  intro c hc
  obtain ⟨ex, cx⟩ := prod3_eq ha hb hc
  have hE := allN_spec (allN_spec (allN_spec kElt a ha) b hb) c hc
  unfold eltK at hE
  rw [strictB_eq] at hE
  obtain ⟨e1, hE⟩ := band hE
  obtain ⟨e2, hE⟩ := band hE
  obtain ⟨e3, hE⟩ := band hE
  obtain ⟨e4, hE⟩ := band hE
  obtain ⟨e5, hE⟩ := band hE
  obtain ⟨e6, e7⟩ := band hE
  obtain ⟨o1, o2, o3⟩ := okK_iff e1
  have hcw : ∀ w ∈ candWords, okK (cjM (nWK w) (x3 a b c)) = true := List.all_eq_true.1 e6
  have hcc := (okK_iff (gen_ok (x := CK) (by simp)).1).1
  have hz := okK_iff kZ
  rw [ex]
  simp only [Bool.and_eq_true]
  refine ⟨⟨⟨⟨?_, ?_⟩, ?_⟩, ?_⟩, ?_⟩
  · rw [compA_pcM cx cx, compA_pcM cx (cn_pcM cx cx), idA_eq, eqA_pcM (cn_pcM cx (cn_pcM cx cx)) cn_id]
    exact e2
  · rw [allLt_true]
    intro a' ha'
    rw [allLt_true]
    intro b' hb'
    rw [allLt_true]
    intro c' hc'
    obtain ⟨ey, cy⟩ := prod3_eq ha' hb' hc'
    rw [ey, compA_pcM cx cy, compA_pcM cy cx, eqA_pcM (cn_pcM cx cy) (cn_pcM cy cx)]
    exact allN_spec (allN_spec (allN_spec e3 a' ha') b' hb') c' hc'
  · rw [suppA_eq, notSix_eq cx]
    revert e4
    cases h : Nat.beq (suppK (x3 a b c)) 108
    · have hne : suppK (x3 a b c) ≠ 108 := Nat.ne_of_beq_eq_false h
      cases notSixK (x3 a b c) <;> simp [hne]
    · have he := Nat.eq_of_beq_eq_true h
      cases notSixK (x3 a b c) <;> simp [he]
  · rw [c_eq, compA_pcM cx hcc, compA_pcM hcc cx, eqA_pcM (cn_pcM cx hcc) (cn_pcM hcc cx), idA_eq,
      eqA_pcM cx cn_id, zArr_eq, eqA_pcM cx hz.1, invCand_pinvM hz.2.1, eqA_pcM cx hz.2.2]
    exact e5
  · rw [idA_eq, eqA_pcM cx cn_id, suppA_eq]
    simp only [Bool.or_eq_true] at e7 ⊢
    rcases e7 with (h | h) | h
    · exact Or.inl (Or.inl h)
    · exact Or.inl (Or.inr (by simp [Nat.eq_of_beq_eq_true h]))
    · refine Or.inr ?_
      have ep : pick4 (unpack 136 8 (x3 a b c)) = pickGoK (x3 a b c) candWords [] [] := by
        unfold pick4
        exact pickGo_eq cx hcw candWords (fun w hw => hw) [] [] (by simp)
      rw [ep]
      refine sepOK_of e1 hcw (fun v hv => ?_) h
      rcases pickGoK_mem candWords [] [] v hv with e | e
      · exact e
      · simp at e

end CertificateChecks.KernelO8F

end
