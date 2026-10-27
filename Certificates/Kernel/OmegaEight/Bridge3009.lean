
module

public import Certificates.Kernel.OmegaEight.SA3009
public import Certificates.Kernel.OmegaEight.Arr3009K
public import Certificates.Kernel.LocalComp.Weyl3185
public import CFSG.Certificates.Kernel.Child3Sound
public import CFSG.Certificates.Kernel.Spor.SiftEq

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelO8

open CFSG.KC.Enum CFSG.KC.O8 CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.EvenSmallLie.OmegaEight
  CFSG.Monster.B.Co2.Native CFSG.Certificates.Native
open CFSG.KC.BfsPin (compA_unpack invCand_unpack canonK_pcomp eqA_unpack)
open CFSG.KLC.E8 (strictB_eq')
open CFSG.KC.Misc.PairCount (unpack_get)

theorem omegaChain_k : omegaChainCheck = true := by
  unfold omegaChainCheck
  rw [Bool.and_eq_true, wordsOf_eq]
  refine ⟨rawChainK_sound (chunks := 4) chainOmP.1 chainOmP.2.1 chainOmP.2.2.1 chainOmP.2.2.2.1
    chainOmP.2.2.2.2, ?_⟩
  rw [rawOrbitSizesK_sound chainOmP.1 (perm_of_head chainOmP.2.1) chainOmP.2.2.1]
  decide +kernel

theorem bindsAQ : Binds 360 9 AQ.S 18 7 AQ.BP autS ((autBase.map Fin.val).toArray) := by
  refine ⟨by norm_num, by norm_num, by norm_num, autS_bind.1, autS_bind.2, rfl, fun t ht => ?_⟩
  interval_cases t <;> rfl

theorem autChain_k : autChainCheck = true := by
  unfold autChainCheck
  rw [Bool.and_eq_true, wordsOf_eq]
  refine ⟨rawChainK_sound (chunks := 4) bindsAQ AQ.head AQ.hl (by decide) AQ.hs, ?_⟩
  rw [rawOrbitSizesK_sound bindsAQ (perm_of_head AQ.head) AQ.hl]
  decide +kernel

theorem omega1Chain_k : omega1ChainCheck = true := by
  unfold omega1ChainCheck
  rw [Bool.and_eq_true, wordsOf_eq]
  refine ⟨rawChainK_sound (chunks := 4) KernelLC.W3185.binds1 KernelLC.W3185.Om1.head
    KernelLC.W3185.Om1.hl (by decide) KernelLC.W3185.Om1.hs, ?_⟩
  rw [rawOrbitSizesK_sound KernelLC.W3185.binds1 KernelLC.W3185.perm1 KernelLC.W3185.Om1.hl]
  decide +kernel

theorem bindsSY : Binds 360 9 SY.S 8 5 SY.BP sylowS ((sylowBase.map Fin.val).toArray) := by
  refine ⟨by norm_num, by norm_num, by norm_num, sylowS_bind.1, sylowS_bind.2, rfl, fun t ht => ?_⟩
  interval_cases t <;> rfl

theorem sylowChain_k : sylowChainCheck = true := by
  unfold sylowChainCheck
  rw [Bool.and_eq_true, wordsOf_eq]
  refine ⟨rawChainK_sound (chunks := 4) bindsSY SY.head SY.hl (by decide) SY.hs, ?_⟩
  rw [rawOrbitSizesK_sound bindsSY (perm_of_head SY.head) SY.hl]
  decide +kernel

theorem gen_get {j : Nat} (hj : j < 10) : genArrs[j]! = unpack 360 9 (AP.S j) := genAP.2 j hj

theorem omegaS_get {j : Nat} (hj : j < 17) : omegaS[j]! = unpack 360 9 (OmP.S j) := omegaS_bind.2 j hj

theorem at9_eq {P p : Nat} (hp : p < 360) : (unpack 360 9 P)[p]! = at9 P p := unpack_get hp

theorem eqA_pc {p q : Nat} (hp : cn p = true) (hq : cn q = true) :
    eqA 360 (unpack 360 9 p) (unpack 360 9 q) = Nat.beq p q := eqA_unpack hp hq

theorem cn_cj {c x : Nat} (hc : cn c = true) (hci : cn (pinv c) = true) (hx : cn x = true) :
    cn (cj c x) = true := cn_pc (cn_pc hc hx) hci

theorem kPid' : cn pid = true ∧ CFSG.KS.Prim.idK 360 9 (mask 9) = true := (bAnd_iff _ _).1 kPid

theorem idA_eq : idA 360 = unpack 360 9 pid := (idK_sound kPid'.2).symm

theorem cn_pid : cn pid = true := kPid'.1

theorem commArr_pc {p q : Nat} (hp : cn p = true) (hq : cn q = true) :
    commArr (unpack 360 9 p) (unpack 360 9 q) = Nat.beq (pc p q) (pc q p) := by
  unfold commArr
  rw [compA_pc hp hq, compA_pc hq hp, eqA_pc (cn_pc hp hq) (cn_pc hq hp)]

theorem isInvA_of {p : Nat} (h : pm p = true) :
    isInvA 360 (unpack 360 9 p) (invCand 360 (unpack 360 9 p)) = true := by
  have := invEqK_sound h
  rw [this.1]
  exact this.2

theorem powArr_eq (t : Array ℕ) : ∀ k, powArr t k = CFSG.Sporadic.Schreier.Co3.co3PowA 360 t k
  | 0 => rfl
  | k + 1 => by rw [powArr, powArr_eq t k]; rfl

theorem powArr_pc {p : Nat} (hp : cn p = true) (k : Nat) :
    powArr (unpack 360 9 p) k = unpack 360 9 (ppw p k) := by
  rw [powArr_eq]
  exact powEqK_sound ((bAnd_iff _ _).2 ⟨hp, Nat.beq_refl _⟩)

theorem bne_of{a b : Nat} (h : bIf(Nat.beq a b, false, true) = true) : (a != b) = true := by
  revert h
  cases e : Nat.beq a b
  · intro _
    simpa using Nat.ne_of_beq_eq_false e
  · intro h
    exact absurd h (by decide)

theorem not_beq_of {a b : Nat} (h : bIf(Nat.beq a b, false, true) = true) : (!Nat.beq a b) = true := by
  revert h
  cases Nat.beq a b <;> decide

theorem decide_beq_of {a b : Nat}
    (h : bIf(Nat.blt a 120, Nat.blt b 120, bIf(Nat.blt b 120, false, true)) = true) :
    (decide (a < 120) == decide (b < 120)) = true := by
  have e1 : decide (a < 120) = Nat.blt a 120 := by rw [Bool.eq_iff_iff, decide_eq_true_iff, Nat.blt_eq]
  have e2 : decide (b < 120) = Nat.blt b 120 := by rw [Bool.eq_iff_iff, decide_eq_true_iff, Nat.blt_eq]
  rw [e1, e2]
  revert h
  cases Nat.blt a 120 <;> cases Nat.blt b 120 <;> decide

theorem mainArrs_get {i : Nat} (hi : i < 5) (h : lettersK 8 (mainWords.getD i []) = true) :
    mainArrs.getD i #[] = unpack 360 9 (mainK i) := by
  rw [mainArrs, getD_map_of_lt sylowW [] #[] (by simp [mainWords]; omega), sylowW_eq h]
  rfl

theorem main_ok {i : Nat} (hi : i < 5) :
    mainArrs.getD i #[] = unpack 360 9 (mainK i) ∧ cn (mainK i) = true ∧ pm (mainK i) = true := by
  have h := allN_spec kMain i hi
  simp only [bAnd_iff] at h
  exact ⟨mainArrs_get hi h.1, h.2.1, h.2.2⟩

theorem conjArrs_get {j : Nat} (hj : j < 38) (h : lettersK 18 (conjWords.getD j []) = true) :
    conjArrs.getD j #[] = unpack 360 9 (wA (conjWords.getD j [])) := by
  rw [conjArrs, getD_map_of_lt autW [] #[] (by simp [conjWords]; omega), autW_eq h]

theorem structure_k : structureCheck = true := by
  have hC := kStrC
  simp only [bAnd_iff] at hC
  obtain ⟨hc, h8, h9, hi8, hi9⟩ := hC
  have hc' : ∀ j < 10, cn (AP.S j) = true := allN_spec hc
  unfold structureCheck
  rw [Bool.and_eq_true, List.all_eq_true, List.all_eq_true]
  refine ⟨fun i hi => ?_, fun p hp => ?_⟩
  · rw [List.mem_range] at hi
    have h := allN_spec kStr i hi
    simp only [bAnd_iff, Nat.blt_eq] at h
    obtain ⟨hr, ht, e1, e2, hpt⟩ := h
    rw [gen_get (by omega : 8 < 10), gen_get (by omega : 9 < 10), gen_get (by omega : i < 10),
      gen_get hr, gen_get ht, conjArr_cj (hc' 8 (by omega)) hi8 h8 (hc' i (by omega)),
      conjArr_cj (hc' 9 (by omega)) hi9 h9 (hc' i (by omega)),
      eqA_pc (cn_cj (hc' 8 (by omega)) hi8 (hc' i (by omega))) (hc' _ hr),
      eqA_pc (cn_cj (hc' 9 (by omega)) hi9 (hc' i (by omega))) (hc' _ ht), e1, e2]
    simp only [Bool.true_and, List.all_eq_true, List.mem_range]
    intro p hp
    rw [at9_eq hp]
    exact decide_beq_of (allN_spec hpt p hp)
  · rw [List.mem_range] at hp
    rw [gen_get (by omega : 8 < 10), at9_eq hp]
    exact beq_iff_eq.2 (Nat.eq_of_beq_eq_true (allN_spec kRho p hp))

theorem stab_k : CFSG.EvenSmallLie.OmegaEight.stabCheck = true := by
  unfold CFSG.EvenSmallLie.OmegaEight.stabCheck
  rw [Bool.and_eq_true, List.all_eq_true, List.all_eq_true]
  refine ⟨fun j hj => ?_, fun p hp => ?_⟩
  · have h := List.all_eq_true.1 kStab1 j hj
    simp only [bAnd_iff, Nat.blt_eq] at h
    rw [omegaS_bind.1, omegaS_get h.1, at9_eq (p := 0) (by norm_num)]
    simp [h.1, Nat.eq_of_beq_eq_true h.2]
  · rw [List.mem_range] at hp
    have h := allN_spec kStab2 p hp
    rw [List.any_eq_true] at h ⊢
    obtain ⟨j, hj, hne⟩ := h
    have hj17 := of_blt ((bAnd_iff _ _).1 (List.all_eq_true.1 kStab1 j hj)).1
    refine ⟨j, hj, ?_⟩
    rw [omegaS_get hj17, at9_eq (p := p + 1) (by omega)]
    exact bne_of hne

theorem tree_k : treeLitCheck = true := by
  have hm : (treeLit.2.2[0]! == 0) = true ∧ ∀ i < 119, treeLit.1[i + 1]! < 120 ∧
      treeLit.2.1[i + 1]! < 8 ∧ treeLit.2.2[treeLit.1[i + 1]!]! < treeLit.2.2[i + 1]! := by
    decide +kernel
  unfold treeLitCheck treeOK
  rw [Bool.and_eq_true, List.all_eq_true]
  refine ⟨hm.1, fun i hi => ?_⟩
  rw [List.mem_range] at hi
  obtain ⟨h1, h2, h3⟩ := hm.2 i hi
  rw [gen_get (lt_of_lt_of_le h2 (by norm_num)), at9_eq (lt_of_lt_of_le h1 (by norm_num))]
  simp only [Bool.and_eq_true, decide_eq_true_eq]
  exact ⟨⟨⟨h1, h2⟩, h3⟩, beq_iff_eq.2 (Nat.eq_of_beq_eq_true (allN_spec kTreeG i hi))⟩

theorem repArrs_mem {r : Array ℕ} (hr : r ∈ repArrs) : ∃ j < 38, repArrs.getD j #[] = r := by
  obtain ⟨j, hj, e⟩ := List.mem_iff_getElem.1 hr
  have hl : repArrs.length = 38 := by simp [repArrs, repWords]
  refine ⟨j, hl ▸ hj, ?_⟩
  rw [List.getD_eq_getElem _ _ hj, e]

theorem rep_ok {j : Nat} (hj : j < 38) :
    repArrs.getD j #[] = unpack 360 9 (wS (repWords.getD j [])) ∧ cn (wS (repWords.getD j [])) = true := by
  have hk := allN_spec kReps j hj
  simp only [bAnd_iff] at hk
  exact ⟨repArrs_get hj hk.2.1, hk.2.2.1⟩

theorem sylowReps_k : sylowRepsLitCheck = true := by
  unfold sylowRepsLitCheck
  rw [Bool.and_eq_true, List.all_eq_true, List.all_eq_true]
  refine ⟨fun r hr => ?_, fun j hj => ?_⟩
  · obtain ⟨j, hj, rfl⟩ := repArrs_mem hr
    have h := allN_spec kSylowReps j hj
    simp only [bAnd_iff] at h
    obtain ⟨e, hcn⟩ := rep_ok hj
    rw [e, CFSG.KC.Child3.ordTest2_unpack hcn, Bool.and_eq_true]
    exact ⟨h.2.2.1, not_beq_of h.2.2.2.1⟩
  · rw [List.mem_range] at hj
    have h := allN_spec kSylowReps j hj
    simp only [bAnd_iff] at h
    obtain ⟨hcn, hpm, hsq, hne, hsift, ht5, hconj⟩ := h
    obtain ⟨e, -⟩ := rep_ok hj
    have hg := allN_spec (rgJ_ok j hj) 0 (by norm_num)
    rw [ble_true (Nat.zero_le _)] at hg
    unfold rgOK at hg
    simp only [bAnd_iff] at hg
    obtain ⟨hl1, -, hc1, hc2, hc3, -⟩ := hg
    obtain ⟨em, hmc, -⟩ := main_ok (of_blt ht5)
    have hG : Nat.shiftRight (wS (repWords.getD j [])) (360 * 9) = 0 := by
      unfold cn canonK at hcn
      simp only [bAnd_iff] at hcn
      exact Nat.eq_of_beq_eq_true hcn.2.1
    rw [e, conjArrs_get hj hl1, em, conjArr_cj hc1 hc2 hc3 hmc,
      eqA_pc (cn_cj hc1 hc2 hmc) hcn, Nat.eq_of_beq_eq_true hconj, Nat.beq_refl, Bool.and_true,
      siftK_eq chainOmP.1 (perm_of_head chainOmP.2.1) chainOmP.2.2.1 rfl hG
        (range_of_permOK hpm)]
    have h3 : decide (repTypes.getD j 0 < 3) = Nat.blt (repTypes.getD j 0) 3 := by
      rw [Bool.eq_iff_iff, decide_eq_true_iff, Nat.blt_eq]
    rw [h3]
    revert hsift
    cases siftK 360 9 (mask 9) (360 * 9) (pidn 360 9) OmP.LR OmP.TRI OmP.BP 7 0 (wS (repWords.getD j [])) <;>
      cases Nat.blt (repTypes.getD j 0) 3 <;> decide

theorem cent0_k : cent0Check = true := by
  unfold cent0Check
  rw [List.all_eq_true]
  intro i hi
  rw [List.mem_range] at hi
  rw [List.all_eq_true]
  intro wd hw
  have h := List.all_eq_true.1 (allN_spec kCent i hi) wd hw
  simp only [bAnd_iff] at h
  obtain ⟨em, hmc, -⟩ := main_ok hi
  rw [omegaW_eq h.1, em, commArr_pc h.2.1 hmc]
  exact h.2.2.2

theorem fg_k : fgCheck = true := by
  unfold fgCheck
  rw [List.all_eq_true]
  intro i hi
  rw [List.mem_range] at hi
  have h := allN_spec kFg i hi
  simp only [bAnd_iff, strictB_eq'] at h
  obtain ⟨hl, hc, hci, hp, hsq, hne⟩ := h
  obtain ⟨em, hmc, -⟩ := main_ok (by omega : i + 3 < 5)
  simp only
  rw [em, omegaW_eq hl, conjArr_cj hc hci hp hmc, compA_pc (cn_cj hc hci hmc) hmc,
    compA_pc (cn_pc (cn_cj hc hci hmc) hmc) (cn_pc (cn_cj hc hci hmc) hmc), idA_eq,
    eqA_pc (cn_pc (cn_pc (cn_cj hc hci hmc) hmc) (cn_pc (cn_cj hc hci hmc) hmc)) cn_pid,
    eqA_pc (cn_pc (cn_cj hc hci hmc) hmc) cn_pid, Bool.and_eq_true]
  exact ⟨hsq, not_beq_of hne⟩

theorem odd_k : oddCheck = true := by
  unfold oddCheck
  rw [List.all_eq_true]
  intro i hi
  rw [List.mem_range] at hi
  have h := allN_spec kOdd i hi
  simp only [bAnd_iff, strictB_eq'] at h
  obtain ⟨hl1, hl2, hu, hv, hou, hov, hcu, hcv, hpow⟩ := h
  obtain ⟨em, hmc, -⟩ := main_ok (by omega : i < 5)
  have hpar : ∀ k < 3, (oddData.getD k ([], [], 0, 0, 0)).2.2.2.1 % 2 = 1 ∧
      (oddData.getD k ([], [], 0, 0, 0)).2.2.2.2 % 2 = 1 := by decide
  obtain ⟨hp1, hp2⟩ := hpar i hi
  simp only
  rw [em, omegaW_eq hl1, omegaW_eq hl2, CFSG.KC.O8.ordK_sound hu hou, CFSG.KC.O8.ordK_sound hv hov,
    commArr_pc hu hmc, commArr_pc hv hmc, hcu, hcv, compA_pc hu hv, powArr_pc (cn_pc hu hv),
    Nat.eq_of_beq_eq_true hpow, eqA_pc hmc hmc, Nat.beq_refl]
  simp only [hp1, hp2, beq_self_eq_true, Bool.and_self]

theorem invs_k : invsCheck = true := by
  unfold invsCheck
  simp only [Bool.and_eq_true, List.all_eq_true, List.mem_range, List.mem_append]
  refine ⟨⟨⟨fun j hj t ht => ?_, fun t ht => ?_⟩, fun ws hws w hw => ?_⟩, fun w hw => ?_⟩
  · obtain ⟨l, hl, rfl⟩ := List.mem_iff_getElem.1 ht
    have hl5 : l < 5 := by
      rw [← repGens_length hj]
      exact hl
    obtain ⟨e, h⟩ := repGens_get hj hl5
    rw [← List.getD_eq_getElem _ #[] hl, e]
    unfold rgOK at h
    simp only [bAnd_iff] at h
    exact isInvA_of h.2.2.2.2.2.2.2.1
  · rcases ht with (ht | ht) | ht
    · obtain ⟨j, hj, rfl⟩ := List.mem_iff_getElem.1 ht
      have hl : conjArrs.length = 38 := by simp [conjArrs, conjWords]
      have hj' : j < 38 := hl ▸ hj
      have hg := allN_spec (rgJ_ok j hj') 0 (by norm_num)
      rw [ble_true (Nat.zero_le _)] at hg
      unfold rgOK at hg
      simp only [bAnd_iff] at hg
      rw [← List.getD_eq_getElem _ #[] hj, conjArrs_get hj' hg.1]
      exact isInvA_of hg.2.2.2.2.1
    · obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.1 ht
      have hl : mainArrs.length = 5 := by simp [mainArrs, mainWords]
      obtain ⟨em, -, hp⟩ := main_ok (hl ▸ hi)
      rw [← List.getD_eq_getElem _ #[] hi, em]
      exact isInvA_of hp
    · obtain ⟨j, hj, rfl⟩ := repArrs_mem ht
      have h := allN_spec kSylowReps j hj
      simp only [bAnd_iff] at h
      rw [(rep_ok hj).1]
      exact isInvA_of h.2.1
  · obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.1 hws
    have hl : cent0Words.length = 5 := by simp [cent0Words]
    have h := List.all_eq_true.1 (allN_spec kCent i (hl ▸ hi)) w
      (by rwa [List.getD_eq_getElem _ [] hi])
    simp only [bAnd_iff] at h
    rw [omegaW_eq h.1]
    exact isInvA_of h.2.2.1
  · obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.1 hw
    have hl : fgWords.length = 2 := by simp [fgWords]
    have h := allN_spec kFg i (hl ▸ hi)
    simp only [bAnd_iff] at h
    rw [← List.getD_eq_getElem _ [] hi, omegaW_eq h.1]
    exact isInvA_of h.2.2.2.1

end CertificateChecks.KernelO8

end
