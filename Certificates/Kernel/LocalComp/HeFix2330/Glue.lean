module

public import Certificates.Kernel.LocalComp.HeFix2330.Chk
public import Certificates.Kernel.LocalComp.HeFixBind
public import Certificates.Kernel.Sporadic.OddCore.HeL2F
public import CFSG.Certificates.Kernel.MaxD2.Basic
public import CFSG.Certificates.Kernel.L34KSnd.Tab

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelLC.HeFix2330

open CFSG.KC.Enum CFSG.KS CFSG.KS.Prim CFSG.KS.Raw CFSG.KS.PEnum CFSG.KC.BfsPin
open CFSG.PSL3Four.Native CFSG.Monster.B.Co2.Native CFSG.Sporadic.SmallOddCore CFSG.Sporadic.HeldB
open CFSG.ComponentClassification.GrSLit.HeldFix CertificateChecks.KernelLC.HeFix
open CertificateChecks.KernelSpor

theorem hw {w : List Nat} (h : ∀ j ∈ w, j < 9) :
    hfCTab w = unpack 8330 14 (H w) ∧ cn (H w) = true :=
  ⟨CFSG.KC.PermTool.wordTabS_unpack hid hidA w (fun k hk => cnC1 (h k hk))
    (fun k hk => c1Tab_eq (h k hk)),
    CFSG.KC.PermTool.canonK_wordTabK hid w fun k hk => cnC1 (h k hk)⟩

theorem qparts : (∀ i < 2, permOK 8330 14 (mask 14) (8330 * 14) (H (hfQWords.getD i [])) (QI i) =
    true) ∧ (∀ j < 9, cn (CertificateChecks.KernelSporSch.HeB14.C1I j) = true) ∧
    Nat.beq (pc (pc (pc (H (hfQWords.getD 0 [])) (H (hfQWords.getD 1 []))) (QI 0)) (QI 1)) PT1 =
      true := by
  have h := kQ
  simp only [Bool.and_eq_true] at h
  exact ⟨fun i hi => allN_spec h.1.1 i hi, fun j hj => allN_spec h.1.2 j hj, h.2⟩

theorem qlt : ∀ i < 2, ∀ j ∈ hfQWords.getD i [], j < 9 := by decide

theorem cnQI {i : Nat} (hi : i < 2) : cn (QI i) = true :=
  CFSG.KC.PermTool.canonK_wordTabK hid _ fun j hj =>
    qparts.2.1 j (qlt i hi j (List.mem_reverse.1 hj))

theorem qinv {i : Nat} (hi : i < 2) :
    invCand 8330 (hfCTab (hfQWords.getD i [])) = unpack 8330 14 (QI i) ∧
      isInvA 8330 (hfCTab (hfQWords.getD i [])) (invCand 8330 (hfCTab (hfQWords.getD i []))) =
        true := by
  have e := invEqK_sound (qparts.1 i hi)
  rw [(hw (qlt i hi)).1, e.1]
  exact ⟨rfl, e.2⟩

theorem cmp {p q : Nat} (hp : cn p = true) (hq : cn q = true) :
    comp 8330 (unpack 8330 14 p) (unpack 8330 14 q) = unpack 8330 14 (pc p q) :=
  compA_unpack hp hq

theorem cnpc {p q : Nat} (hp : cn p = true) (hq : cn q = true) : cn (pc p q) = true :=
  canonK_pcomp hp hq

theorem hidT : idTab 8330 = unpack 8330 14 (pidn 8330 14) := by
  rw [CFSG.KC.PermTool.idTab_eq, hidA]

theorem ne_id {p : Nat} (hp : cn p = true) (h : Nat.beq p (pidn 8330 14) = false) :
    unpack 8330 14 p ≠ idTab 8330 := by
  intro e
  have b := CFSG.KC.L34KSnd.beq_unpack hp hid
  rw [← hidT, e, beq_self_eq_true] at b
  rw [← b] at h
  exact absurd h (by decide)

theorem oparts : (∀ i < 2, Nat.beq (H (hfRep 7 (hfOrd7Words.getD i []))) (pidn 8330 14) = true ∧
      Nat.beq (H (hfOrd7Words.getD i [])) (pidn 8330 14) = false) ∧
    (∀ i < 3, Nat.beq (H (hfRep 3 (hfOrd3Words.getD i []))) (pidn 8330 14) = true ∧
      Nat.beq (H (hfOrd3Words.getD i [])) (pidn 8330 14) = false) := by
  have h := kO
  simp only [Bool.and_eq_true] at h
  refine ⟨fun i hi => ?_, fun i hi => ?_⟩
  · have g := allN_spec h.1 i hi
    simp only [Bool.and_eq_true, Bool.not_eq_true'] at g
    exact g
  · have g := allN_spec h.2 i hi
    simp only [Bool.and_eq_true, Bool.not_eq_true'] at g
    exact g

theorem o7lt : ∀ i < 2, ∀ j ∈ hfOrd7Words.getD i [], j < 9 := by decide

theorem o3lt : ∀ i < 3, ∀ j ∈ hfOrd3Words.getD i [], j < 9 := by decide

theorem rep_lt {k : Nat} {w : List Nat} (h : ∀ j ∈ w, j < 9) : ∀ j ∈ hfRep k w, j < 9 := by
  intro j hj
  unfold hfRep at hj
  obtain ⟨l, hl, hjl⟩ := List.mem_flatten.1 hj
  rw [(List.eq_of_mem_replicate hl)] at hjl
  exact h j hjl

theorem hidT42 : idTab 42 = unpack 42 6 (pidn 42 6) := He2276.idTab_eq

theorem hx {w : List Nat} (h : ∀ j ∈ w, j < 9) :
    hfCTab42 w = unpack 42 6 (X w) ∧ canonK 42 6 (mask 6) (42 * 6) (X w) = true :=
  ⟨CFSG.KC.PermTool.wordTabS_unpack He2276.idc.1 hidT42 w (fun k hk => (He2276.x_get (h k hk)).2)
    (fun k hk => (He2276.x_get (h k hk)).1),
    CFSG.KC.PermTool.canonK_wordTabK He2276.idc.1 w fun k hk => (He2276.x_get (h k hk)).2⟩

theorem clt : ∀ i < 6, ∀ j ∈ hfCommWords.getD i [], j < 9 := by decide

theorem cparts {i : Nat} (hi : i < 6) :
    permOK 42 6 (mask 6) (42 * 6) (X (hfCommWords.getD i [])) (pi' (X (hfCommWords.getD i []))) =
      true ∧
    Nat.beq (pc' (pi' (X (hfCommWords.getD i []))) (X (hfCommWords.getD i []))) (pidn 42 6) =
      true := by
  have g := allN_spec kC i hi
  simp only [Bool.and_eq_true] at g
  exact g

theorem xinv {i : Nat} (hi : i < 6) :
    invTab 42 (hfCTab42 (hfCommWords.getD i [])) = unpack 42 6 (pi' (X (hfCommWords.getD i []))) ∧
      canonK 42 6 (mask 6) (42 * 6) (pi' (X (hfCommWords.getD i []))) = true := by
  rw [(hx (clt i hi)).1]
  exact ⟨CFSG.KS.MaxD2.inv_u (cparts hi).1,
    (CFSG.KS.MaxD2.perm_canon (cparts hi).1 (by decide)).2⟩

theorem cmp42 {p q : Nat} (hp : canonK 42 6 (mask 6) (42 * 6) p = true)
    (hq : canonK 42 6 (mask 6) (42 * 6) q = true) :
    comp 42 (unpack 42 6 p) (unpack 42 6 q) = unpack 42 6 (pc' p q) :=
  compA_unpack hp hq

theorem gparts : HCE.k = 3 ∧ HSE.k = 2 ∧ HTE.k = 3 ∧
    (∀ i < 3, HCE.G i = CG i ∧ canonK 42 6 (mask 6) (42 * 6) (HCE.G i) = true) ∧
    (∀ i < 2, HSE.G i = X (hfOrd7Words.getD i []) ∧
      canonK 42 6 (mask 6) (42 * 6) (HSE.G i) = true) ∧
    (∀ i < 3, HTE.G i = X (hfOrd3Words.getD i []) ∧
      canonK 42 6 (mask 6) (42 * 6) (HTE.G i) = true) := by
  have h := kG
  simp only [Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩ := h
  refine ⟨Nat.eq_of_beq_eq_true h1, Nat.eq_of_beq_eq_true h2, Nat.eq_of_beq_eq_true h3,
    fun i hi => ?_, fun i hi => ?_, fun i hi => ?_⟩
  · have g := allN_spec h4 i hi
    simp only [Bool.and_eq_true] at g
    exact ⟨Nat.eq_of_beq_eq_true g.1, g.2⟩
  · have g := allN_spec h5 i hi
    simp only [Bool.and_eq_true] at g
    exact ⟨Nat.eq_of_beq_eq_true g.1, g.2⟩
  · have g := allN_spec h6 i hi
    simp only [Bool.and_eq_true] at g
    exact ⟨Nat.eq_of_beq_eq_true g.1, g.2⟩

theorem gensC : GensOK 42 6 HCE.k HCE.G hfCommTabs42 := by
  refine ⟨by rw [gparts.1]; rfl, fun i hi => ?_⟩
  rw [gparts.1] at hi
  have h1 : 2 * i < 6 := by omega
  have h2 : 2 * i + 1 < 6 := by omega
  refine ⟨?_, (gparts.2.2.2.1 i hi).2⟩
  rw [(gparts.2.2.2.1 i hi).1, hfCommTabs42, ofFn_get _ hi]
  dsimp only
  unfold commTab
  have a := (hx (clt _ h1)).2
  have b := (hx (clt _ h2)).2
  have ab : canonK 42 6 (mask 6) (42 * 6) (pc' (X (hfCommWords.getD (2 * i) []))
      (X (hfCommWords.getD (2 * i + 1) []))) = true := canonK_pcomp a b
  have abc : canonK 42 6 (mask 6) (42 * 6) (pc' (pc' (X (hfCommWords.getD (2 * i) []))
      (X (hfCommWords.getD (2 * i + 1) []))) (pi' (X (hfCommWords.getD (2 * i) [])))) = true :=
    canonK_pcomp ab (xinv h1).2
  rw [(xinv h1).1, (xinv h2).1, (hx (clt _ h1)).1, (hx (clt _ h2)).1, cmp42 a b,
    cmp42 ab (xinv h1).2, cmp42 abc (xinv h2).2]
  rfl

theorem gensS : GensOK 42 6 HSE.k HSE.G hfOrd7Tabs42 := by
  refine ⟨by rw [gparts.2.1]; rfl, fun i hi => ?_⟩
  rw [gparts.2.1] at hi
  refine ⟨?_, (gparts.2.2.2.2.1 i hi).2⟩
  rw [(gparts.2.2.2.2.1 i hi).1, hfOrd7Tabs42, ofFn_get _ hi]
  exact (hx (o7lt i hi)).1

theorem gensT : GensOK 42 6 HTE.k HTE.G hfOrd3Tabs42 := by
  refine ⟨by rw [gparts.2.2.1]; rfl, fun i hi => ?_⟩
  rw [gparts.2.2.1] at hi
  refine ⟨?_, (gparts.2.2.2.2.2 i hi).2⟩
  rw [(gparts.2.2.2.2.2 i hi).1, hfOrd3Tabs42, ofFn_get _ hi]
  exact (hx (o3lt i hi)).1

theorem hd : penumHdK (pidn 42 6) HCE.cnt 10752 HCE.T HCE.PL = true ∧
    penumHdK (pidn 42 6) HSE.cnt 10752 HSE.T HSE.PL = true ∧
    penumHdK (pidn 42 6) HTE.cnt 10752 HTE.T HTE.PL = true ∧
    HCE.cnt = 10752 ∧ HSE.cnt = 10752 ∧ HTE.cnt = 10752 := by
  have h := kHd
  simp only [Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩ := h
  exact ⟨h1, h2, h3, Nat.eq_of_beq_eq_true h4, Nat.eq_of_beq_eq_true h5, Nat.eq_of_beq_eq_true h6⟩

theorem enumC : enumOK 42 hfCommTabs42 hfCommEnum42 = true ∧ hfCommEnum42.tabs.size = 10752 := by
  have hp : ∀ i < HCE.cnt, penumPtK 42 6 (mask 6) (42 * 6) false HCE.G HCE.GI HCE.k HCE.cnt
      HCE.T HCE.PL HCE.POS HCE.SRT HCE.SRI i = true := by
    intro i hi
    have e := hd.2.2.2.1
    rcases Nat.lt_or_ge i 2688 with h0 | h0
    · exact penumSl_spec c_sl0 i (Nat.zero_le _) (by omega) hi
    rcases Nat.lt_or_ge i 5376 with h1 | h1
    · exact penumSl_spec c_sl1 i h0 (by omega) hi
    rcases Nat.lt_or_ge i 8064 with h2 | h2
    · exact penumSl_spec c_sl2 i h1 (by omega) hi
    · exact penumSl_spec c_sl3 i h2 (by omega) (by omega)
  have s := penumK_left_sound (cap := 10752) (by decide) gensC hd.1 hp
  unfold hfCommEnum42
  rw [s.1]
  exact ⟨s.2, by simp [penumRec, hd.2.2.2.1]⟩

theorem enumS : enumOK 42 hfOrd7Tabs42 hfOrd7Enum42 = true ∧ hfOrd7Enum42.tabs.size = 10752 := by
  have hp : ∀ i < HSE.cnt, penumPtK 42 6 (mask 6) (42 * 6) false HSE.G HSE.GI HSE.k HSE.cnt
      HSE.T HSE.PL HSE.POS HSE.SRT HSE.SRI i = true := by
    intro i hi
    have e := hd.2.2.2.2.1
    rcases Nat.lt_or_ge i 2688 with h0 | h0
    · exact penumSl_spec s_sl0 i (Nat.zero_le _) (by omega) hi
    rcases Nat.lt_or_ge i 5376 with h1 | h1
    · exact penumSl_spec s_sl1 i h0 (by omega) hi
    rcases Nat.lt_or_ge i 8064 with h2 | h2
    · exact penumSl_spec s_sl2 i h1 (by omega) hi
    · exact penumSl_spec s_sl3 i h2 (by omega) (by omega)
  have s := penumK_left_sound (cap := 10752) (by decide) gensS hd.2.1 hp
  unfold hfOrd7Enum42
  rw [s.1]
  exact ⟨s.2, by simp [penumRec, hd.2.2.2.2.1]⟩

theorem enumT : enumOK 42 hfOrd3Tabs42 hfOrd3Enum42 = true ∧ hfOrd3Enum42.tabs.size = 10752 := by
  have hp : ∀ i < HTE.cnt, penumPtK 42 6 (mask 6) (42 * 6) false HTE.G HTE.GI HTE.k HTE.cnt
      HTE.T HTE.PL HTE.POS HTE.SRT HTE.SRI i = true := by
    intro i hi
    have e := hd.2.2.2.2.2
    rcases Nat.lt_or_ge i 2688 with h0 | h0
    · exact penumSl_spec t_sl0 i (Nat.zero_le _) (by omega) hi
    rcases Nat.lt_or_ge i 5376 with h1 | h1
    · exact penumSl_spec t_sl1 i h0 (by omega) hi
    rcases Nat.lt_or_ge i 8064 with h2 | h2
    · exact penumSl_spec t_sl2 i h1 (by omega) hi
    · exact penumSl_spec t_sl3 i h2 (by omega) (by omega)
  have s := penumK_left_sound (cap := 10752) (by decide) gensT hd.2.2.1 hp
  unfold hfOrd3Enum42
  rw [s.1]
  exact ⟨s.2, by simp [penumRec, hd.2.2.2.2.2]⟩

theorem check :
    (∀ i < 2, ∀ j ∈ hfQWords.getD i [], j < 9) ∧ (∀ i < 6, ∀ j ∈ hfCommWords.getD i [], j < 9) ∧
      (∀ i < 2, ∀ j ∈ hfOrd7Words.getD i [], j < 9) ∧
      (∀ i < 3, ∀ j ∈ hfOrd3Words.getD i [], j < 9) ∧
      isInvA 8330 (hfCTab (hfQWords.getD 0 [])) (invCand 8330 (hfCTab (hfQWords.getD 0 []))) =
        true ∧
      isInvA 8330 (hfCTab (hfQWords.getD 1 [])) (invCand 8330 (hfCTab (hfQWords.getD 1 []))) =
        true ∧
      comp 8330 (comp 8330 (comp 8330 (hfCTab (hfQWords.getD 0 [])) (hfCTab (hfQWords.getD 1 [])))
        (invCand 8330 (hfCTab (hfQWords.getD 0 [])))) (invCand 8330 (hfCTab (hfQWords.getD 1 []))) =
        heT1Arr ∧
      (∀ i < 2, hfCTab (hfRep 7 (hfOrd7Words.getD i [])) = idTab 8330 ∧
        hfCTab (hfOrd7Words.getD i []) ≠ idTab 8330) ∧
      (∀ i < 3, hfCTab (hfRep 3 (hfOrd3Words.getD i [])) = idTab 8330 ∧
        hfCTab (hfOrd3Words.getD i []) ≠ idTab 8330) ∧
      (∀ i < 6, comp 42 (invTab 42 (hfCTab42 (hfCommWords.getD i [])))
        (hfCTab42 (hfCommWords.getD i [])) = idTab 42 ∧
        (invTab 42 (hfCTab42 (hfCommWords.getD i []))).size = 42) ∧
      enumOK 42 hfCommTabs42 hfCommEnum42 = true ∧ hfCommEnum42.tabs.size = 10752 ∧
      enumOK 42 hfOrd7Tabs42 hfOrd7Enum42 = true ∧ hfOrd7Enum42.tabs.size = 10752 ∧
      enumOK 42 hfOrd3Tabs42 hfOrd3Enum42 = true ∧ hfOrd3Enum42.tabs.size = 10752 := by
  have q0 := hw (qlt 0 (by decide))
  have q1 := hw (qlt 1 (by decide))
  refine ⟨qlt, clt, o7lt, o3lt, (qinv (i := 0) (by decide)).2, (qinv (i := 1) (by decide)).2, ?_,
    fun i hi => ?_, fun i hi => ?_, fun i hi => ?_, enumC.1, enumC.2, enumS.1, enumS.2, enumT.1,
    enumT.2⟩
  · rw [(qinv (i := 0) (by decide)).1, (qinv (i := 1) (by decide)).1, q0.1, q1.1, heT1_eq,
      cmp q0.2 q1.2, cmp (cnpc q0.2 q1.2) (cnQI (i := 0) (by decide)),
      cmp (cnpc (cnpc q0.2 q1.2) (cnQI (i := 0) (by decide))) (cnQI (i := 1) (by decide)),
      Nat.eq_of_beq_eq_true qparts.2.2]
  · have hr := hw (rep_lt (k := 7) (o7lt i hi))
    have h1 := hw (o7lt i hi)
    refine ⟨?_, ?_⟩
    · rw [hr.1, hidT, Nat.eq_of_beq_eq_true (oparts.1 i hi).1]
    · rw [h1.1]
      exact ne_id h1.2 (oparts.1 i hi).2
  · have hr := hw (rep_lt (k := 3) (o3lt i hi))
    have h1 := hw (o3lt i hi)
    refine ⟨?_, ?_⟩
    · rw [hr.1, hidT, Nat.eq_of_beq_eq_true (oparts.2 i hi).1]
    · rw [h1.1]
      exact ne_id h1.2 (oparts.2 i hi).2
  · refine ⟨?_, ?_⟩
    · rw [(xinv hi).1, (hx (clt i hi)).1, cmp42 (xinv hi).2 (hx (clt i hi)).2, hidT42,
        Nat.eq_of_beq_eq_true (cparts hi).2]
    · rw [(xinv hi).1]
      exact CFSG.KS.MaxD2.size_u _

end CertificateChecks.KernelLC.HeFix2330

end
