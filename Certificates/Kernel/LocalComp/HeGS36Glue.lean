module

public import Certificates.Kernel.LocalComp.HeGS36
public import Certificates.Kernel.LocalComp.HeFixBind
public import Certificates.Kernel.SporSch.HeT.B2114
public import CFSG.Certificates.Kernel.L34KSnd.Tab

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelLC.HeGS36

open CFSG.KC.Enum CFSG.KS CFSG.KS.Prim CFSG.KS.Raw CFSG.KC.BfsPin CFSG.KC.PermTool CFSG.PSL3Four.Native
open CFSG.Monster.B.Co2.Native CFSG.Sporadic.HeldB CFSG.Sporadic.SmallOddCore
open CFSG.ComponentClassification.GrSLit.HeldFix CFSG.ComponentClassification.GrSLit.HeGS
open CertificateChecks.KernelLC.HeFix

theorem parts : (∀ j < 9, cn (CertificateChecks.KernelSporSch.HeB14.C0 j) = true) ∧
    cn G1I = true ∧ cn cT = true ∧ cn cI = true ∧ cn gT = true ∧ cn gI = true := by
  have h := kCanon
  simp only [Bool.and_eq_true] at h
  exact ⟨fun j hj => allN_spec h.1.1.1.1.1 j hj, h.1.1.1.1.2, h.1.1.1.2, h.1.1.2, h.1.2, h.2⟩

theorem cparts : Nat.beq (pc cT (K (heDWords.getD 1 []))) (pc PT1 cT) = true ∧
    permOK 8330 14 (mask 14) (8330 * 14) cT cI = true ∧
    permOK 8330 14 (mask 14) (8330 * 14) cI cT = true ∧
    permOK 8330 14 (mask 14) (8330 * 14) gT gI = true := by
  have h := kC
  simp only [Bool.and_eq_true] at h
  exact ⟨h.1.1.1.1, h.1.1.1.2, h.1.1.2, h.1.2⟩

theorem cmp {p q : Nat} (hp : cn p = true) (hq : cn q = true) :
    comp 8330 (unpack 8330 14 p) (unpack 8330 14 q) = unpack 8330 14 (pc p q) :=
  compA_unpack hp hq

theorem cnpc {p q : Nat} (hp : cn p = true) (hq : cn q = true) : cn (pc p q) = true :=
  canonK_pcomp hp hq

theorem cnG : cn (HG.F 0) = true ∧ cn (HG.F 1) = true := by
  have h := kCanonG
  simp only [Bool.and_eq_true] at h
  exact ⟨h.1.1, h.1.2⟩

theorem a1i : invCand 8330 (heGen 1) = unpack 8330 14 G1I := by
  have h := allN_spec kPL2 1 (by decide)
  simp only [L2, L2I, List.getD_cons_succ, List.getD_cons_zero] at h
  rw [heGen_eq (by decide)]
  exact (invEqK_sound h).1

theorem kw {w : List Nat} (hw : ∀ j ∈ w, j < 9) :
    heGSKTab w = unpack 8330 14 (K w) ∧ cn (K w) = true := by
  refine ⟨wordTabS_unpack hid hidA w (fun k hk => parts.1 k (hw k hk)) (fun k hk => ?_),
    canonK_wordTabK hid w fun k hk => parts.1 k (hw k hk)⟩
  rw [heGSC0Tabs, ofFn_get _ (hw k hk)]
  exact (CertificateChecks.KernelSporSch.HeB14.C0_word (hw k hk)).1

theorem hw {w : List Nat} (hw : ∀ j ∈ w, j < 9) : hfCTab w = unpack 8330 14 (H w) :=
  wordTabS_unpack hid hidA w (fun k hk => cnC1 (hw k hk)) (fun k hk => c1Tab_eq (hw k hk))

theorem pow_eq {p : Nat} (hp : cn p = true) :
    ∀ e, heGS36Pow (unpack 8330 14 p) e = unpack 8330 14 (powK 8330 14 p e)
  | 0 => by rw [heGS36Pow, idTab_eq, hidA]; rfl
  | e + 1 => by
    rw [heGS36Pow, pow_eq hp e, cmp hp (canonK_powK hid hp e)]
    rfl

theorem kd1 : heGSKTab (heDWords.getD 1 []) = unpack 8330 14 (K (heDWords.getD 1 [])) ∧
    cn (K (heDWords.getD 1 [])) = true := kw (by decide)

theorem cTab : heGS36CTab = unpack 8330 14 cT := by
  have c1 := cnpc cnG.2 kd1.2
  have c2 := cnpc c1 parts.2.1
  have c3 := cnpc c2 cnW.1
  unfold heGS36CTab
  rw [a1i, heGen_eq (by decide), kd1.1, heT1_eq, cmp cnG.2 kd1.2, cmp c1 parts.2.1,
    cmp c2 cnW.1, pow_eq c3, cmp (canonK_powK hid c3 8) cnG.2]
  rfl

theorem cInv : invCand 8330 heGS36CTab = unpack 8330 14 cI := by
  rw [cTab]
  exact (invEqK_sound cparts.2.1).1

theorem w1Tab : heGS36W1Tab = unpack 8330 14 w1 := by
  unfold heGS36W1Tab
  rw [cInv, cTab, heGen_eq (by decide), cmp parts.2.2.1 cnG.1,
    cmp (cnpc parts.2.2.1 cnG.1) parts.2.2.2.1]
  rfl

theorem cnw1 : cn w1 = true := cnpc (cnpc parts.2.2.1 cnG.1) parts.2.2.2.1

theorem tgt_eq {p : Nat} (hp : p < 4) : heGS36Target p = unpack 8330 14 (tgt p) := by
  unfold heGS36Target tgt
  cases hb : Nat.beq (p % 2) 0
  · rw [if_neg (Nat.ne_of_beq_eq_false hb)]
    unfold heGS36W2Tab
    rw [w1Tab, heT1_eq, cmp cnw1 cnW.1]
  · rw [if_pos (Nat.eq_of_beq_eq_true hb), w1Tab]

theorem g36tgt_eq (p : Nat) : g36tgt p = tgt p := by
  unfold g36tgt tgt g36w1 w1 cI
  simp only [g36cT_eq, g36pc_eq]

theorem lt9 {p : Nat} (hp : p < 4) : (∀ j ∈ heGS36D p 0 ++ heGS36D p 1, j < 9) ∧
    (∀ j ∈ heGS36D p 2 ++ heGS36D p 3, j < 9) ∧ ∀ j ∈ heGS36Word p, j < 9 := by
  interval_cases p <;> decide

theorem cnH {w : List Nat} (hw : ∀ j ∈ w, j < 9) : cn (H w) = true :=
  canonK_wordTabK hid w fun k hk => cnC1 (hw k hk)

theorem lt9X : ∀ j ∈ heGSXWord, j < 9 := by decide

theorem lt9_app {u v : List Nat} (hu : ∀ j ∈ u, j < 9) (hv : ∀ j ∈ v, j < 9) :
    ∀ j ∈ u ++ v, j < 9 := fun j hj => (List.mem_append.1 hj).elim (hu j) (hv j)

theorem lt9_rep (k : Nat) : ∀ j ∈ hfRep k heGSXWord, j < 9 := fun j hj => by
  simp only [hfRep, List.mem_flatten, List.mem_replicate] at hj
  obtain ⟨l, ⟨-, rfl⟩, hl⟩ := hj
  exact lt9X j hl

theorem pc_idL {q : Nat} (hq : cn q = true) : pc (pidn 8330 14) q = q := by
  unfold pc
  exact CFSG.KC.L34KSnd.eq_of_pg (cnpc hid hq) hq fun i hi => by
    rw [CFSG.KC.L34KSnd.pg_pcomp' hid hi,
      CFSG.KC.L34KSnd.pg_pidn' (CFSG.KC.L34KSnd.canon_sz hid) (CFSG.KC.L34KSnd.canon_lt hq hi)]

theorem H_append : ∀ u v : List Nat, (∀ j ∈ u, j < 9) → (∀ j ∈ v, j < 9) →
    H (u ++ v) = pc (H u) (H v)
  | [], _, _, hv => (pc_idL (cnH hv)).symm
  | j :: u, v, hu, hv => by
    have hu' : ∀ k ∈ u, k < 9 := fun k hk => hu k (List.mem_cons_of_mem j hk)
    change pc (PC1 j) (H (u ++ v)) = pc (pc (PC1 j) (H u)) (H v)
    rw [H_append u v hu' hv]
    exact (CFSG.KC.L34KSnd.pcomp_assoc' (cnC1 (hu j List.mem_cons_self)) (cnH hu') (cnH hv)).symm

theorem H_cancel {w : List Nat} (u r v : List Nat) (hr : H r = pidn 8330 14)
    (hb : (∀ j ∈ u, j < 9) ∧ (∀ j ∈ r, j < 9) ∧ ∀ j ∈ v, j < 9) (e : w = u ++ (r ++ v)) :
    H w = H (u ++ v) := by
  obtain ⟨hu, hrr, hv⟩ := hb
  have hrv : ∀ j ∈ r ++ v, j < 9 := fun j hj => (List.mem_append.1 hj).elim (hrr j) (hv j)
  rw [e, H_append u (r ++ v) hu hrv, H_append r v hrr hv, hr, pc_idL (cnH hv),
    ← H_append u v hu hv]

theorem pairs_id {p : Nat} (hp : p < 4) : H (heGS36D p 0 ++ heGS36D p 1) = pidn 8330 14 ∧
    H (heGS36D p 2 ++ heGS36D p 3) = pidn 8330 14 := by
  have h := g36Rel
  simp only [Bool.and_eq_true] at h
  have r1 := Nat.eq_of_beq_eq_true h.1.1.1
  have r2 := Nat.eq_of_beq_eq_true h.1.1.2
  have r3 := Nat.eq_of_beq_eq_true h.1.2
  have r8 := Nat.eq_of_beq_eq_true h.2
  have hz : H ([] ++ []) = pidn 8330 14 := rfl
  have a0 : H (heGS36D 0 0 ++ heGS36D 0 1) = pidn 8330 14 :=
    Eq.trans (H_cancel [8, 2] [1, 1] [2, 8, 8, 8, 8, 8] r1 (by decide) (by decide)) <|
    Eq.trans (H_cancel [8] [2, 2] [8, 8, 8, 8, 8] r2 (by decide) (by decide)) <|
    Eq.trans (H_cancel [] [8, 8, 8, 8, 8, 8] [] r8 (by decide) (by decide)) hz
  interval_cases p
  · refine ⟨a0, ?_⟩
    exact Eq.trans (H_cancel [1, 8, 3] [8, 8, 8, 8, 8, 8] [3, 8, 8, 8, 8, 8, 1] r8 (by decide)
        (by decide)) <|
      Eq.trans (H_cancel [1, 8] [3, 3] [8, 8, 8, 8, 8, 1] r3 (by decide) (by decide)) <|
      Eq.trans (H_cancel [1] [8, 8, 8, 8, 8, 8] [1] r8 (by decide) (by decide)) <|
      Eq.trans (H_cancel [] [1, 1] [] r1 (by decide) (by decide)) hz
  · refine ⟨Eq.trans (H_cancel [] [8, 8, 8, 8, 8, 8] [] r8 (by decide) (by decide)) hz, ?_⟩
    exact Eq.trans (H_cancel [3] [8, 8, 8, 8, 8, 8] [3] r8 (by decide) (by decide)) <|
      Eq.trans (H_cancel [] [3, 3] [] r3 (by decide) (by decide)) hz
  · refine ⟨Eq.trans (H_cancel [8, 3] [2, 2] [3, 8, 8, 8, 8, 8] r2 (by decide) (by decide)) <|
      Eq.trans (H_cancel [8] [3, 3] [8, 8, 8, 8, 8] r3 (by decide) (by decide)) <|
      Eq.trans (H_cancel [] [8, 8, 8, 8, 8, 8] [] r8 (by decide) (by decide)) hz, ?_⟩
    exact Eq.trans (H_cancel [8, 1] [8, 8, 8, 8, 8, 8] [8, 8, 8, 8, 8, 8, 1, 8, 8, 8, 8, 8] r8
        (by decide) (by decide)) <|
      Eq.trans (H_cancel [8, 1] [8, 8, 8, 8, 8, 8] [1, 8, 8, 8, 8, 8] r8 (by decide) (by decide)) <|
      Eq.trans (H_cancel [8] [1, 1] [8, 8, 8, 8, 8] r1 (by decide) (by decide)) <|
      Eq.trans (H_cancel [] [8, 8, 8, 8, 8, 8] [] r8 (by decide) (by decide)) hz
  · refine ⟨a0, ?_⟩
    exact Eq.trans (H_cancel [8, 1] [2, 2] [1, 8, 8, 8, 8, 8] r2 (by decide) (by decide)) <|
      Eq.trans (H_cancel [8] [1, 1] [8, 8, 8, 8, 8] r1 (by decide) (by decide)) <|
      Eq.trans (H_cancel [] [8, 8, 8, 8, 8, 8] [] r8 (by decide) (by decide)) hz

theorem H_rep : ∀ k : Nat, H (hfRep k heGSXWord) = powK 8330 14 (H heGSXWord) k
  | 0 => rfl
  | k + 1 => by
    have e : hfRep (k + 1) heGSXWord = heGSXWord ++ hfRep k heGSXWord := by
      simp only [hfRep, List.replicate_succ, List.flatten_cons]
    rw [e, H_append _ _ lt9X (lt9_rep k), H_rep k]
    rfl

theorem kG_all {p : Nat} (hp : p < 4) : H (heGS36Word p) = tgt p := by
  have h : g36F p = true := by
    interval_cases p
    exacts [kG0, kG1, kG2, kG3]
  have hb : (∀ j ∈ heGS36D p 0, j < 9) ∧ (∀ j ∈ heGS36D p 1, j < 9) ∧
      (∀ j ∈ heGS36D p 2, j < 9) ∧ ∀ j ∈ heGS36D p 3, j < 9 := by
    interval_cases p <;> decide
  obtain ⟨h0, h1, h2, h3⟩ := hb
  have hR := lt9_rep (3 + p / 2)
  unfold g36F at h
  simp only [g36pc_eq, g36w_eq, g36pow_eq, g36tgt_eq] at h
  rw [← Nat.eq_of_beq_eq_true h]
  unfold heGS36Word
  simp only [List.append_assoc]
  rw [H_append _ _ h0 (lt9_app hR (lt9_app h1 (lt9_app h2 (lt9_app hR h3)))),
    H_append _ _ hR (lt9_app h1 (lt9_app h2 (lt9_app hR h3))),
    H_append _ _ h1 (lt9_app h2 (lt9_app hR h3)), H_append _ _ h2 (lt9_app hR h3),
    H_append _ _ hR h3, H_rep]
  rfl

theorem gTab : heGSGTab = unpack 8330 14 gT := by
  have kv := kw (w := heGSVWord) (by decide)
  have c1 := cnpc parts.2.1 cnG.1
  have c2 := cnpc c1 cnG.2
  have c3 := cnpc c2 kv.2
  unfold heGSGTab heGSVTab
  dsimp only
  rw [a1i, heGen_eq (by decide), heGen_eq (by decide), kv.1, cmp parts.2.1 cnG.1, cmp c1 cnG.2,
    cmp c2 kv.2, cmp c3 c3, cmp (cnpc c3 c3) parts.2.1]
  rfl

theorem i5Tab : heGSInit[5]!.1 = unpack 8330 14 i5 := by
  have k0 := kw (w := heDWords.getD 0 []) (by decide)
  have e : heGSInit[5]!.1 = comp 8330 (comp 8330 heGSGTab (heGSKTab (heDWords.getD 0 [])))
      (invCand 8330 heGSGTab) := by
    rw [heGSInit, ofFn_get _ (by decide)]
    rfl
  rw [e, gTab, (invEqK_sound cparts.2.2.2).1, k0.1, cmp parts.2.2.2.2.1 k0.2,
    cmp (cnpc parts.2.2.2.2.1 k0.2) parts.2.2.2.2.2]
  rfl

theorem cni5 : cn i5 = true :=
  cnpc (cnpc parts.2.2.2.2.1 (kw (w := heDWords.getD 0 []) (by decide)).2) parts.2.2.2.2.2

theorem check :
    comp 8330 heGS36CTab (heGSKTab (heDWords.getD 1 [])) = comp 8330 heT1Arr heGS36CTab ∧
      permChk 8330 heGS36CTab = true ∧
      (∀ p < 4, hfCTab (heGS36D p 0 ++ heGS36D p 1) = idTab 8330 ∧
        hfCTab (heGS36D p 2 ++ heGS36D p 3) = idTab 8330 ∧
        hfCTab (heGS36Word p) = heGS36Target p) ∧
      comp 8330 (heGSKTab (heDWords.getD 1 [])) heGSInit[5]!.1 ≠
        comp 8330 heGSInit[5]!.1 (heGSKTab (heDWords.getD 1 [])) ∧
      comp 8330 (heGSKTab (heGSComm2 heGSUComm)) (heGSKTab (heGSComm2 heGSUComm)) =
        idTab 8330 := by
  have hE := kE
  simp only [Bool.and_eq_true, Bool.not_eq_true'] at hE
  have hidT : idTab 8330 = unpack 8330 14 (pidn 8330 14) := by rw [idTab_eq, hidA]
  refine ⟨?_, ?_, fun p hp => ?_, ?_, ?_⟩
  · rw [cTab, kd1.1, heT1_eq, cmp parts.2.2.1 kd1.2, cmp cnW.1 parts.2.2.1,
      Nat.eq_of_beq_eq_true cparts.1]
  · exact CertificateChecks.KernelSporSch.HePt.perm_of cTab cparts.2.1 cparts.2.2.1
  · obtain ⟨l1, l2, l3⟩ := lt9 hp
    obtain ⟨e1, e2⟩ := pairs_id hp
    rw [hw l1, hw l2, hw l3, tgt_eq hp, hidT, e1, e2, kG_all hp]
    exact ⟨rfl, rfl, rfl⟩
  · rw [i5Tab, kd1.1, cmp kd1.2 cni5, cmp cni5 kd1.2]
    intro h
    have e := CFSG.KC.L34KSnd.beq_unpack (cnpc kd1.2 cni5) (cnpc cni5 kd1.2)
    rw [h, beq_self_eq_true] at e
    rw [← e] at hE
    exact absurd hE.1 (by decide)
  · have kc := kw (w := heGSComm2 heGSUComm) (by decide)
    rw [kc.1, cmp kc.2 kc.2, Nat.eq_of_beq_eq_true hE.2, hidT]

end CertificateChecks.KernelLC.HeGS36

end
