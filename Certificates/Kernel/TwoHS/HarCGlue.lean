module

public import Certificates.Kernel.TwoHS.HarCEP
public import Certificates.Kernel.TwoHS.HarCEV
public import Certificates.Kernel.TwoHS.HarCE3
public import Certificates.Kernel.TwoHS.HarCE4
public import Certificates.Kernel.TwoHS.HarCE5
public import Certificates.Kernel.TwoHS.HarCE6
public import Certificates.Kernel.TwoHS.HarCE7
public import Certificates.Kernel.TwoHS.HarCE8
public import Certificates.Kernel.TwoHS.HarCE9
public import Certificates.Kernel.TwoHS.HarCK2
public import Certificates.Kernel.TwoHS.HYOpsGlue
public import Certificates.Kernel.Sporadic.OddCore.PEnumGlue
public import CFSG.Certificates.Kernel.Common.ForallChunks
public import CFSG.Certificates.Kernel.Spor.PEnumBSound
public import CFSG.Certificates.Kernel.Spor.HKeyUSound
public import CFSG.Certificates.Kernel.Spor.MulHFSound
public import CFSG.Certificates.Kernel.Spor.PEnumCSound
public import CFSG.Certificates.Kernel.Spor.MulHQISound
public import CFSG.Certificates.Kernel.Spor.MulHNSound
public import CFSG.Certificates.Kernel.Spor.MulHPcSound
import CFSG.Certificates.Kernel.Spor.PcompFacts
public import CFSG.Certificates.Kernel.Misc.RuInvHash
public import CFSG.Certificates.Kernel.Spor.ClassOneH
public import CFSG.Certificates.Kernel.Spor.PackFld
public import CFSG.Certificates.Kernel.Spor.RawOrbGrp

public section

set_option maxRecDepth 400000

namespace CFSG.KD.TwoHS

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KS.PEnum CFSG.KS.MulH
open CFSG.EvenSporadicStandard.TwoHS CFSG.Sporadic.Th.Native CFSG.Sporadic.SmallOddCore
open CFSG.Sporadic.Schreier.Native CFSG.Sporadic.SmallOddCore.Native

#kc_forall_chunks ch7291pe_all (fun k => ch7291pe k = true) 8 CFSG.KD.TwoHS.ch7291pe 1
#kc_forall_chunks ch7291hv_all (fun k => ch7291hv k = true) 16 CFSG.KD.TwoHS.ch7291hv 1
#kc_forall_chunks clPE_all (fun k => clPE k = true) 6 CFSG.KD.TwoHS.clPE 1
#kc_forall_chunks ntE5_all (fun k => ntE5 k = true) 2 CFSG.KD.TwoHS.ntE5 1
#kc_forall_chunks ntE6_all (fun k => ntE6 k = true) 4 CFSG.KD.TwoHS.ntE6 1
#kc_forall_chunks ntE7_all (fun k => ntE7 k = true) 8 CFSG.KD.TwoHS.ntE7 1
#kc_forall_chunks ntE8_all (fun k => ntE8 k = true) 16 CFSG.KD.TwoHS.ntE8 1
#kc_forall_chunks ntE9_all (fun k => ntE9 k = true) 32 CFSG.KD.TwoHS.ntE9 1
#kc_forall_chunks ntQ5_all (fun k => ntQ5 k = true) 2 CFSG.KD.TwoHS.ntQ5 1
#kc_forall_chunks ntQ6_all (fun k => ntQ6 k = true) 4 CFSG.KD.TwoHS.ntQ6 1
#kc_forall_chunks c3S_all (fun k => c3S k = true) 8 CFSG.KD.TwoHS.c3S 1
#kc_forall_chunks peQ_all (fun k => peQ k = true) 2 CFSG.KD.TwoHS.peQ 1
#kc_forall_chunks hsQF_all (fun k => ch7291hsF k = true) 2 CFSG.KD.TwoHS.ch7291hsF 1
#kc_forall_chunks clPQ_all (fun k => clPQ k = true) 2 CFSG.KD.TwoHS.clPQ 1
#kc_forall_chunks nqQ_all (fun k => nqQ k = true) 2 CFSG.KD.TwoHS.nqQ 1

theorem bIf_ft (c : Bool) : bIf(c, false, true) = !c := by cases c <;> rfl

theorem invYK_parts {c : Nat → Bool} {e f : Nat → Nat → Bool}
    (hf : f = fun p r => bAnd(c p, bAnd(c r, e p r))) {p r : Nat} (h : f p r = true) :
    c p = true ∧ c r = true ∧ e p r = true := by
  subst hf
  obtain ⟨hp, h'⟩ := (bAnd_iff _ _).1 h
  exact ⟨hp, (bAnd_iff _ _).1 h'⟩

theorem invYK_spec {p r : Nat} (h : invYK p r = true) :
    Cn p ∧ Cn r ∧ invEqK 11200 14 (mask 14) (11200 * 14) p r = true :=
  invYK_parts (c := cnK) (e := invEqK 11200 14 (mask 14) (11200 * 14)) harC_invU h

theorem base_parts :
    (∀ j < 3, TE.GI j = UL (j + 1) ∧ TE.G j = idK ∧ invYK (TE.GI j) (TEI j) = true) ∧
    TE.cnt = 1024 ∧ penumHdK idK TE.cnt 2000 TE.T TE.PL = true ∧
    (∀ j < 6, TQ.GI j = QK j ∧ TQ.G j = idK ∧ invYK (TQ.GI j) (TQI j) = true) ∧
    TQ.cnt = 128 ∧ penumHdK idK TQ.cnt 400 TQ.T TQ.PL = true ∧
    (∀ j < 5, TCG j = CGK j ∧ invYK (TCG j) (TCGI j) = true) ∧
    r32 TQR 0 < TQ.cnt ∧ TQ.T (r32 TQR 0) = UK harCRoot ∧
    Nat.beq (pc (UK harCRoot) (UK harCRoot)) Z1K = true ∧
    Nat.beq (pc (pc G3K G3K) G3K) idK = true ∧ bIf(Nat.beq G3K idK, false, true) = true ∧
    Nat.beq (pc (pc (pc (pc G5K G5K) G5K) G5K) G5K) idK = true ∧
    bIf(Nat.beq G5K idK, false, true) = true ∧
    Nat.beq (pc G3K Z1K) (pc Z1K G3K) = true ∧ Nat.beq (pc G5K Z1K) (pc Z1K G5K) = true ∧
    Nat.beq (pc CK Z1K) (pc Z1K CK) = true ∧ invYK CK CKI = true ∧ cnK Z1K = true ∧
    cnK C0K = true := by
  have h := harC_base
  simp only [bAnd_iff] at h
  obtain ⟨a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15, a16, a17, a18, a19,
    a20⟩ := h
  refine ⟨fun j hj => ?_, Nat.eq_of_beq_eq_true a2, a3, fun j hj => ?_, Nat.eq_of_beq_eq_true a5,
    a6, fun j hj => ?_, Nat.le_of_ble_eq_true a8, Nat.eq_of_beq_eq_true a9, a10, a11, a12, a13, a14,
    a15, a16, a17, a18, a19, a20⟩
  · have := allN_spec a1 j hj
    simp only [bAnd_iff] at this
    exact ⟨Nat.eq_of_beq_eq_true this.1, Nat.eq_of_beq_eq_true this.2.1, this.2.2⟩
  · have := allN_spec a4 j hj
    simp only [bAnd_iff] at this
    exact ⟨Nat.eq_of_beq_eq_true this.1, Nat.eq_of_beq_eq_true this.2.1, this.2.2⟩
  · have := allN_spec a7 j hj
    simp only [bAnd_iff] at this
    exact ⟨Nat.eq_of_beq_eq_true this.1, this.2⟩

theorem g3_eq : harCG3 () = tabT (unpack 11200 14 G3K) ∧ Cn G3K := wordTbl_eq (wd := harCW3) (by decide)

theorem g5_eq : harCG5 () = tabT (unpack 11200 14 G5K) ∧ Cn G5K := wordTbl_eq (wd := harCW5) (by decide)

theorem c_eq : harCGW () = tabT (unpack 11200 14 CK) ∧ Cn CK := wordTbl_eq (wd := harCWit) (by decide)

theorem cI_eq : invT 11200 (harCGW ()) = tabT (unpack 11200 14 CKI) ∧ Cn CKI := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hci, -, -⟩ := base_parts
  obtain ⟨-, c2, c3⟩ := invYK_spec hci
  rw [c_eq.1]
  exact ⟨invT_eq c3, c2⟩

theorem z1_eq : harZ1 = tabT (unpack 11200 14 Z1K) ∧ Cn Z1K := tU_eq (wd := [3, 3, 3, 3]) (by decide)

theorem c0_eq : harC0 = tabT (unpack 11200 14 C0K) ∧ Cn C0K :=
  tU_eq (wd := [1, 2, 1, 2, 3, 1, 2, 1, 2, 3]) (by decide)

theorem z2_eq : harZ2 = tabT (unpack 11200 14 Z2K) ∧ Cn Z2K := by
  unfold harZ2 Z2K
  rw [c0_eq.1, z1_eq.1, comp_eq c0_eq.2 z1_eq.2]
  exact ⟨rfl, cPc c0_eq.2 z1_eq.2⟩

theorem inv_eq {p : Nat} (_hp : Cn p) (h : invYK p (pinvY p) = true) :
    invT 11200 (tabT (unpack 11200 14 p)) = tabT (unpack 11200 14 (pinvY p)) ∧ Cn (pinvY p) :=
  ⟨invT_eq (invYK_spec h).2.2, (invYK_spec h).2.1⟩

@[expose] noncomputable def QKp (p : List Nat × Bool) : Nat := commP (UK p.1) (cond p.2 G3K G5K)

theorem qp_eq {p : List Nat × Bool} (hw : ∀ l ∈ p.1, 1 ≤ l ∧ l ≤ 3)
    (hqi : invYK (UK p.1) (pinvY (UK p.1)) = true) :
    tComm 11200 (tU p.1) (if p.2 then harCG3 () else harCG5 ()) = tabT (unpack 11200 14 (QKp p)) ∧
      Cn (QKp p) := by
  obtain ⟨ea, ca⟩ := tU_eq hw
  obtain ⟨eai, cai⟩ := inv_eq ca hqi
  have hb : (if p.2 then harCG3 () else harCG5 ()) = tabT (unpack 11200 14 (cond p.2 G3K G5K)) ∧
      Cn (cond p.2 G3K G5K) ∧ invYK (cond p.2 G3K G5K) (pinvY (cond p.2 G3K G5K)) = true := by
    cases p.2
    · rw [ite_eq_right Bool.false_ne_true, Bool.cond_false]
      exact ⟨g5_eq.1, g5_eq.2, harC_inv5⟩
    · rw [ite_eq_left rfl, Bool.cond_true]
      exact ⟨g3_eq.1, g3_eq.2, harC_inv3⟩
  obtain ⟨eb, cb, hbi⟩ := hb
  obtain ⟨ebi, cbi⟩ := inv_eq cb hbi
  unfold tComm QKp commP
  rw [ea, eb, eai, ebi, comp_eq ca cb, comp_eq cai cbi, comp_eq (cPc ca cb) (cPc cai cbi)]
  exact ⟨rfl, cPc (cPc ca cb) (cPc cai cbi)⟩

theorem tabs_of_map {α : Type} {L : List α} {f : α → Table} {G : Nat → Nat}
    (h : ∀ j (hj : j < L.length), f L[j] = tabT (unpack 11200 14 (G j)) ∧ Cn (G j)) :
    TabsOK 11200 14 L.length G (L.map f).toArray := by
  refine ⟨by simp, fun j hj => ?_⟩
  rw [getElem!_pos _ j (by simpa using hj), List.getElem_toArray, List.getElem_map]
  exact h j hj

theorem harCQPairs_letters : ∀ p ∈ harCQPairs, ∀ l ∈ p.1, 1 ≤ l ∧ l ≤ 3 := by decide

theorem TQ_tabs : TabsOK 11200 14 6 TQ.GI (harCQ ()).toArray := by
  have e : harCQ () = harCQPairs.map fun p => tComm 11200 (tU p.1)
      (if p.2 then harCG3 () else harCG5 ()) := rfl
  rw [e]
  refine tabs_of_map fun j hj => ?_
  have hj6 : j < 6 := hj
  have hp : harCQPairs.getD j ([], true) = harCQPairs[j] := List.getD_eq_getElem _ _ hj
  have hinv := harC_inv
  simp only [bAnd_iff] at hinv
  have hqi := allN_spec hinv.1 j hj6
  rw [hp] at hqi
  have eq : TQ.GI j = QKp harCQPairs[j] := by
    rw [(base_parts.2.2.2.1 j hj6).1]
    unfold QK QKp
    rw [hp]
  rw [eq]
  exact qp_eq (harCQPairs_letters _ (List.getElem_mem hj)) hqi

theorem uw_eq {j : Nat} (_hj : j < 3) : UL (j + 1) = WK (harUW.getD j []) := by
  unfold UL
  rw [Nat.add_sub_cancel]

theorem TE_tabs : TabsOK 11200 14 3 TE.GI harU.toArray := by
  have e : harU = harUW.map (wordTbl 11200 harYs) := rfl
  rw [e]
  refine tabs_of_map fun j hj => ?_
  have hj3 : j < 3 := hj
  have hp : harUW.getD j [] = harUW[j] := List.getD_eq_getElem _ _ hj
  rw [(base_parts.1 j hj3).1, uw_eq hj3, hp]
  have hl := harUW_letters j hj3
  rw [hp] at hl
  exact wordTbl_eq hl

theorem tabs_of_list {L : List Table} {G : Nat → Nat}
    (h : ∀ j (hj : j < L.length), L[j] = tabT (unpack 11200 14 (G j)) ∧ Cn (G j)) :
    TabsOK 11200 14 L.length G L.toArray := by
  refine ⟨by simp, fun j hj => ?_⟩
  rw [getElem!_pos _ j (by simpa using hj), List.getElem_toArray]
  exact h j hj

theorem TC_tabs : TabsOK 11200 14 5 TCG (harCGens ()).toArray := by
  unfold harCGens harU
  refine tabs_of_list fun j hj => ?_
  have hlen : harUW.length = 3 := rfl
  have hj5 : j < 5 := by simpa [hlen] using hj
  rw [(base_parts.2.2.2.2.2.2.1 j hj5).1]
  by_cases h3 : j < 3
  · rw [List.getElem_append_left (by simpa [hlen] using h3), List.getElem_map]
    have hp : harUW.getD j [] = harUW[j] := List.getD_eq_getElem _ _ h3
    have hl := harUW_letters j h3
    rw [hp] at hl
    have ec : CGK j = UL (j + 1) := by
      unfold CGK
      rcases (by omega : j = 0 ∨ j = 1 ∨ j = 2) with rfl | rfl | rfl <;>
        simp only [List.getD_cons_succ, List.getD_cons_zero]
    rw [ec, uw_eq h3, hp]
    exact wordTbl_eq hl
  · rw [List.getElem_append_right (by simpa [hlen] using Nat.le_of_not_lt h3)]
    rcases (by omega : j = 3 ∨ j = 4) with rfl | rfl
    · have ec : CGK 3 = G3K := by
        unfold CGK
        simp only [List.getD_cons_succ, List.getD_cons_zero]
      simp only [List.length_map, hlen, Nat.sub_self, List.getElem_cons_zero, ec]
      exact g3_eq
    · have ec : CGK 4 = G5K := by
        unfold CGK
        simp only [List.getD_cons_succ, List.getD_cons_zero]
      simp only [List.length_map, hlen, Nat.reduceSub, List.getElem_cons_succ, List.getElem_cons_zero,
        ec]
      exact g5_eq

theorem sH : ∀ i < TE.cnt, hsortPtK 11200 14 (mask 14) TE.cnt TE.T TE.HS TE.HSI i = true := by
  have hc := base_parts.2.1
  refine CFSG.KS.PEnumB.hsortPtK_of_V (HV := TEV) (fun i hi => ?_) (fun i hi => ?_)
  · have hk : i / 64 < 16 := by omega
    have h := slK_spec (ch7291hv_all (i / 64) hk) i (by change 64 * (i / 64) ≤ i; omega)
      (by change i < 64 * (i / 64) + 64; omega) hi
    unfold ch7291jHv at h
    unfold CFSG.KS.PEnumB.hvK
    rw [← hkeyU_eq]
    exact h
  · exact slK_spec ch7291hsv_ok i (by omega) (by omega) hi

theorem ntE_at {r i : Nat} (k : Nat) (h : ntE r k = true) (h1 : 16 * k ≤ i)
    (h2 : i < 16 * k + 16) (h3 : i < 2 ^ r) : pcTK 11200 14 (mask 14) TE.T TEP r i = true :=
  slK_spec h i h1 h2
    (by rw [shl_one]; exact h3)

theorem ntE_spec : ∀ r < 10, ∀ i < 2 ^ r, pcTK 11200 14 (mask 14) TE.T TEP r i = true := by
  intro r hr i hi
  by_cases h4 : r < 4
  · have h16 : 2 ^ r ≤ 2 ^ 4 := Nat.pow_le_pow_right (by norm_num) (by omega)
    have hi' : i < 16 := by
      have := Nat.lt_of_lt_of_le hi h16
      simpa using this
    exact ntE_at 0 (CFSG.KS.Raw.Orb.allN_iff.1 ntE_lo r h4) (by omega) (by omega) hi
  · have hi' := hi
    interval_cases r <;> norm_num at hi'
    · exact ntE_at 0 ntE4 (by omega) (by omega) hi
    · exact ntE_at (i / 16) (ntE5_all (i / 16) (by change i / 16 < 2; omega))
        (by omega) (by omega) hi
    · exact ntE_at (i / 16) (ntE6_all (i / 16) (by change i / 16 < 4; omega))
        (by omega) (by omega) hi
    · exact ntE_at (i / 16) (ntE7_all (i / 16) (by change i / 16 < 8; omega))
        (by omega) (by omega) hi
    · exact ntE_at (i / 16) (ntE8_all (i / 16) (by change i / 16 < 16; omega))
        (by omega) (by omega) hi
    · exact ntE_at (i / 16) (ntE9_all (i / 16) (by change i / 16 < 32; omega))
        (by omega) (by omega) hi

theorem rlE_ok {r c : Nat} (hr : r < 10) (hc : 4 * c < max r 1) : rlE r c = true := by
  have hc3 : c < 3 := by omega
  by_cases h4 : r < 4
  · have e : c = 0 := by omega
    rw [e]
    exact CFSG.KS.Raw.Orb.allN_iff.1 rlE_lo r h4
  · interval_cases r <;> interval_cases c <;> (try omega)
    exacts [rlE40, rlE50, rlE51, rlE60, rlE61, rlE70, rlE71, rlE80, rlE81, rlE90, rlE91,
      rlE92]

theorem rlE_spec {r : Nat} (hr : r < 10) :
    canonK 11200 14 (mask 14) (11200 * 14) (pcNK TE.T TEP (2 ^ r)) = true ∧
      (∃ a < 2 ^ r, pcomp 11200 14 (mask 14) (pcNK TE.T TEP (2 ^ r)) (pcNK TE.T TEP (2 ^ r)) =
        pcNK TE.T TEP a) ∧
      ∀ s < r, ∃ b < 2 ^ r,
        pcomp 11200 14 (mask 14) (pcNK TE.T TEP (2 ^ r)) (pcNK TE.T TEP (2 ^ s)) =
          pcomp 11200 14 (mask 14) (pcNK TE.T TEP b) (pcNK TE.T TEP (2 ^ r)) :=
  pcR_spec (rlE_ok (c := 0) hr (by omega)) (fun s hs => rlE_ok (c := s / 4) hr (by omega))

theorem clos_E : ∀ i < TE.cnt, ∀ i' < TE.cnt, ∃ q < TE.cnt,
    pcomp 11200 14 (mask 14) (pcNK TE.T TEP i) (pcNK TE.T TEP i') = pcNK TE.T TEP q := by
  have hc := base_parts.2.1
  obtain ⟨h0, hc0, -, -⟩ := pcM_spec mbE_ok
  have H := (pc_closed (m := 10) (N := pcNK TE.T TEP) h0 hc0
    (fun r hr => (rlE_spec hr).1)
    (fun r hr i hi => pcT_spec (ntE_spec r hr i hi))
    (fun r hr => (rlE_spec hr).2.1)
    (fun r hr => (rlE_spec hr).2.2) 10 (Nat.le_refl _)).2
  have e : (2 : Nat) ^ 10 = 1024 := by norm_num
  rw [e] at H
  rw [hc]
  exact H

theorem sF : ∀ c < TE.cnt * (3 + 3),
    clHK 11200 14 (mask 14) 3 TE.cnt TE.T TE.GI TEI TECl c = true := by
  intro c hc'
  have hc := base_parts.2.1
  have hk : c / 1024 < 6 := by omega
  exact pcC_clH (by norm_num) (by norm_num) clos_E mbE_ok
    (slK_spec (clPE_all (c / 1024) hk) c (by change 1024 * (c / 1024) ≤ c; omega)
      (by change c < 1024 * (c / 1024) + 1024; omega) (by change c < TE.cnt * 6; omega)) hc'

theorem sC : ∀ i < TE.cnt,
    CFSG.KS.PEnumC.penumPtC 3 6 TE.cnt TE.T TE.PL TE.POS TECl TE.SRT TE.SRI i = true := by
  intro i hi
  have hc := base_parts.2.1
  have hk : i / 128 < 8 := by omega
  exact CFSG.KS.PEnumC.penumSlC_spec (ch7291pe_all (i / 128) hk) i
    (by change 128 * (i / 128) ≤ i; omega) (by change i < 128 * (i / 128) + 128; omega) hi

theorem sT : ∀ i < TE.cnt, canonK 11200 14 (mask 14) (11200 * 14) (TE.T i) = true :=
  clH_canon (fun j hj => (invYK_spec (base_parts.1 j hj).2.2).1) ch7291t0 sF sC

theorem sCl : ∀ c < TE.cnt * (3 + 3), findPtK TE.cnt TE.T
    (prodQK 11200 14 (mask 14) (3 + 3) TE.T (bothK 3 TE.GI TEI)) TECl c = true :=
  findPt_of_clH sT (fun j hj => (invYK_spec (base_parts.1 j hj).2.2).2.2) sF

theorem sE : ∀ i < TE.cnt, penumPtK 11200 14 (mask 14) (11200 * 14) true TE.G TE.GI 3 TE.cnt TE.T
    TE.PL TE.POS TE.SRT TE.SRI i = true := by
  have hc := base_parts.2.1
  refine CFSG.KS.PEnumC.penumPtK_of_C (K := 3 + 3) (S := bothK 3 TE.GI TEI) (CL := TECl)
    (by omega) (fun j hj => (base_parts.1 j hj).2.1) (fun j hj => ?_)
    (fun j hj => (invYK_spec (base_parts.1 j hj).2.2).1) ch7291t0 sCl sC
  unfold bothK
  rw [CFSG.KS.Raw.Orb.nIf_eq, ite_eq_left (Nat.blt_eq.mpr hj)]

theorem ntQ_at {r i : Nat} (k : Nat) (h : ntQ r k = true) (h1 : 16 * k ≤ i)
    (h2 : i < 16 * k + 16) (h3 : i < 2 ^ r) : pcTK 11200 14 (mask 14) TQ.T TQP r i = true :=
  slK_spec h i h1 h2
    (by rw [shl_one]; exact h3)

theorem ntQ_spec : ∀ r < 7, ∀ i < 2 ^ r, pcTK 11200 14 (mask 14) TQ.T TQP r i = true := by
  intro r hr i hi
  by_cases h4 : r < 4
  · have h16 : 2 ^ r ≤ 2 ^ 4 := Nat.pow_le_pow_right (by norm_num) (by omega)
    have hi' : i < 16 := by
      have := Nat.lt_of_lt_of_le hi h16
      simpa using this
    exact ntQ_at 0 (CFSG.KS.Raw.Orb.allN_iff.1 ntQ_lo r h4) (by omega) (by omega) hi
  · have hi' := hi
    interval_cases r <;> norm_num at hi'
    · exact ntQ_at 0 ntQ4 (by omega) (by omega) hi
    · exact ntQ_at (i / 16) (ntQ5_all (i / 16) (by change i / 16 < 2; omega))
        (by omega) (by omega) hi
    · exact ntQ_at (i / 16) (ntQ6_all (i / 16) (by change i / 16 < 4; omega))
        (by omega) (by omega) hi

theorem rlQ_ok {r c : Nat} (hr : r < 7) (hc : 4 * c < max r 1) : rlQ r c = true := by
  have hc2 : c < 2 := by omega
  by_cases h4 : r < 4
  · have e : c = 0 := by omega
    rw [e]
    exact CFSG.KS.Raw.Orb.allN_iff.1 rlQ_lo r h4
  · interval_cases r <;> interval_cases c <;> (try omega)
    exacts [rlQ40, rlQ50, rlQ51, rlQ60, rlQ61]

theorem rlQ_spec {r : Nat} (hr : r < 7) :
    canonK 11200 14 (mask 14) (11200 * 14) (pcNK TQ.T TQP (2 ^ r)) = true ∧
      (∃ a < 2 ^ r, pcomp 11200 14 (mask 14) (pcNK TQ.T TQP (2 ^ r)) (pcNK TQ.T TQP (2 ^ r)) =
        pcNK TQ.T TQP a) ∧
      ∀ s < r, ∃ b < 2 ^ r,
        pcomp 11200 14 (mask 14) (pcNK TQ.T TQP (2 ^ r)) (pcNK TQ.T TQP (2 ^ s)) =
          pcomp 11200 14 (mask 14) (pcNK TQ.T TQP b) (pcNK TQ.T TQP (2 ^ r)) :=
  pcR_spec (rlQ_ok (c := 0) hr (by omega)) (fun s hs => rlQ_ok (c := s / 4) hr (by omega))

theorem clos_Q : ∀ i < TQ.cnt, ∀ i' < TQ.cnt, ∃ q < TQ.cnt,
    pcomp 11200 14 (mask 14) (pcNK TQ.T TQP i) (pcNK TQ.T TQP i') = pcNK TQ.T TQP q := by
  have hc := base_parts.2.2.2.2.1
  obtain ⟨h0, hc0, -, -⟩ := pcM_spec mbQ_ok
  have H := (pc_closed (m := 7) (N := pcNK TQ.T TQP) h0 hc0
    (fun r h => (rlQ_spec h).1)
    (fun r h i hi => pcT_spec (ntQ_spec r h i hi))
    (fun r h => (rlQ_spec h).2.1)
    (fun r h => (rlQ_spec h).2.2) 7 (Nat.le_refl _)).2
  have e : (2 : Nat) ^ 7 = 128 := by norm_num
  rw [e] at H
  rw [hc]
  exact H

theorem qF : ∀ c < TQ.cnt * (6 + 6),
    clHK 11200 14 (mask 14) 6 TQ.cnt TQ.T TQ.GI TQI TQCl c = true := by
  intro c hc'
  have hc := base_parts.2.2.2.2.1
  have hk : c / 768 < 2 := by omega
  exact pcC_clH (by norm_num) (by norm_num) clos_Q mbQ_ok
    (slK_spec (clPQ_all (c / 768) hk) c (by change 768 * (c / 768) ≤ c; omega)
      (by change c < 768 * (c / 768) + 768; omega) (by change c < TQ.cnt * 12; omega)) hc'

theorem qC : ∀ i < TQ.cnt,
    CFSG.KS.PEnumC.penumPtC 6 12 TQ.cnt TQ.T TQ.PL TQ.POS TQCl TQ.SRT TQ.SRI i = true := by
  intro i hi
  have hc := base_parts.2.2.2.2.1
  have hk : i / 64 < 2 := by omega
  exact CFSG.KS.PEnumC.penumSlC_spec (peQ_all (i / 64) hk) i
    (by change 64 * (i / 64) ≤ i; omega) (by change i < 64 * (i / 64) + 64; omega) hi

theorem qT : ∀ i < TQ.cnt, canonK 11200 14 (mask 14) (11200 * 14) (TQ.T i) = true :=
  clH_canon (fun j hj => (invYK_spec (base_parts.2.2.2.1 j hj).2.2).1) cnQ0 qF qC

theorem qCl : ∀ c < TQ.cnt * (6 + 6), findPtK TQ.cnt TQ.T
    (prodQK 11200 14 (mask 14) (6 + 6) TQ.T (bothK 6 TQ.GI TQI)) TQCl c = true :=
  findPt_of_clH qT (fun j hj => (invYK_spec (base_parts.2.2.2.1 j hj).2.2).2.2) qF

theorem qE : ∀ i < TQ.cnt, penumPtK 11200 14 (mask 14) (11200 * 14) true TQ.G TQ.GI 6 TQ.cnt TQ.T
    TQ.PL TQ.POS TQ.SRT TQ.SRI i = true := by
  have hc := base_parts.2.2.2.2.1
  refine CFSG.KS.PEnumC.penumPtK_of_C (K := 6 + 6) (S := bothK 6 TQ.GI TQI) (CL := TQCl)
    (by omega) (fun j hj => (base_parts.2.2.2.1 j hj).2.1) (fun j hj => ?_)
    (fun j hj => (invYK_spec (base_parts.2.2.2.1 j hj).2.2).1) cnQ0 qCl qC
  unfold bothK
  rw [CFSG.KS.Raw.Orb.nIf_eq, ite_eq_left (Nat.blt_eq.mpr hj)]

theorem qH : ∀ i < TQ.cnt, hsortPtK 11200 14 (mask 14) TQ.cnt TQ.T TQ.HS TQ.HSI i = true := by
  intro i hi
  have hc := base_parts.2.2.2.2.1
  have hk : i / 64 < 2 := by omega
  rw [← hsortPtKF_eq 11200 14 TQ.cnt TQ.T TQ.HS TQ.HSI i]
  exact slK_spec (hsQF_all (i / 64) hk) i (by change 64 * (i / 64) ≤ i; omega)
    (by change i < 64 * (i / 64) + 64; omega) hi

theorem qN : ∀ c < TQ.cnt * 5, findPtK TQ.cnt TQ.T (conjQK 11200 14 (mask 14) 5 TQ.T TCG TCGI) TQN
    c = true := by
  have hc := base_parts.2.2.2.2.1
  have hT0 : TQ.T 0 = pidn 11200 14 := by
    have h := base_parts.2.2.2.2.2.1
    unfold penumHdK at h
    simp only [bAnd_iff] at h
    exact Nat.eq_of_beq_eq_true h.2.2.1
  have hW : ∀ i < TQ.cnt, nqWK 12 5 TQ.cnt TQ.PL TQCl TQN i = true := by
    intro i hi
    have hk : i / 64 < 2 := by omega
    exact slK_spec (nqQ_all (i / 64) hk) i (by change 64 * (i / 64) ≤ i; omega)
      (by change i < 64 * (i / 64) + 64; omega) hi
  exact findPt_of_nq (K := 6 + 6) (S := TQ.GI) qT
    (fun l hl => (invYK_spec (base_parts.2.2.2.1 l hl).2.2).1) hT0
    (fun x hx l hl => clH_at qF hx hl)
    (fun i hi h0 => CFSG.KS.PEnumC.penumPtC_par (qC i hi) h0)
    (fun j hj => invYK_spec (base_parts.2.2.2.2.2.2.1 j hj).2)
    (fun j hj => CFSG.KS.Raw.Orb.allN_iff.1 nqQI_ok j hj) nqQG_ok hW

theorem nePtK_spec {c ci y t : Nat} : ∀ r p, nePtK c ci y t r p = true → ∃ p', p ≤ p' ∧
    p' < p + r ∧ pg 14 (mask 14) t p' ≠ pg 14 (mask 14) c (pg 14 (mask 14) y (pg 14 (mask 14) ci p')) := by
  intro r
  induction r with
  | zero =>
    intro p h
    have h' : false = true := h
    cases h'
  | succ r ih =>
    intro p h
    change bIf(Nat.beq (pg 14 (mask 14) t p)
      (pg 14 (mask 14) c (pg 14 (mask 14) y (pg 14 (mask 14) ci p))),
      nePtK c ci y t r (Nat.succ p), true) = true at h
    cases e : Nat.beq (pg 14 (mask 14) t p)
        (pg 14 (mask 14) c (pg 14 (mask 14) y (pg 14 (mask 14) ci p)))
    · refine ⟨p, Nat.le_refl _, by omega, fun h' => ?_⟩
      rw [h', Nat.beq_refl] at e
      cases e
    · rw [e] at h
      obtain ⟨p', h1, h2, h3⟩ := ih _ h
      exact ⟨p', by omega, by omega, h3⟩

theorem c3 : ∀ i < TE.cnt, c3At i = true := by
  intro i hi
  have hc := base_parts.2.1
  have hk : i / 128 < 8 := by omega
  have h0 := c3S_all (i / 128) hk
  unfold c3S at h0
  rw [CFSG.KS.Raw.Orb.strictB_eq] at h0
  have h := slK_spec h0 i (by change 128 * (i / 128) ≤ i; omega)
    (by change i < 128 * (i / 128) + 128; omega) hi
  have kci := cI_eq.2
  obtain ⟨-, -, -, hci⟩ := CFSG.KS.PF.canon_facts kci
  have ho := CFSG.KS.Raw.Orb.allN_iff.1 harC_o0
  have hm := CFSG.KS.Raw.Orb.allN_iff.1 harC_m
  have hz : TE.T 898 = Z2K := Nat.eq_of_beq_eq_true harC_TZ2
  have h0c : pg 14 (mask 14) CKI 0 = 0 := Nat.eq_of_beq_eq_true harC_ci0
  unfold c3P at h
  unfold c3At
  rw [CFSG.KS.Raw.Orb.strictB_eq, hz] at h
  rw [CFSG.KS.Raw.Orb.strictB_eq]
  cases e : Nat.beq (pc (TE.T i) (TE.T i)) Z2K
  · rfl
  · have hs : sqPre Z2K (TE.T i) = true := by
      rw [← Nat.eq_of_beq_eq_true e]
      unfold sqPre
      rw [CFSG.KS.Raw.Orb.allN_iff]
      intro p hp
      unfold pc
      rw [CFSG.KS.PF.pg_pcomp (n := 11200) (by decide) (by omega)]
      exact Nat.beq_refl _
    rw [hs] at h
    have hx : ∀ p < 11200, pg 14 (mask 14) (pc (pc CK (TE.T i)) CKI) p =
        pg 14 (mask 14) CK (pg 14 (mask 14) (TE.T i) (pg 14 (mask 14) CKI p)) := by
      intro p hp
      unfold pc
      rw [CFSG.KS.PF.pg_pcomp (n := 11200) (by decide) hp,
        CFSG.KS.PF.pg_pcomp (n := 11200) (by decide) (hci p hp)]
    change strictB (pc (pc CK (TE.T i)) CKI)
      (fun x => allN TE.cnt (fun q => bIf(Nat.beq (TE.T q) x, false, true))) = true
    rw [CFSG.KS.Raw.Orb.strictB_eq, CFSG.KS.Raw.Orb.allN_iff]
    intro q hq
    cases e2 : Nat.beq (TE.T q) (pc (pc CK (TE.T i)) CKI)
    · rfl
    · exfalso
      cases e3 : m0At (pg 14 (mask 14) (TE.T i) 0)
      · have h3 : o0At (pg 14 (mask 14) (TE.T q) 0) = true := ho q hq
        rw [Nat.eq_of_beq_eq_true e2, hx 0 (by decide), h0c] at h3
        have h4 := hm (pg 14 (mask 14) (TE.T i) 0) (CFSG.KS.PF.pg_lt 14 _ _)
        change bIf(o0At (pg 14 (mask 14) CK (pg 14 (mask 14) (TE.T i) 0)),
          m0At (pg 14 (mask 14) (TE.T i) 0), true) = true at h4
        rw [h3, e3] at h4
        cases h4
      · rw [e3] at h
        have h2 : allN TE.cnt (fun q => nePtK CK CKI (TE.T i) (TE.T q) 11200 0) = true := h
        rw [CFSG.KS.Raw.Orb.allN_iff] at h2
        obtain ⟨p, -, hp, hne⟩ := nePtK_spec 11200 0 (h2 q hq)
        apply hne
        rw [Nat.eq_of_beq_eq_true e2]
        exact hx p (by omega)

theorem TE_G : ∀ j < 3, TE.G j = pidn 11200 14 := fun j hj => (base_parts.1 j hj).2.1

theorem TQ_G : ∀ j < 6, TQ.G j = pidn 11200 14 := fun j hj => (base_parts.2.2.2.1 j hj).2.1

theorem TE_inv : ∀ j < 3, invEqK 11200 14 (mask 14) (11200 * 14) (TE.GI j) (TEI j) = true ∧
    canonK 11200 14 (mask 14) (11200 * 14) (TEI j) = true := fun j hj =>
  ⟨(invYK_spec (base_parts.1 j hj).2.2).2.2, (invYK_spec (base_parts.1 j hj).2.2).2.1⟩

theorem TQ_inv : ∀ j < 6, invEqK 11200 14 (mask 14) (11200 * 14) (TQ.GI j) (TQI j) = true ∧
    canonK 11200 14 (mask 14) (11200 * 14) (TQI j) = true := fun j hj =>
  ⟨(invYK_spec (base_parts.2.2.2.1 j hj).2.2).2.2, (invYK_spec (base_parts.2.2.2.1 j hj).2.2).2.1⟩

theorem TC_inv : ∀ j < 5, invEqK 11200 14 (mask 14) (11200 * 14) (TCG j) (TCGI j) = true ∧
    canonK 11200 14 (mask 14) (11200 * 14) (TCGI j) = true := fun j hj =>
  ⟨(invYK_spec (base_parts.2.2.2.2.2.2.1 j hj).2).2.2,
    (invYK_spec (base_parts.2.2.2.2.2.2.1 j hj).2).2.1⟩

theorem perm_all {gs : List Table} {k : Nat} {G GI : Nat → Nat} (hg : TabsOK 11200 14 k G gs.toArray)
    (hi : ∀ j < k, invEqK 11200 14 (mask 14) (11200 * 14) (G j) (GI j) = true ∧
      canonK 11200 14 (mask 14) (11200 * 14) (GI j) = true) :
    gs.all (fun g => permOK 11200 g && invOK 11200 g (invT 11200 g)) = true := by
  rw [List.all_eq_true]
  intro g hgm
  obtain ⟨j, hj, rfl, hc⟩ := TabsOK_list hg hgm
  rw [permOK_unpack hc (hi j hj).1, invT_eq (hi j hj).1, invOK_unpack hc (hi j hj).2 (hi j hj).1]
  rfl

theorem memT_hRec_false {cnt X : Nat} {T PL : Nat → Nat} (hX : Cn X)
    (hT : ∀ q < cnt, Cn (T q)) (h : ∀ q < cnt, Nat.beq (T q) X = false) :
    memT 11200 (hRec 11200 14 cnt T PL).1 (tabT (unpack 11200 14 X)) = false := by
  unfold memT
  rw [Bool.eq_false_iff]
  intro ha
  rw [Array.any_eq_true] at ha
  obtain ⟨q, hq, hx⟩ := ha
  have hq' : q < cnt := by simpa [hRec] using hq
  have e : (hRec 11200 14 cnt T PL).1[q] = tabT (unpack 11200 14 (T q)) := by simp [hRec]
  rw [e, tblEq_eq hX (hT q hq')] at hx
  have h2 := h q hq'
  rw [Nat.eq_of_beq_eq_true hx, Nat.beq_refl] at h2
  exact absurd h2 (by decide)

theorem all_hRec {cnt : Nat} {T PL : Nat → Nat} {p : Table → Bool}
    (h : ∀ i < cnt, p (tabT (unpack 11200 14 (T i))) = true) : (hRec 11200 14 cnt T PL).1.all p = true := by
  rw [Array.all_eq_true]
  intro i hi
  have hi' : i < cnt := by simpa [hRec] using hi
  simpa [hRec] using h i hi'

theorem harCOK1_true : harCOK1 () = true := by
  have b := base_parts
  obtain ⟨-, -, -, -, -, -, -, -, -, -, o3, n3, o5, n5, c3z, c5z, ccz, ci, -, -⟩ := b
  obtain ⟨e3, k3⟩ := g3_eq
  obtain ⟨e5, k5⟩ := g5_eq
  obtain ⟨ec, kc⟩ := c_eq
  obtain ⟨ez, kz⟩ := z1_eq
  have hc := perm_all TC_tabs TC_inv
  have hcc := invYK_spec ci
  unfold harCOK1
  simp only []
  rw [hc, e3, e5, ec, ez, comp_eq k3 k3, comp_eq (cPc k3 k3) k3, comp_eq k5 k5, comp_eq (cPc k5 k5) k5,
    comp_eq (cPc (cPc k5 k5) k5) k5, comp_eq (cPc (cPc (cPc k5 k5) k5) k5) k5, idT_eq,
    tblEq_eq (cPc (cPc k3 k3) k3) cId, tblEq_eq k3 cId,
    tblEq_eq (cPc (cPc (cPc (cPc k5 k5) k5) k5) k5) cId, tblEq_eq k5 cId,
    commTT_eq k3 kz, commTT_eq k5 kz, commTT_eq kc kz, permOK_unpack kc hcc.2.2, invT_eq hcc.2.2,
    invOK_unpack kc hcc.2.1 hcc.2.2]
  rw [bIf_ft] at n3 n5
  simp only [o3, o5, c3z, c5z, ccz, n3, n5, Bool.and_true]

theorem harCOK2_true : harCOK2 () = true := by
  have b := base_parts
  obtain ⟨-, -, -, -, hq, hh, -, hr1, hr2, hroot, -⟩ := b
  have hn := hn
  have hq' : (harCQ ()).all (permOK 11200) = true := by
    rw [List.all_eq_true]
    intro g hgm
    obtain ⟨j, hj, rfl, hc⟩ := TabsOK_list TQ_tabs hgm
    exact permOK_unpack hc (TQ_inv j hj).1
  have he := enumOK_of hn TQ_G TQ_tabs TQ_inv hh qE qH qCl hq
  have hnm := normOK_of hn TQ_G TQ_tabs hh qE qH TC_tabs TC_inv qN
  have hmem := mulH_sound hn TQ_G TQ_tabs hh qE qH
  obtain ⟨er, cr⟩ := tU_eq (wd := harCRoot) (by decide)
  obtain ⟨ez, kz⟩ := z1_eq
  unfold harCOK2
  simp only []
  rw [hq', he, hnm, hmem.1, er, ez, comp_eq cr cr, tblEq_eq (cPc cr cr) kz,
    memT_of hr1 (by rw [hr2]; exact tblEq_self cr)]
  simp only [Bool.true_and]
  exact hroot

theorem harCOK3_true : harCOK3 () = true := by
  have b := base_parts
  obtain ⟨-, hc, hh, -⟩ := b
  have hn := hn
  have he := enumOK_of hn TE_G TE_tabs TE_inv hh sE sH sCl hc
  have hm := mulH_sound hn TE_G TE_tabs hh sE sH
  obtain ⟨ec, kc⟩ := c_eq
  obtain ⟨eci, kci⟩ := cI_eq
  obtain ⟨ez, kz⟩ := z2_eq
  have hT : ∀ q < TE.cnt, Cn (TE.T q) := fun q hq => penumPt_canon (sE q hq)
  unfold harCOK3
  simp only []
  rw [he, hm.1, eci, ec, ez, Bool.true_and]
  refine all_hRec fun i hi => ?_
  have hy := hT i hi
  have h := c3 i hi
  unfold c3At at h
  simp only [CFSG.KS.PEnum.strictB_app'] at h
  unfold conjT
  rw [comp_eq hy hy, tblEq_eq (cPc hy hy) kz, comp_eq kc hy, comp_eq (cPc kc hy) kci]
  cases e : Nat.beq (pc (TE.T i) (TE.T i)) Z2K
  · rfl
  · rw [e] at h
    have h' : allN TE.cnt (fun q => bIf(Nat.beq (TE.T q) (pc (pc CK (TE.T i)) CKI), false, true)) =
        true := h
    rw [memT_hRec_false (cPc (cPc kc hy) kci) hT fun q hq => by
      have := allN_spec h' q hq
      cases e' : Nat.beq (TE.T q) (pc (pc CK (TE.T i)) CKI)
      · rfl
      · rw [e'] at this
        exact absurd this (by decide)]
    rfl

theorem harCOK_true : harCOK () = true := by
  unfold harCOK
  rw [harCOK1_true, harCOK2_true, harCOK3_true]
  rfl

end CFSG.KD.TwoHS

end
