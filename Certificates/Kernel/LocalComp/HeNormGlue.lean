module

public import Certificates.Kernel.LocalComp.HeNorm
public import Certificates.Kernel.SporSch.HeT.B2114
public import Certificates.Kernel.LocalComp.HeFix2329.Glue
public import CFSG.Certificates.Kernel.MaxD2.Basic
public import CFSG.Certificates.Kernel.HeFixKSnd.Basic

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelLC.HeNorm

open CFSG.KC.Enum CFSG.KS CFSG.KS.Prim CFSG.KS.Raw CFSG.KC.BfsPin CFSG.KC.PermTool
open CFSG.PSL3Four.Native CFSG.Sporadic.SmallOddCore CFSG.ComponentClassification.GrSLit.HeldFix
open CFSG.KC.LocalComp.ConjPin CertificateChecks.KernelLC.HeFix
open CertificateChecks.KernelSporSch.HeB14 (C1 C1I C1_word c1_parts)
open Certificates.HeNorm (words wt wti hT hTi cj)
open CertificateChecks.KernelLC.HePtW

theorem allN_false {n : Nat} {f : Nat → Bool} (h : allN n f = false) : ∃ k < n, f k = false := by
  by_contra hne
  have : allN n f = true := CFSG.KS.Raw.Orb.allN_iff.2 fun k hk => by
    cases e : f k
    · exact absurd ⟨k, hk, e⟩ hne
    · rfl
  rw [this] at h
  exact absurd h (by decide)

theorem letters : ∀ w ∈ words, ∀ j ∈ w, j < 9 := by decide

theorem lt9 {i : Nat} (hi : i < 8) : ∀ j ∈ words.getD i [], j < 9 := by
  interval_cases i <;> decide

theorem pg_pc {p q x : Nat} (hx : x < 8330) :
    pg 14 (mask 14) (pc p q) x = pg 14 (mask 14) p (pg 14 (mask 14) q x) :=
  CFSG.KS.PF.pg_pcomp (by norm_num) hx

theorem c1pt {j : Nat} (hj : j < 9) {x : Nat} (hx : x < 8330) :
    (pg 14 (mask 14) (C1 j) x < 8330 ∧ pg 14 (mask 14) (C1I j) (pg 14 (mask 14) (C1 j) x) = x) ∧
    (pg 14 (mask 14) (C1I j) x < 8330 ∧ pg 14 (mask 14) (C1 j) (pg 14 (mask 14) (C1I j) x) = x) :=
  ⟨(CFSG.KS.MaxD2.perm_spec (c1_parts hj).1).1 x hx, (CFSG.KS.MaxD2.perm_spec (c1_parts hj).1).2 x hx⟩

theorem hnPt {i : Nat} (hi : i < 8) {x : Nat} (hx : x < 8330) :
    (ptW C1 (words.getD i []) x < 8330 ∧
      ptW C1I (words.getD i []).reverse (ptW C1 (words.getD i []) x) = x) ∧
    (ptW C1I (words.getD i []).reverse x < 8330 ∧
      ptW C1 (words.getD i []) (ptW C1I (words.getD i []).reverse x) = x) := by
  refine ⟨ptW_inv _ (fun j hj y hy => (c1pt (lt9 hi j hj) hy).1) x hx, ?_⟩
  have h := ptW_inv (G := C1I) (GI := C1) (words.getD i []).reverse
    (fun j hj y hy => (c1pt (lt9 hi j (List.mem_reverse.1 hj)) hy).2) x hx
  rwa [List.reverse_reverse] at h

theorem wparts : (∀ j < 9, cn (C1 j) = true ∧ cn (C1I j) = true) ∧
    ∀ i < 8, permOK 8330 14 (mask 14) (8330 * 14) (W i) (WI i) = true := by
  have hc : ∀ j < 9, cn (C1 j) = true ∧ cn (C1I j) = true := fun j hj =>
    CFSG.KS.MaxD2.perm_canon (c1_parts hj).1 hsz
  refine ⟨hc, fun i hi => permOK_of
    (canonK_wordTabK hid _ fun k hk => (hc k (lt9 hi k hk)).1)
    (canonK_wordTabK hid _ fun k hk => (hc k (lt9 hi k (List.mem_reverse.1 hk))).2) fun x hx => ?_⟩
  unfold W WI
  rw [pg_wordTabK _ _ hx, pg_wordTabK _ _ (hnPt hi hx).1.1]
  exact (hnPt hi hx).1.2

theorem c1T {k : Nat} (hk : k < 9) : hfC1Tabs[k]! = unpack 8330 14 (C1 k) := by
  rw [hfC1Tabs, ofFn_get _ hk]
  exact (C1_word hk).1

theorem cmp {p q : Nat} (hp : cn p = true) (hq : cn q = true) :
    comp 8330 (unpack 8330 14 p) (unpack 8330 14 q) = unpack 8330 14 (pc p q) :=
  compA_unpack hp hq

theorem cnpc {p q : Nat} (hp : cn p = true) (hq : cn q = true) : cn (pc p q) = true :=
  canonK_pcomp hp hq

theorem wt_eq {i : Nat} (hi : i < 8) : wt i = unpack 8330 14 (W i) ∧ cn (W i) = true :=
  ⟨wordTabS_unpack hid hidA _ (fun k hk => (wparts.1 k (lt9 hi k hk)).1)
    (fun k hk => c1T (lt9 hi k hk)),
    canonK_wordTabK hid _ fun k hk => (wparts.1 k (lt9 hi k hk)).1⟩

theorem cnWI {i : Nat} (hi : i < 8) : cn (WI i) = true :=
  canonK_wordTabK hid _ fun k hk => (wparts.1 k (lt9 hi k (List.mem_reverse.1 hk))).2

theorem wti_eq {i : Nat} (hi : i < 8) : wti i = unpack 8330 14 (WI i) := by
  unfold wti
  rw [(wt_eq hi).1]
  exact CFSG.KS.MaxD2.inv_u (wparts.2 i hi)

theorem hT_eq {i j : Nat} (hi : i < 8) (hj : j < 8) :
    hT i j = unpack 8330 14 (Hh i j) ∧ cn (Hh i j) = true := by
  unfold hT
  rw [wti_eq hj, (wt_eq hi).1, cmp (cnWI hj) (wt_eq hi).2]
  exact ⟨rfl, cnpc (cnWI hj) (wt_eq hi).2⟩

theorem cnHI {i j : Nat} (hi : i < 8) (hj : j < 8) : cn (HI i j) = true :=
  cnpc (cnWI hi) (wt_eq hj).2

theorem pg_HI {i j : Nat} (_hi : i < 8) (hj : j < 8) {x : Nat} (hx : x < 8330) :
    pg 14 (mask 14) (HI i j) x = ptW C1I (words.getD i []).reverse (ptW C1 (words.getD j []) x) := by
  unfold HI WI W
  rw [pg_pc hx, pg_wordTabK _ _ hx, pg_wordTabK _ _ (hnPt hj hx).1.1]

theorem pg_Hh {i j : Nat} (hi : i < 8) (_hj : j < 8) {x : Nat} (hx : x < 8330) :
    pg 14 (mask 14) (Hh i j) x = ptW C1I (words.getD j []).reverse (ptW C1 (words.getD i []) x) := by
  unfold Hh WI W
  rw [pg_pc hx, pg_wordTabK _ _ hx, pg_wordTabK _ _ (hnPt hi hx).1.1]

theorem hparts {i j : Nat} (hi : i < 8) (hj : j < 8) :
    permOK 8330 14 (mask 14) (8330 * 14) (Hh i j) (HI i j) = true := by
  refine permOK_of (hT_eq hi hj).2 (cnHI hi hj) fun x hx => ?_
  have b1 := (hnPt hi hx).1.1
  have b2 := (hnPt hj b1).2.1
  rw [pg_Hh hi hj hx, pg_HI hi hj b2, (hnPt hj b1).2.2, (hnPt hi hx).1.2]

theorem cnT {k : Nat} (hk : k < 5) : cn (T0K k) = true := (T0_get (j := k) (by omega)).2

theorem pg_T0K {k : Nat} (hk : k < 5) {x : Nat} (hx : x < 8330) :
    pg 14 (mask 14) (T0K k) x = ptT k x := by
  match k, hk with
  | 0, _ => rw [T0K_0]; rfl
  | i + 1, hk =>
    rw [T0K_succ (by omega), pg_wordTabK _ _ hx]
    match i, hk with
    | 0, _ => rfl
    | 1, _ => rfl
    | 2, _ => rfl
    | 3, _ => rfl

theorem R_eq {i j k : Nat} (hi : i < 8) (hj : j < 8) (hk : k < 5) :
    restrictK 14 6 hfDelta32 (pc (pc (Hh i j) (T0K k)) (HI i j)) = R i j k := by
  unfold restrictK R
  congr 1
  refine List.map_congr_left fun x hx => ?_
  have hx' := delta_lt x hx
  have b1 := CFSG.KS.MaxD2.canon_lt (cnHI hi hj) hx'
  have b2 := CFSG.KS.MaxD2.canon_lt (cnT hk) b1
  rw [pg_pc hx', pg_pc b1, pg_Hh hi hj b2, pg_T0K hk b1, pg_HI hi hj hx']
  rfl

theorem hTi_eq {i j : Nat} (hi : i < 8) (hj : j < 8) : hTi i j = unpack 8330 14 (HI i j) := by
  unfold hTi
  rw [(hT_eq hi hj).1]
  exact CFSG.KS.MaxD2.inv_u (hparts hi hj)

theorem tt_eq {k : Nat} (hk : k < 5) : hfTTabs[k]! = unpack 8330 14 (T0K k) := by
  have h := (T0_get (j := k) (by omega)).1
  rw [hfT0Tabs, ofFn_get _ (by omega)] at h
  simpa [hk] using h

theorem res_eq {i j k : Nat} (hi : i < 8) (hj : j < 8) (hk : k < 5) :
    hfRes (cj i j k) = unpack 32 6 (R i j k) := by
  have c1 := cnpc (hT_eq hi hj).2 (cnT hk)
  have c2 := cnpc c1 (cnHI hi hj)
  unfold cj hfRes
  rw [(hT_eq hi hj).1, tt_eq hk, hTi_eq hi hj, cmp (hT_eq hi hj).2 (cnT hk), cmp c1 (cnHI hi hj),
    restrictArr_unpack (w' := 6) c2 delta_lt (by rw [delta_len]; decide), delta_len, R_eq hi hj hk]

theorem tabs_eq : hfTEnum32.tabs =
    Array.ofFn (n := HeT32.N) fun i => unpack 32 6 (HeT32.T i.val) := by
  have P := CertificateChecks.KernelLC.HeFix2329.pinT
  have hs := P.size
  have hb := P.bind
  rw [Array.toArray_toList] at hs hb
  exact (CFSG.KC.LocalComp.Pin.enumBFS_of_bfsK hs hb P.ok (by decide)).2

theorem out_notIn {X : Nat} (h : outK X = true) :
    notInOK (Array.ofFn (n := HeT32.N) fun i => unpack 32 6 (HeT32.T i.val))
      (unpack 32 6 X) = true := by
  have hc : ∀ i < HeT32.N, canonK 32 6 (mask 6) (32 * 6) (HeT32.T i) = true := fun i hi =>
    (CFSG.KC.HeFixKSnd.pin_pts_PP CertificateChecks.KernelLC.HeFix2329.pinT i hi).1
  unfold outK at h
  rw [Bool.not_eq_true'] at h
  obtain ⟨x, hx, hpx⟩ := allN_false h
  have hge : ¬ pg 6 (mask 6) X x < 32 := fun hl => by
    rw [Nat.blt_eq.mpr hl] at hpx
    exact absurd hpx (by decide)
  unfold notInOK allBelow
  rw [List.all_eq_true]
  intro k hk
  rw [List.mem_range, Array.size_ofFn] at hk
  rw [ofFn_get _ hk, Bool.not_eq_true']
  apply beq_false_of_ne
  intro e
  have e2 := congrArg (fun t : Tab => t[x]!) e
  simp only at e2
  rw [CFSG.KS.MaxD2.get_u hx, CFSG.KS.MaxD2.get_u hx] at e2
  exact hge (e2 ▸ CFSG.KS.MaxD2.canon_lt (hc k hk) hx)

theorem kN_all {i : Nat} (hi : i < 8) : nK i = true := by
  interval_cases i
  exacts [kN0, kN1, kN2, kN3, kN4, kN5, kN6, kN7]

theorem notIn {i j : Nat} (hi : i < 8) (hj : j < 8) (hij : i ≠ j) :
    ∃ k < 5, notInOK hfTEnum32.tabs (hfRes (cj i j k)) = true := by
  have g := allN_spec (kN_all hi) j hj
  have hb : Nat.beq i j = false := by
    cases e : Nat.beq i j
    · rfl
    · exact absurd (Nat.eq_of_beq_eq_true e) hij
  rw [hb, Bool.false_or, Bool.not_eq_true'] at g
  obtain ⟨k, hk, hf'⟩ := allN_false g
  have hf : (outK (R i j k) || notInK 32 6 HeT32.N HeT32.T (R i j k)) = true := by
    rw [Bool.not_eq_false'] at hf'
    exact hf'
  refine ⟨k, hk, ?_⟩
  rw [tabs_eq, res_eq hi hj hk]
  rcases Bool.or_eq_true_iff.1 hf with h | h
  · exact out_notIn h
  · exact CFSG.KC.LocalComp.Pin.notInOK_of_K rfl h

theorem check : (∀ w ∈ words, ∀ j ∈ w, j < 9) ∧
    (∀ i < 8, (wti i).size = 8330 ∧ comp 8330 (wti i) (wt i) = idTab 8330) ∧
    (∀ i < 8, ∀ j < 8, (hTi i j).size = 8330 ∧ comp 8330 (hTi i j) (hT i j) = idTab 8330) ∧
    ∀ i < 8, ∀ j < 8, i ≠ j → ∃ k < 5, notInOK hfTEnum32.tabs (hfRes (cj i j k)) = true := by
  refine ⟨letters, fun i hi => ⟨?_, ?_⟩, fun i hi j hj => ⟨?_, ?_⟩,
    fun i hi j hj hij => notIn hi hj hij⟩
  · rw [wti_eq hi]
    exact CFSG.KS.MaxD2.size_u _
  · rw [wti_eq hi, (wt_eq hi).1]
    exact CFSG.KS.MaxD2.inv_comp (wparts.2 i hi)
  · rw [hTi_eq hi hj]
    exact CFSG.KS.MaxD2.size_u _
  · rw [hTi_eq hi hj, (hT_eq hi hj).1]
    exact CFSG.KS.MaxD2.inv_comp (hparts hi hj)

end CertificateChecks.KernelLC.HeNorm

end
