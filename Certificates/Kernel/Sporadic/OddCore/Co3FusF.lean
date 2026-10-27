module

public import Certificates.Kernel.Sporadic.OddCore.Co3FusE
public import Certificates.Kernel.Sporadic.OddCore.MulHGlue
public import Certificates.Kernel.Sporadic.OddCore.PEnumGlue3
public import Certificates.Kernel.Sporadic.OddCore.Glue
public import CFSG.Certificates.Kernel.Misc.PairCountSound
public import CFSG.Certificates.Kernel.Spor.SiftRSound
import CFSG.Certificates.Kernel.Common.Harness
import Mathlib.Tactic.IntervalCases
public import CFSG.Certificates.Kernel.Spor.RawSlSound
public import CFSG.Sporadic.SmallOddCore.ClassSimple

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSpor.Co3Fus

open CFSG.Sporadic.SmallOddCore CFSG.Sporadic.SmallOddCore.Native CFSG.Sporadic.Th.Native
open CFSG.Sporadic.Schreier.Native CFSG.Sporadic.Schreier.Co3 CFSG.KC.Enum CFSG.KS CFSG.KS.Raw
open CFSG.KS.Prim CFSG.KS.PEnum CFSG.KS.MulH CFSG.KC.BfsPin CFSG.Monster.B.Co2.Native

theorem base : szOK 276 9 = true ∧ canonK 276 9 (mask 9) (276 * 9) idK = true ∧
    CFSG.KS.Prim.idK 276 9 (mask 9) = true ∧ canonK 276 9 (mask 9) (276 * 9) Co3Z = true ∧
    canonK 276 9 (mask 9) (276 * 9) Co3Tt = true ∧ Nat.beq Co3E.cnt 1024 = true ∧
    penumHdK idK Co3E.cnt 2000 Co3E.T Co3E.PL = true ∧
    allN 8 (fun j => bAnd(Nat.beq (Co3E.GI j) (Co3T.S j), bAnd(Nat.beq (Co3E.G j) idK,
      bAnd(canonK 276 9 (mask 9) (276 * 9) (Co3T.S j),
        canonK 276 9 (mask 9) (276 * 9) (Co3T.SI j))))) = true := by
  simpa only [bAnd_iff] using base_ok

theorem gen_ok {j : Nat} (hj : j < 8) : Co3E.GI j = Co3T.S j ∧ Co3E.G j = pidn 276 9 ∧
    canonK 276 9 (mask 9) (276 * 9) (Co3T.S j) = true ∧
    canonK 276 9 (mask 9) (276 * 9) (Co3T.SI j) = true := by
  obtain ⟨h1, h2, h3, h4⟩ := (by simpa only [bAnd_iff] using allN_spec base.2.2.2.2.2.2.2 j hj :
    Nat.beq (Co3E.GI j) (Co3T.S j) = true ∧ Nat.beq (Co3E.G j) idK = true ∧
      canonK 276 9 (mask 9) (276 * 9) (Co3T.S j) = true ∧
      canonK 276 9 (mask 9) (276 * 9) (Co3T.SI j) = true)
  exact ⟨Nat.eq_of_beq_eq_true h1, Nat.eq_of_beq_eq_true h2, h3, h4⟩

theorem hid : idT 276 = tabT (unpack 276 9 (pidn 276 9)) := by
  rw [idT_tabT, idK_sound base.2.2.1]

theorem hcnt : Co3E.cnt = 1024 := Nat.eq_of_beq_eq_true base.2.2.2.2.2.1

theorem t_tabs : TabsOK 276 9 8 Co3T.S co3TTbls := by
  have hs : co3TArrs.size = 10 := Co3T.binds.2.2.2.1
  refine ⟨by simp [co3TTbls, hs], fun j hj => ⟨?_, (gen_ok hj).2.2.1⟩⟩
  rw [getElem!_pos _ j (by simp [co3TTbls, hs]; omega)]
  simp only [co3TTbls, Array.getElem_map, Array.getElem_extract, Nat.zero_add]
  rw [← getElem!_pos co3TArrs j (by omega), Co3T.arr_eq j (by omega)]
  rfl

theorem t_invs : ∀ j < 8, invEqK 276 9 (mask 9) (276 * 9) (Co3T.S j) (Co3T.SI j) = true ∧
    canonK 276 9 (mask 9) (276 * 9) (Co3T.SI j) = true :=
  fun j hj => ⟨allN_spec Co3T.perm j (by omega), (gen_ok hj).2.2.2⟩

theorem e_tabs : TabsOK 276 9 8 Co3E.GI co3TTbls := TabsOK_congr (fun _ hj => (gen_ok hj).1) t_tabs

theorem cover {L N : Nat} {P : Nat → Prop} (hL : 0 < L)
    (h : ∀ s < N, ∀ i, L * s ≤ i → i < L * s + L → P i) : ∀ i < L * N, P i := by
  intro i hi
  refine h (i / L) (Nat.div_lt_of_lt_mul hi) i (Nat.mul_div_le i L) ?_
  have := Nat.lt_mul_div_succ i hL
  rw [Nat.mul_add, Nat.mul_one] at this
  exact this

theorem e_pe : ∀ i < Co3E.cnt, penumPtK 276 9 (mask 9) (276 * 9) true Co3E.G Co3E.GI 8 Co3E.cnt
    Co3E.T Co3E.PL Co3E.POS Co3E.SRT Co3E.SRI i = true := by
  rw [hcnt]
  refine cover (L := 128) (N := 8) (by norm_num) fun s hs i h1 h2 => ?_
  have hi : i < Co3E.cnt := by rw [hcnt]; omega
  interval_cases s
  · exact penumSl_spec eE0 i h1 h2 hi
  · exact penumSl_spec eE1 i h1 h2 hi
  · exact penumSl_spec eE2 i h1 h2 hi
  · exact penumSl_spec eE3 i h1 h2 hi
  · exact penumSl_spec eE4 i h1 h2 hi
  · exact penumSl_spec eE5 i h1 h2 hi
  · exact penumSl_spec eE6 i h1 h2 hi
  · exact penumSl_spec eE7 i h1 h2 hi

theorem e_hs : ∀ i < Co3E.cnt, hsortPtK 276 9 (mask 9) Co3E.cnt Co3E.T Co3E.HS Co3E.HSI i =
    true := by
  rw [hcnt]
  refine cover (L := 256) (N := 4) (by norm_num) fun s hs i h1 h2 => ?_
  have hi : i < Co3E.cnt := by rw [hcnt]; omega
  interval_cases s
  · exact slK_spec eH0 i h1 h2 hi
  · exact slK_spec eH1 i h1 h2 hi
  · exact slK_spec eH2 i h1 h2 hi
  · exact slK_spec eH3 i h1 h2 hi

theorem e_cl : ∀ c < Co3E.cnt * (8 + 8), findPtK Co3E.cnt Co3E.T
    (prodQK 276 9 (mask 9) (8 + 8) Co3E.T (bothK 8 Co3T.S Co3T.SI)) Co3ECl c = true := by
  have hc : Co3E.cnt * (8 + 8) = 2048 * 8 := by rw [hcnt]
  rw [hc]
  refine cover (L := 2048) (N := 8) (by norm_num) fun s hs i h1 h2 => ?_
  have hi : i < Nat.mul Co3E.cnt 16 := by
    change i < Co3E.cnt * 16
    rw [hcnt]
    omega
  interval_cases s
  · exact slK_spec eCl0 i h1 h2 hi
  · exact slK_spec eCl1 i h1 h2 hi
  · exact slK_spec eCl2 i h1 h2 hi
  · exact slK_spec eCl3 i h1 h2 hi
  · exact slK_spec eCl4 i h1 h2 hi
  · exact slK_spec eCl5 i h1 h2 hi
  · exact slK_spec eCl6 i h1 h2 hi
  · exact slK_spec eCl7 i h1 h2 hi

theorem e_canon : ∀ i < Co3E.cnt, canonK 276 9 (mask 9) (276 * 9) (Co3E.T i) = true :=
  fun i hi => penumPt_canon (e_pe i hi)

@[expose] noncomputable def ER : Array Table × Array Nat × Array Nat :=
  hRec 276 9 Co3E.cnt Co3E.T Co3E.PL

theorem e_sound : mulClosureH 276 co3TTbls 2000 = ER ∧
    mulTreeOK 276 co3TTbls ER.1 ER.2.1 ER.2.2 = true ∧ hkeysDistinct 276 ER.1.toList = true :=
  mulH_sound base.1 (fun _ hj => (gen_ok hj).2.1) e_tabs base.2.2.2.2.2.2.1 e_pe e_hs

theorem ER_get {i : Nat} (hi : i < Co3E.cnt) : ER.1[i]! = tabT (unpack 276 9 (Co3E.T i)) :=
  hRec_get hi

theorem gens_ok : co3TTbls.all (fun g => permOK 276 g && invOK 276 g (invT 276 g)) = true := by
  rw [Array.all_eq_true]
  intro j hj
  have hj' : j < 8 := by rw [← t_tabs.1]; exact hj
  obtain ⟨hg, hc⟩ := t_tabs.2 j hj'
  rw [← getElem!_pos co3TTbls j hj, hg, invT_unpack (by norm_num) (t_invs j hj').1]
  simp only [Bool.and_eq_true]
  exact ⟨permOK_unpack hc (t_invs j hj').1, invOK_unpack hc (t_invs j hj').2 (t_invs j hj').1⟩

theorem wit_ok {k : Nat} (hk : k < 191) : witK k = true := by
  rcases Nat.lt_or_ge k 96 with h | h
  · exact slK_spec wit0 k (Nat.zero_le _) (by omega) hk
  · exact slK_spec wit1 k h (by omega) hk

theorem wit_facts {k : Nat} (hk : k < 191) :
    canonK 276 9 (mask 9) (276 * 9) (Co3FT.F k) = true ∧
      invEqK 276 9 (mask 9) (276 * 9) (Co3FT.F k) (Co3FI k) = true ∧
      canonK 276 9 (mask 9) (276 * 9) (Co3FI k) = true ∧ Co3Text.hiOK (Co3FT.F k) = true ∧
      Co3C.sift (Co3FT.F k) = true := by
  simpa only [witK, bAnd_iff] using wit_ok hk

theorem fus_tab {k : Nat} (hk : k < 191) : co3FusionTbl k = tabT (unpack 276 9 (Co3FT.F k)) := by
  have h := CFSG.KC.Misc.HexFlat.hexT_sound Co3FT.all (by norm_num) k hk
  rw [← Co3FT.eq] at h
  rw [← h, tabT_natArr]
  rfl

theorem wits_ok : co3FusionWits.all (fun w => permOK 276 w.1 && invOK 276 w.1 (invT 276 w.1) &&
    co3Sift w.1) = true := by
  unfold co3FusionWits
  rw [List.all_map, List.all_eq_true]
  intro k hk
  have hk' := List.mem_range.1 hk
  obtain ⟨h1, h2, h3, h4, h5⟩ := wit_facts hk'
  simp only [Function.comp, Bool.and_eq_true]
  rw [fus_tab hk', invT_unpack (by norm_num) h2]
  refine ⟨⟨permOK_unpack h1 h2, invOK_unpack h1 h3 h2⟩, ?_⟩
  unfold co3Sift
  rw [natArr_tabT h1]
  exact siftK_soundR Co3C.binds Co3C.perm Co3C.hl rfl (Nat.eq_of_beq_eq_true h4)
    (range_of_canonK h1) h5

theorem hidc : canonK 276 9 (mask 9) (276 * 9) (pidn 276 9) = true := base.2.1

theorem invoOK_eq {n : Nat} (hn : n < 2 ^ 32) (P : Table) :
    CFSG.Sporadic.Th.Native.invoOK n P = tblEq n (compT n P P) (idT n) := by
  unfold CFSG.Sporadic.Th.Native.invoOK tblEq
  rw [Bool.eq_iff_iff, CFSG.KS.TW.allIn_iff, CFSG.KS.TW.allIn_iff]
  refine forall_congr' fun i => imp_congr_right fun hi => ?_
  have h1 : ap (compT n P P) i = ap P (ap P i) := by
    unfold ap compT
    rw [getElem!_pos _ i (by simpa using hi), Array.getElem_ofFn]
  have h2 : ap (idT n) i = i := by
    unfold ap idT
    rw [getElem!_pos _ i (by simpa using hi), Array.getElem_ofFn, UInt32.toNat_ofNat',
      Nat.mod_eq_of_lt (by omega)]
  rw [h1, h2]

theorem involOK_unpack {X : Nat} (hX : canonK 276 9 (mask 9) (276 * 9) X = true) :
    involOK 276 (tabT (unpack 276 9 X)) = involK X := by
  unfold involOK
  rw [invoOK_eq (by norm_num), compT_unpack hX hX, hid, tblEq_unpack (canonK_pcomp hX hX) hidc,
    tblEq_unpack hX hidc]
  unfold involK pc idK
  cases Nat.beq (pcomp 276 9 (mask 9) X X) (pidn 276 9) <;> cases Nat.beq X (pidn 276 9) <;> rfl

theorem filter_size (A : Array Table) (p : Table → Bool) :
    (A.filter p).size = A.toList.countP p := by
  rw [← Array.length_toList, Array.toList_filter, List.countP_eq_length_filter]

theorem fl_eq {k : Nat} (hk : k < 191) : fl k = if co3FusionFlags.getD k false then 1 else 0 := by
  have h := Nat.eq_of_beq_eq_true (allN_spec flags_ok k hk)
  rw [h]
  cases co3FusionFlags.getD k false <;> rfl

theorem tgt_tab {k : Nat} (hk : k < 191) :
    (if co3FusionFlags.getD k false then co3ZTbl else co3TtTbl) = tabT (unpack 276 9 (tgt (fl k))) ∧
      canonK 276 9 (mask 9) (276 * 9) (tgt (fl k)) = true := by
  rw [fl_eq hk]
  cases co3FusionFlags.getD k false
  · refine ⟨?_, base.2.2.2.2.1⟩
    unfold co3TtTbl
    rw [CertificateChecks.KernelSpor.Co3Single.tt_eq]
    rfl
  · refine ⟨?_, base.2.2.2.1⟩
    unfold co3ZTbl
    rw [CertificateChecks.KernelSpor.Co3Single.z_eq]
    rfl

theorem fuses_eq {k S : Nat} (hk : k < 191) (hS : canonK 276 9 (mask 9) (276 * 9) S = true) :
    co3FusesTo (tabT (unpack 276 9 S)) (co3FusionTbl k, co3FusionFlags.getD k false) =
      fusesK k S := by
  obtain ⟨h1, h2, h3, -, -⟩ := wit_facts hk
  obtain ⟨ht, htc⟩ := tgt_tab hk
  unfold co3FusesTo
  simp only []
  rw [fus_tab hk, invT_unpack (by norm_num) h2, conjT_unpack h1 h3 hS, ht,
    tblEq_unpack (canonK_pcomp (canonK_pcomp h1 hS) h3) htc]
  rfl

theorem pg_lt {X x : Nat} (hX : canonK 276 9 (mask 9) (276 * 9) X = true) (hx : x < 276) :
    pg 9 (mask 9) X x < 276 := by
  unfold canonK at hX
  simp only [bAnd_iff] at hX
  exact Nat.le_of_ble_eq_true (allN_spec hX.2.2 x hx)

theorem pg_pcomp {p q x : Nat} (hp : canonK 276 9 (mask 9) (276 * 9) p = true)
    (hq : canonK 276 9 (mask 9) (276 * 9) q = true) (hx : x < 276) :
    pg 9 (mask 9) (pcomp 276 9 (mask 9) p q) x = pg 9 (mask 9) p (pg 9 (mask 9) q x) := by
  have h := congrArg (·[x]!) (compA_unpack hp hq)
  rw [CFSG.KC.Misc.PairCount.unpack_get hx, OddCore.compA_get hx,
    CFSG.KC.Misc.PairCount.unpack_get hx, CFSG.KC.Misc.PairCount.unpack_get (pg_lt hq hx)] at h
  exact h.symm

theorem miss_false {k S x : Nat} (hk : k < 191) (hS : canonK 276 9 (mask 9) (276 * 9) S = true)
    (h : missK k S x = true) : fusesK k S = false := by
  obtain ⟨h1, -, h3, -, -⟩ := wit_facts hk
  unfold missK at h
  obtain ⟨hx, hne⟩ := (bAnd_iff _ _).1 h
  have hx' : x < 276 := Nat.le_of_ble_eq_true hx
  cases e : fusesK k S
  · rfl
  · unfold fusesK pc at e
    have e' := congrArg (pg 9 (mask 9) · x) (Nat.eq_of_beq_eq_true e)
    rw [pg_pcomp (canonK_pcomp h1 hS) h3 hx', pg_pcomp h1 hS (pg_lt h3 hx')] at e'
    unfold pt at hne
    rw [e'] at hne
    simp at hne

theorem fus_facts {i : Nat} (hi : i < Co3E.cnt) (hinv : involK (Co3E.T i) = true) :
    r32 Co3WJ i < 191 ∧ fusesK (r32 Co3WJ i) (Co3E.T i) = true ∧
      ∀ j' < 191, fl j' ≠ fl (r32 Co3WJ i) → fusesK j' (Co3E.T i) = false := by
  have h : fusPtK i = true := by
    rcases Nat.lt_or_ge i 256 with a | a
    · exact slK_spec fus0 i (Nat.zero_le _) (by omega) hi
    rcases Nat.lt_or_ge i 512 with b | b
    · exact slK_spec fus1 i a (by omega) hi
    rcases Nat.lt_or_ge i 768 with c | c
    · exact slK_spec fus2 i b (by omega) hi
    · exact slK_spec fus3 i c (by rw [hcnt] at hi; omega) hi
  unfold fusPtK at h
  rw [strictB_eq'', hinv] at h
  change strictB (r32 Co3WJ i) _ = true at h
  rw [strictB_eq'', strictB_eq''] at h
  obtain ⟨hj, hp, hf, hall⟩ := (by simpa only [bAnd_iff] using h :
    Nat.blt (r32 Co3WJ i) 191 = true ∧ Nat.blt (r32 Co3PI i) 191 = true ∧
      fusesK (r32 Co3WJ i) (Co3E.T i) = true ∧ allN 191 (fun j' =>
        bIf(Nat.beq (fl j') (fl (r32 Co3WJ i)), true,
          missK j' (Co3E.T i) (r32 Co3PTS (Nat.add (Nat.mul (r32 Co3PI i) 191) j')))) = true)
  refine ⟨Nat.le_of_ble_eq_true hj, hf, fun j' hj' hne => ?_⟩
  have hm := allN_spec hall j' hj'
  have hb : Nat.beq (fl j') (fl (r32 Co3WJ i)) = false := by
    cases e : Nat.beq (fl j') (fl (r32 Co3WJ i))
    · rfl
    · exact absurd (Nat.eq_of_beq_eq_true e) hne
  rw [hb] at hm
  exact miss_false hj' (e_canon i hi) hm

theorem wit_mem {k : Nat} (hk : k < 191) :
    (co3FusionTbl k, co3FusionFlags.getD k false) ∈ co3FusionWits :=
  List.mem_map.2 ⟨k, List.mem_range.2 hk, rfl⟩

theorem wit_of {w : Table × Bool} (hw : w ∈ co3FusionWits) :
    ∃ k < 191, w = (co3FusionTbl k, co3FusionFlags.getD k false) := by
  obtain ⟨k, hk, rfl⟩ := List.mem_map.1 hw
  exact ⟨k, List.mem_range.1 hk, rfl⟩

theorem fl01 {k : Nat} (hk : k < 191) : fl k = 1 ↔ co3FusionFlags.getD k false = true := by
  rw [fl_eq hk]
  cases co3FusionFlags.getD k false <;> simp

theorem anyZ {i : Nat} (hi : i < Co3E.cnt) (hinv : involK (Co3E.T i) = true) :
    (co3FusionWits.any fun w => w.2 && co3FusesTo (tabT (unpack 276 9 (Co3E.T i))) w) =
      Nat.beq (fl (r32 Co3WJ i)) 1 := by
  obtain ⟨hj, hf, hno⟩ := fus_facts hi hinv
  rw [Bool.eq_iff_iff, List.any_eq_true, Nat.beq_eq]
  constructor
  · rintro ⟨w, hw, h⟩
    obtain ⟨k, hk, rfl⟩ := wit_of hw
    simp only [Bool.and_eq_true] at h
    rw [fuses_eq hk (e_canon i hi)] at h
    by_contra hne
    have hk1 : fl k = 1 := (fl01 hk).2 h.1
    rw [hno k hk (by rw [hk1]; exact Ne.symm hne)] at h
    exact absurd h.2 (by decide)
  · intro h1
    refine ⟨_, wit_mem hj, ?_⟩
    simp only [Bool.and_eq_true]
    rw [fuses_eq hj (e_canon i hi)]
    exact ⟨(fl01 hj).1 h1, hf⟩

theorem anyT {i : Nat} (hi : i < Co3E.cnt) (hinv : involK (Co3E.T i) = true) :
    (co3FusionWits.any fun w => !w.2 && co3FusesTo (tabT (unpack 276 9 (Co3E.T i))) w) =
      bIf(Nat.beq (fl (r32 Co3WJ i)) 1, false, true) := by
  obtain ⟨hj, hf, hno⟩ := fus_facts hi hinv
  have h0 : ∀ k < 191, fl k ≠ 1 → fl k = 0 := by
    intro k hk h
    rw [fl_eq hk] at h ⊢
    cases e : co3FusionFlags.getD k false
    · rfl
    · rw [e] at h
      exact absurd rfl h
  rw [Bool.eq_iff_iff, List.any_eq_true]
  constructor
  · rintro ⟨w, hw, h⟩
    obtain ⟨k, hk, rfl⟩ := wit_of hw
    simp only [Bool.and_eq_true, Bool.not_eq_true'] at h
    rw [fuses_eq hk (e_canon i hi)] at h
    have hk0 : fl k ≠ 1 := fun e => by rw [(fl01 hk).1 e] at h; exact absurd h.1 (by decide)
    cases e : Nat.beq (fl (r32 Co3WJ i)) 1
    · rfl
    · have hw1 := Nat.eq_of_beq_eq_true e
      rw [hno k hk (by rw [hw1]; exact hk0)] at h
      exact absurd h.2 (by decide)
  · intro h1
    refine ⟨_, wit_mem hj, ?_⟩
    simp only [Bool.and_eq_true, Bool.not_eq_true']
    rw [fuses_eq hj (e_canon i hi)]
    refine ⟨?_, hf⟩
    cases e : Nat.beq (fl (r32 Co3WJ i)) 1
    · have hne : fl (r32 Co3WJ i) ≠ 1 := fun h => by rw [h] at e; exact absurd e (by decide)
      cases e2 : co3FusionFlags.getD (r32 Co3WJ i) false
      · rfl
      · exact absurd ((fl01 hj).2 e2) hne
    · rw [e] at h1
      exact absurd h1 (by decide)

theorem ER_mem {x : Table} (hx : x ∈ ER.1) :
    ∃ i < Co3E.cnt, x = tabT (unpack 276 9 (Co3E.T i)) := by
  rw [Array.mem_iff_getElem] at hx
  obtain ⟨i, hi, rfl⟩ := hx
  have hi' : i < Co3E.cnt := by simpa [ER, hRec] using hi
  exact ⟨i, hi', by simp [ER, hRec]⟩

theorem inv_all : (ER.1.filter (involOK 276)).all (fun s => co3FusionWits.any (co3FusesTo s)) =
    true := by
  rw [Array.all_eq_true_iff_forall_mem]
  intro s hs
  rw [Array.mem_filter] at hs
  obtain ⟨hm, hinv⟩ := hs
  obtain ⟨i, hi, rfl⟩ := ER_mem hm
  rw [involOK_unpack (e_canon i hi)] at hinv
  obtain ⟨hj, hf, -⟩ := fus_facts hi hinv
  rw [List.any_eq_true]
  exact ⟨_, wit_mem hj, by rw [fuses_eq hj (e_canon i hi)]; exact hf⟩

theorem cnt_of {q : Table → Bool} {q' : Nat → Bool}
    (h : ∀ i < Co3E.cnt, q (tabT (unpack 276 9 (Co3E.T i))) = q' i) :
    (ER.1.filter q).size = cntBelowK Co3E.cnt q' 16 := by
  rw [filter_size]
  exact countP_hRec (by rw [hcnt]) h

theorem cnts : cntBelowK Co3E.cnt (fun i => strictB (Co3E.T i) involK) 16 = 191 ∧
    cntBelowK Co3E.cnt (fun i => bAnd(strictB (Co3E.T i) involK,
      Nat.beq (fl (r32 Co3WJ i)) 1)) 16 = 55 ∧
    cntBelowK Co3E.cnt (fun i => bAnd(strictB (Co3E.T i) involK,
      bIf(Nat.beq (fl (r32 Co3WJ i)) 1, false, true))) 16 = 136 := by
  obtain ⟨h1, h2, h3⟩ := (by simpa only [bAnd_iff] using counts :
    Nat.beq (cntBelowK Co3E.cnt (fun i => strictB (Co3E.T i) involK) 16) 191 = true ∧
    Nat.beq (cntBelowK Co3E.cnt (fun i => bAnd(strictB (Co3E.T i) involK,
      Nat.beq (fl (r32 Co3WJ i)) 1)) 16) 55 = true ∧
    Nat.beq (cntBelowK Co3E.cnt (fun i => bAnd(strictB (Co3E.T i) involK,
      bIf(Nat.beq (fl (r32 Co3WJ i)) 1, false, true))) 16) 136 = true)
  exact ⟨Nat.eq_of_beq_eq_true h1, Nat.eq_of_beq_eq_true h2, Nat.eq_of_beq_eq_true h3⟩

theorem cntI : (ER.1.filter (involOK 276)).size = 191 := by
  rw [cnt_of (q' := fun i => strictB (Co3E.T i) involK)
    (fun i hi => by rw [strictB_eq'', involOK_unpack (e_canon i hi)]), cnts.1]

theorem cntZ : ((ER.1.filter (involOK 276)).filter fun s =>
    co3FusionWits.any fun w => w.2 && co3FusesTo s w).size = 55 := by
  rw [Array.filter_filter, cnt_of (q' := fun i => bAnd(strictB (Co3E.T i) involK,
    Nat.beq (fl (r32 Co3WJ i)) 1)) (fun i hi => ?_), cnts.2.1]
  rw [strictB_eq'', involOK_unpack (e_canon i hi)]
  cases h : involK (Co3E.T i)
  · simp only [Bool.and_false]
  · rw [anyZ hi h]
    simp only [Bool.and_true]

theorem cntT : ((ER.1.filter (involOK 276)).filter fun s =>
    co3FusionWits.any fun w => !w.2 && co3FusesTo s w).size = 136 := by
  rw [Array.filter_filter, cnt_of (q' := fun i => bAnd(strictB (Co3E.T i) involK,
    bIf(Nat.beq (fl (r32 Co3WJ i)) 1, false, true))) (fun i hi => ?_), cnts.2.2]
  rw [strictB_eq'', involOK_unpack (e_canon i hi)]
  cases h : involK (Co3E.T i)
  · simp only [Bool.and_false]
  · rw [anyT hi h]
    simp only [Bool.and_true]

theorem facts2271 : co3FusionOK = true := by
  unfold co3FusionOK
  simp only [Bool.and_eq_true, beq_iff_eq]
  rw [e_sound.1]
  refine ⟨⟨⟨⟨⟨⟨⟨⟨⟨gens_ok, e_sound.2.1⟩, closedOK_of e_canon (TabsOK_both t_tabs t_invs) e_cl⟩,
    e_sound.2.2⟩, ?_⟩, wits_ok⟩, cntI⟩, inv_all⟩, cntZ⟩, cntT⟩
  rw [ER, hRec_size, hcnt]

end CertificateChecks.KernelSpor.Co3Fus

end
