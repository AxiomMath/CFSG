module

public import Certificates.Kernel.Sporadic.OddCore.McLNcl
public import Certificates.Kernel.Sporadic.OddCore.PEnumGlue3
public import CFSG.Sporadic.SmallOddCore.SylowSimple
public import CFSG.Certificates.Kernel.Misc.PairCountSound
import CFSG.Certificates.Kernel.Common.Harness
import Mathlib.Tactic.IntervalCases

public section

namespace CertificateChecks.KernelSpor.McL2287

open CFSG.PSL3Four.Native CFSG.Sporadic.SmallOddCore CFSG.Sporadic.SuzOddCore CFSG.KC.Enum CFSG.KS
open CFSG.KS.Raw CFSG.KS.Prim CFSG.KS.PEnum CFSG.KC.BfsPin CFSG.Monster.B.Co2.Native
open CFSG.KS.Mathieu CFSG.KC.Misc.HexAt CFSG.Sporadic.SmallOddCore.Native

theorem idc : canonK 35 6 (mask 6) (35 * 6) (pidn 35 6) = true ∧ idK 35 6 (mask 6) = true ∧
    szOK 35 6 = true := by
  simpa only [bAnd_iff] using id_ok

theorem idTab_eq : idTab 35 = unpack 35 6 (pidn 35 6) := (idK_sound idc.2.1).symm

theorem rec_get35 {cnt i : Nat} {T PL : Nat → Nat} (hi : i < cnt) :
    (penumRec 35 6 cnt T PL).tabs[i]! = unpack 35 6 (T i) := by
  rw [getElem!_pos _ i (by simp only [penumRec, Array.size_ofFn]; exact hi)]
  simp only [penumRec, Array.getElem_ofFn]

theorem comp35 {p q : Nat} (hp : canonK 35 6 (mask 6) (35 * 6) p = true)
    (hq : canonK 35 6 (mask 6) (35 * 6) q = true) :
    comp 35 (unpack 35 6 p) (unpack 35 6 q) = unpack 35 6 (pcomp 35 6 (mask 6) p q) :=
  compA_unpack hp hq

theorem cent_eq {k : Nat} (hk : k < 30) : natArr (mclCentTbl k) = unpack 275 9 (McLCT.F k) := by
  have h := CFSG.KC.Misc.HexFlat.hexT_sound McLCT.all (by norm_num) k hk
  rw [← McLCT.eq] at h
  exact h

theorem cent_perm {k j : Nat} (hk : k < 30)
    (h : invEqK 275 9 (mask 9) (275 * 9) (McLCT.F k) (McLCI j) = true) :
    CFSG.Sporadic.SmallOddCore.permOK 275 (mclCentTbl k) = true := by
  obtain ⟨h1, h2⟩ := invEqK_sound h
  unfold CFSG.Sporadic.SmallOddCore.permOK
  rw [cent_eq hk, h1]
  exact h2

theorem fix_eq : mclFix = fixL := by
  rw [← sel_spec fix_sel]
  unfold mclFix fixedList mclT0Arr
  apply List.filter_congr
  intro x hx
  have hx' : x < 275 := List.mem_range.1 hx
  rw [cent_eq (by norm_num), CFSG.KC.Misc.PairCount.unpack_get hx']
  cases h : Nat.beq (pg 9 (mask 9) (McLCT.F 4) x) x
  · have : pg 9 (mask 9) (McLCT.F 4) x ≠ x := fun e => by simp [e] at h
    simp [this]
  · simp [Nat.eq_of_beq_eq_true h]

theorem fixL_nodup : fixL.Nodup := by
  rw [← sel_spec fix_sel]
  exact List.nodup_range.filter _

theorem fixL_len : fixL.length = 35 := rfl

theorem fixL_mem_lt {x : Nat} (hx : x ∈ fixL) : x < 275 := by
  rw [← sel_spec fix_sel] at hx
  exact List.mem_range.1 (List.mem_filter.1 hx).1

theorem fixL_lt {a : Nat} (ha : a < 35) : fixL[a]'(by rw [fixL_len]; exact ha) < 275 :=
  fixL_mem_lt (List.getElem_mem _)

theorem xg_facts {k : Nat} (hk : k < 2) : canonK 35 6 (mask 6) (35 * 6) (MXE.G k) = true ∧
    ∀ a < 35, pg 9 (mask 9) (McLCT.F (Nat.add k 5)) (nget fixL a) =
      nget fixL (pg 6 (mask 6) (MXE.G k) a) := by
  obtain ⟨h1, h2⟩ := (bAnd_iff _ _).1 (allN_spec xg_ok k hk)
  exact ⟨h1, fun a ha => Nat.eq_of_beq_eq_true (allN_spec h2 a ha)⟩

theorem canon_lt {p a : Nat} (hp : canonK 35 6 (mask 6) (35 * 6) p = true) (ha : a < 35) :
    pg 6 (mask 6) p a < 35 := by
  have h' : bAnd(szOK 35 6, bAnd(Nat.beq (Nat.shiftRight p (35 * 6)) (nat_lit 0),
      allN 35 (fun i => Nat.blt (pg 6 (mask 6) p i) 35))) = true := hp
  simp only [bAnd_iff] at h'
  exact Eq.mp Nat.blt_eq (allN_spec h'.2.2 a ha)

theorem xgens_get {k : Nat} (hk : k < 2) : mclXGens[k]! = unpack 35 6 (MXE.G k) := by
  obtain ⟨hc, hr⟩ := xg_facts hk
  rw [getElem!_pos mclXGens k (by simp [mclXGens]; omega)]
  simp only [mclXGens, Array.getElem_ofFn]
  rw [fix_eq, cent_eq (by omega)]
  apply Array.ext
  · simp [restrictArr, unpack, fixL_len]
  · intro a h1 _
    have ha : a < 35 := by simpa [restrictArr, fixL_len] using h1
    simp only [restrictArr, List.getElem_toArray, List.getElem_map]
    rw [CFSG.KC.Misc.PairCount.unpack_get (fixL_lt ha)]
    simp only [unpack, Array.getElem_ofFn]
    have e1 := hr a ha
    rw [nget_get fixL (by rw [fixL_len]; exact ha)] at e1
    have hb := canon_lt hc ha
    rw [nget_get fixL (by rw [fixL_len]; exact hb)] at e1
    have e2 : Nat.add k 5 = k + 5 := rfl
    rw [e2] at e1
    rw [e1, fixL_nodup.idxOf_getElem]

theorem xi_facts {k : Nat} (hk : k < 2) :
    invEqK 35 6 (mask 6) (35 * 6) (MXE.G k) (MXI k) = true ∧
      canonK 35 6 (mask 6) (35 * 6) (MXI k) = true ∧
      Nat.beq (pcomp 35 6 (mask 6) (MXI k) (MXE.G k)) (pidn 35 6) = true := by
  simpa only [bAnd_iff] using allN_spec xi_ok k hk

theorem xinvs_get {k : Nat} (hk : k < 2) : mclXInvs[k]! = unpack 35 6 (MXI k) := by
  rw [mclXInvs, getElem!_pos _ k (by simp [mclXGens]; omega), Array.getElem_map,
    ← getElem!_pos mclXGens k (by simp [mclXGens]; omega), xgens_get hk]
  exact (invEqK_sound (xi_facts hk).1).1

theorem g_ok : GensOK 35 6 MXE.k MXE.G mclXGens :=
  ⟨rfl, fun _ hj => ⟨xgens_get hj, (xg_facts hj).1⟩⟩

theorem invs : invsOK 35 mclXGens mclXInvs = true := by
  unfold invsOK
  simp only [Bool.and_eq_true, beq_iff_eq]
  refine ⟨by simp [mclXInvs], ?_⟩
  unfold allBelow
  rw [all_range_iff]
  intro k hk
  have hk2 : k < 2 := by simpa [mclXGens] using hk
  obtain ⟨-, hci, hpi⟩ := xi_facts hk2
  simp only [Bool.and_eq_true, beq_iff_eq]
  rw [xinvs_get hk2, xgens_get hk2]
  refine ⟨unpack_size _ _ _, ?_⟩
  rw [comp35 hci (xg_facts hk2).1, idTab_eq, Nat.eq_of_beq_eq_true hpi]

theorem x_pt {i : Nat} (hi : i < MXE.cnt) : penumPtK 35 6 (mask 6) (35 * 6) false MXE.G MXE.GI
    MXE.k MXE.cnt MXE.T MXE.PL MXE.POS MXE.SRT MXE.SRI i = true := by
  have e : MXE.cnt = 20160 := rfl
  rcases Nat.lt_or_ge i 5040 with h0 | h0
  · exact penumSl_spec x_sl0 i (Nat.zero_le _) (by omega) hi
  rcases Nat.lt_or_ge i 10080 with h1 | h1
  · exact penumSl_spec x_sl1 i h0 (by omega) hi
  rcases Nat.lt_or_ge i 15120 with h2 | h2
  · exact penumSl_spec x_sl2 i h1 (by omega) hi
  · exact penumSl_spec x_sl3 i h2 (by omega) hi

theorem x_enum : mclXEnum = penumRec 35 6 MXE.cnt MXE.T MXE.PL ∧
    enumOK 35 mclXGens (penumRec 35 6 MXE.cnt MXE.T MXE.PL) = true :=
  penumK_left_sound (cap := 20160) idc.2.2 g_ok x_hd (fun _ hi => x_pt hi)

theorem ltAll_spec {b : Nat} : ∀ {w : List Nat}, ltAll b w = true → ∀ j ∈ w, j < b
  | [], _, j, hj => by simp at hj
  | x :: w, h, j, hj => by
    have h' : bAnd(Nat.blt x b, ltAll b w) = true := h
    obtain ⟨h1, h2⟩ := (bAnd_iff _ _).1 h'
    rcases List.mem_cons.1 hj with rfl | hj
    · exact Eq.mp Nat.blt_eq h1
    · exact ltAll_spec h2 j hj

theorem wK_eq {u : List Nat} (hu : ∀ j ∈ u, j < 2) :
    wordTabS 35 mclXGens u = unpack 35 6 (wK u) ∧ canonK 35 6 (mask 6) (35 * 6) (wK u) = true :=
  wordTabK_eq idTab_eq idc.1 u (fun j hj => ⟨xgens_get (hu j hj), (xg_facts (hu j hj)).1⟩)

theorem wKI_eq {u : List Nat} (hu : ∀ j ∈ u, j < 2) :
    wordTabS 35 mclXInvs u = unpack 35 6 (wKI u) ∧ canonK 35 6 (mask 6) (35 * 6) (wKI u) = true :=
  wordTabK_eq idTab_eq idc.1 u (fun j hj => ⟨xinvs_get (hu j hj), (xi_facts (hu j hj)).2.1⟩)

@[expose] noncomputable def nclU (c i : Nat) : List Nat := lget2 nclCW (Nat.add (Nat.mul 5 c) i)

@[expose] noncomputable def nclV (c j : Nat) : List Nat := lget2 nclWW (Nat.add (Nat.mul 2 c) j)

theorem ncl_sound {x c : Nat} (hc : canonK 35 6 (mask 6) (35 * 6) x = true) (h : nclK x c = true) :
    nclWordsOK 35 mclXGens mclXInvs (unpack 35 6 x)
      ((List.range 5).map fun i => (nclU c i, (nclU c i).reverse)) ((List.range 2).map (nclV c)) =
      true := by
  unfold nclK at h
  obtain ⟨hA, hB⟩ := (bAnd_iff _ _).1 h
  have hA' : ∀ i < 5, (∀ j ∈ nclU c i, j < 2) ∧
      pcomp 35 6 (mask 6) (wKI (nclU c i).reverse) (wK (nclU c i)) = pidn 35 6 := by
    intro i hi
    obtain ⟨h1, h2⟩ := (bAnd_iff _ _).1 (allN_spec hA i hi)
    exact ⟨ltAll_spec h1, Nat.eq_of_beq_eq_true h2⟩
  have hB' : ∀ j < 2, ltAll 5 (nclV c j) = true ∧ wordTabK 35 6 (mask 6) (pidn 35 6)
      (fun i => nclY x (nclU c i)) (nclV c j) = MXE.G j := by
    intro j hj
    obtain ⟨h1, h2⟩ := (bAnd_iff _ _).1 (allN_spec hB j hj)
    exact ⟨h1, Nat.eq_of_beq_eq_true h2⟩
  have hr : ∀ i < 5, ∀ j ∈ (nclU c i).reverse, j < 2 :=
    fun i hi j hj => (hA' i hi).1 j (List.mem_reverse.1 hj)
  have hsz : mclXGens.size = 2 := by simp [mclXGens]
  have hisz : mclXInvs.size = 2 := by simp [mclXInvs, mclXGens]
  simp only [nclWordsOK, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq, beq_iff_eq,
    CFSG.ComponentClassification.PSL3Four.allBelow_eq_true]
  refine ⟨fun cc hcc => ?_, fun j hj => ?_⟩
  · obtain ⟨i, hi, rfl⟩ := List.mem_map.1 hcc
    have hi5 := List.mem_range.1 hi
    obtain ⟨hu, he⟩ := hA' i hi5
    refine ⟨⟨fun j hj => hsz ▸ hu j hj, fun j hj => hisz ▸ hr i hi5 j hj⟩, ?_⟩
    obtain ⟨e1, c1⟩ := wK_eq hu
    obtain ⟨e2, c2⟩ := wKI_eq (hr i hi5)
    rw [e1, e2, comp35 c2 c1, he, idTab_eq]
  · have hj2 : j < 2 := hsz ▸ hj
    obtain ⟨hv, hw⟩ := hB' j hj2
    have hWj : ((List.range 2).map (nclV c)).getD j [] = nclV c j := by
      simp [List.getD_eq_getElem?_getD, hj2]
    rw [hWj]
    refine ⟨fun i hi => by simpa using ltAll_spec hv i hi, ?_⟩
    have hS : ∀ i ∈ nclV c j, (nclConjs 35 mclXGens mclXInvs (unpack 35 6 x)
        ((List.range 5).map fun i => (nclU c i, (nclU c i).reverse)))[i]! =
          unpack 35 6 (nclY x (nclU c i)) ∧
        canonK 35 6 (mask 6) (35 * 6) (nclY x (nclU c i)) = true := by
      intro i hi
      have hi5 := ltAll_spec hv i hi
      obtain ⟨e1, c1⟩ := wK_eq (hA' i hi5).1
      obtain ⟨e2, c2⟩ := wKI_eq (hr i hi5)
      have e : (nclConjs 35 mclXGens mclXInvs (unpack 35 6 x)
          ((List.range 5).map fun i => (nclU c i, (nclU c i).reverse)))[i]! =
          comp 35 (comp 35 (wordTabS 35 mclXGens (nclU c i)) (unpack 35 6 x))
            (wordTabS 35 mclXInvs (nclU c i).reverse) := by
        rw [nclConjs, getElem!_pos _ i (by simpa using hi5)]
        simp
      rw [e, e1, e2, comp35 c1 hc, comp35 (canonK_pcomp c1 hc) c2]
      exact ⟨rfl, canonK_pcomp (canonK_pcomp c1 hc) c2⟩
    rw [xgens_get hj2, ← hw]
    exact (wordTabK_eq idTab_eq idc.1 (nclV c j) hS).1

theorem syl_sound {k cnt p : Nat} {G GI T PL POS SRT SRI : Nat → Nat} {I : List Nat}
    {words : List (List Nat)} (hk : words.length = k)
    (hg : allN k (fun j => bAnd(canonK 35 6 (mask 6) (35 * 6) (G j),
      bAnd(ltAll 2 (lget2 words j), Nat.beq (G j) (wK (lget2 words j))))) = true)
    (hh : penumHdK (pidn 35 6) cnt 64 T PL = true)
    (hs : penumSlK 35 6 (mask 6) (35 * 6) false G GI k cnt T PL POS SRT SRI 0 cnt = true)
    (hn : sylK cnt p T I = true) :
    (∀ w ∈ words, ∀ j ∈ w, j < mclXGens.size) ∧
    enumOK 35 (words.map (wordTabS 35 mclXGens)).toArray
      (enumBFS 35 (words.map (wordTabS 35 mclXGens)).toArray 64) = true ∧
    (enumBFS 35 (words.map (wordTabS 35 mclXGens)).toArray 64).tabs.size = cnt ∧
    ∀ q < (enumBFS 35 (words.map (wordTabS 35 mclXGens)).toArray 64).tabs.size,
      (enumBFS 35 (words.map (wordTabS 35 mclXGens)).toArray 64).tabs[q]! = idTab 35 ∨
      wordTabS 35 #[(enumBFS 35 (words.map (wordTabS 35 mclXGens)).toArray 64).tabs[q]!]
        (List.replicate p 0) ≠ idTab 35 ∨
      ∃ cs W, nclWordsOK 35 mclXGens mclXInvs
        (enumBFS 35 (words.map (wordTabS 35 mclXGens)).toArray 64).tabs[q]! cs W = true := by
  have hsz : mclXGens.size = 2 := by simp [mclXGens]
  have hgj : ∀ j < k, canonK 35 6 (mask 6) (35 * 6) (G j) = true ∧
      (∀ i ∈ words.getD j [], i < 2) ∧ G j = wK (words.getD j []) := by
    intro j hj
    obtain ⟨h1, h2⟩ := (bAnd_iff _ _).1 (allN_spec hg j hj)
    obtain ⟨h2, h3⟩ := (bAnd_iff _ _).1 h2
    rw [lget2_eq] at h2 h3
    exact ⟨h1, ltAll_spec h2, Nat.eq_of_beq_eq_true h3⟩
  have hlt : ∀ w ∈ words, ∀ j ∈ w, j < mclXGens.size := by
    intro w hw j hj
    obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hw
    have e : words.getD i [] = words[i] := by simp [List.getD_eq_getElem?_getD, hi]
    exact hsz ▸ (hgj i (hk ▸ hi)).2.1 j (e ▸ hj)
  have hgo : GensOK 35 6 k G (words.map (wordTabS 35 mclXGens)).toArray := by
    refine ⟨by simp [hk], fun j hj => ⟨?_, (hgj j hj).1⟩⟩
    have hj' : j < words.length := hk ▸ hj
    rw [getElem!_pos _ j (by simpa using hj'), List.getElem_toArray, List.getElem_map,
      (hgj j hj).2.2]
    have e : words[j] = words.getD j [] := by simp [List.getD_eq_getElem?_getD, hj']
    rw [e]
    exact (wK_eq (hgj j hj).2.1).1
  have hpt : ∀ i < cnt, penumPtK 35 6 (mask 6) (35 * 6) false G GI k cnt T PL POS SRT SRI i =
      true := fun i hi => penumSl_spec hs i (Nat.zero_le _) (by omega) hi
  obtain ⟨he, hok⟩ := penumK_left_sound (cap := 64) idc.2.2 hgo hh hpt
  rw [he]
  refine ⟨hlt, hok, by simp [penumRec], fun q hq => ?_⟩
  have hq' : q < cnt := by simpa [penumRec] using hq
  have hc := penumPt_canon (hpt q hq')
  rw [rec_get35 hq']
  unfold sylK at hn
  have hb := allN_spec hn q hq'
  cases h1 : Nat.beq (T q) (pidn 35 6)
  · rw [h1] at hb
    cases h2 : Nat.beq (wordTabK 35 6 (mask 6) (pidn 35 6) (fun _ => T q) (List.replicate p 0))
      (pidn 35 6)
    · refine Or.inr (Or.inl fun heq => ?_)
      obtain ⟨hw1, hw2⟩ := wordTabK_eq (gs := #[unpack 35 6 (T q)]) (S := fun _ => T q) idTab_eq
        idc.1 (List.replicate p 0) (fun j hj => by
          rw [List.eq_of_mem_replicate hj]
          exact ⟨by simp, hc⟩)
      have e1 : unpack 35 6 (wordTabK 35 6 (mask 6) (pidn 35 6) (fun _ => T q)
          (List.replicate p 0)) = unpack 35 6 (pidn 35 6) := by
        rw [← hw1, ← idTab_eq]
        exact heq
      have e2 := beq_unpack hw2 idc.1
      rw [e1, beq_self_eq_true, h2] at e2
      exact absurd e2 (by decide)
    · rw [h2] at hb
      exact Or.inr (Or.inr ⟨_, _, ncl_sound hc hb⟩)
  · exact Or.inl (by rw [Nat.eq_of_beq_eq_true h1, idTab_eq])

theorem syl_all : ∀ i < 4, (∀ w ∈ mclSylWords.getD i [], ∀ j ∈ w, j < mclXGens.size) ∧
    enumOK 35 (mclSylGens i) (mclSylEnum i) = true ∧
    (mclSylEnum i).tabs.size = mclSylSizes.getD i 0 ∧
    ∀ q < (mclSylEnum i).tabs.size, (mclSylEnum i).tabs[q]! = idTab 35 ∨
      wordTabS 35 #[(mclSylEnum i).tabs[q]!] (List.replicate (mclSylPrimes.getD i 0) 0) ≠
        idTab 35 ∨
      ∃ cs W, nclWordsOK 35 mclXGens mclXInvs (mclSylEnum i).tabs[q]! cs W = true := by
  intro i hi
  unfold mclSylEnum mclSylGens
  interval_cases i
  · exact syl_sound (words := mclSylWords.getD 0 []) (p := mclSylPrimes.getD 0 0) rfl sy0_g sy0_hd
      sy0_sl ncl0
  · exact syl_sound (words := mclSylWords.getD 1 []) (p := mclSylPrimes.getD 1 0) rfl sy1_g sy1_hd
      sy1_sl ncl1
  · exact syl_sound (words := mclSylWords.getD 2 []) (p := mclSylPrimes.getD 2 0) rfl sy2_g sy2_hd
      sy2_sl ncl2
  · exact syl_sound (words := mclSylWords.getD 3 []) (p := mclSylPrimes.getD 3 0) rfl sy3_g sy3_hd
      sy3_sl ncl3

theorem nget_getD (L : List Nat) (i : Nat) : nget L i = L.getD i 0 := by
  induction L generalizing i with
  | nil => rfl
  | cons x xs ih =>
    cases i with
    | zero => rfl
    | succ i => exact ih i

theorem facts2287 :
    (mclFix.length = 35 ∧ mclXGens.size = 2 ∧ invsOK 35 mclXGens mclXInvs = true ∧
      mclXOrbits.size = 14 ∧ CFSG.Sporadic.SmallOddCore.permOK 275 (mclCentTbl 4) = true ∧
      ∀ k < 2, CFSG.Sporadic.SmallOddCore.permOK 275 (mclCentTbl (k + 5)) = true) ∧
    (enumOK 35 mclXGens mclXEnum = true ∧ mclXEnum.tabs.size = 20160) ∧
    (∀ i < 4, (∀ w ∈ mclSylWords.getD i [], ∀ j ∈ w, j < mclXGens.size) ∧
      enumOK 35 (mclSylGens i) (mclSylEnum i) = true ∧
      (mclSylEnum i).tabs.size = mclSylSizes.getD i 0 ∧
      ∀ q < (mclSylEnum i).tabs.size, (mclSylEnum i).tabs[q]! = idTab 35 ∨
        wordTabS 35 #[(mclSylEnum i).tabs[q]!] (List.replicate (mclSylPrimes.getD i 0) 0) ≠
          idTab 35 ∨
        ∃ cs W, nclWordsOK 35 mclXGens mclXInvs (mclSylEnum i).tabs[q]! cs W = true) := by
  obtain ⟨p4, p5, p6⟩ := (by simpa only [bAnd_iff] using c_perm :
    invEqK 275 9 (mask 9) (275 * 9) (McLCT.F 4) (McLCI 0) = true ∧
    invEqK 275 9 (mask 9) (275 * 9) (McLCT.F 5) (McLCI 1) = true ∧
    invEqK 275 9 (mask 9) (275 * 9) (McLCT.F 6) (McLCI 2) = true)
  refine ⟨⟨by rw [fix_eq]; rfl, rfl, invs, by simp [mclXOrbits], cent_perm (by norm_num) p4,
    fun k hk => ?_⟩, ⟨?_, ?_⟩, syl_all⟩
  · interval_cases k
    · exact cent_perm (by norm_num) p5
    · exact cent_perm (by norm_num) p6
  · rw [x_enum.1]
    exact x_enum.2
  · rw [x_enum.1]
    simp [penumRec]
    rfl

end CertificateChecks.KernelSpor.McL2287

end
