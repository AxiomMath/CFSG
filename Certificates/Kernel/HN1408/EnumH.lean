module

public import Certificates.Kernel.HN1408.Basic
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.TwoHSData.CheckDefs

public section

namespace CFSG.KD.HN1408

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KS.PEnum CFSG.KS.MulH CFSG.KC.BfsPin
open CFSG.EvenSporadicStandard.HNRecog CFSG.Sporadic.Th.Native CFSG.Sporadic.SmallOddCore
open CFSG.Sporadic.Schreier.Native CFSG.Sporadic.SmallOddCore.Native

theorem foldl_insert_notin (f : Nat → UInt64) (l : List Nat) (m : Std.HashMap UInt64 Nat)
    (a : UInt64) (h : ∀ i ∈ l, f i ≠ a) :
    (l.foldl (fun m i => m.insert (f i) i) m)[a]? = m[a]? := by
  induction l generalizing m with
  | nil => rfl
  | cons i l ih =>
    rw [List.foldl_cons, ih _ fun j hj => h j (List.mem_cons_of_mem _ hj),
      Std.HashMap.getElem?_insert]
    have : (f i == a) = false := by simpa using h i List.mem_cons_self
    simp [this]

theorem foldl_insert_get (f : Nat → UInt64) (l : List Nat) (hnd : l.Nodup)
    (hinj : ∀ a ∈ l, ∀ b ∈ l, f a = f b → a = b) (m : Std.HashMap UInt64 Nat) {q : Nat}
    (hq : q ∈ l) : (l.foldl (fun m i => m.insert (f i) i) m)[f q]? = some q := by
  induction l generalizing m with
  | nil => simp at hq
  | cons i l ih =>
    rw [List.nodup_cons] at hnd
    rw [List.foldl_cons]
    rcases List.mem_cons.1 hq with rfl | hq'
    · rw [foldl_insert_notin _ _ _ _ fun j hj e => hnd.1
          ((hinj j (List.mem_cons_of_mem _ hj) q List.mem_cons_self e) ▸ hj),
        Std.HashMap.getElem?_insert_self]
    · exact ih hnd.2 (fun a ha b hb e => hinj a (List.mem_cons_of_mem _ ha) b
        (List.mem_cons_of_mem _ hb) e) _ hq'

theorem closedOKH_of {n w cnt K : Nat} {T PL S POS : Nat → Nat} {gs : Array Table}
    (hT : ∀ i < cnt, canonK n w (mask w) (n * w) (T i) = true) (hgs : TabsOK n w K S gs)
    (hf : ∀ c < cnt * K, findPtK cnt T (prodQK n w (mask w) K T S) POS c = true)
    (hd : ∀ a < cnt, ∀ b < cnt, hkey n (tabT (unpack n w (T a))) = hkey n (tabT (unpack n w (T b))) →
      a = b) :
    closedOKH n gs (hRec n w cnt T PL).1 = true := by
  have hsz : (hRec n w cnt T PL).1.size = cnt := hRec_size n w cnt T PL
  have hget : ∀ i < cnt, (hRec n w cnt T PL).1[i]! = tabT (unpack n w (T i)) := fun i hi =>
    hRec_get hi
  have hM : ∀ q < cnt,
      ((List.range' 0 (hRec n w cnt T PL).1.size).foldl
        (fun m i => m.insert (hkey n (hRec n w cnt T PL).1[i]!) i)
        (∅ : Std.HashMap UInt64 Nat))[hkey n (hRec n w cnt T PL).1[q]!]? = some q := by
    intro q hq
    rw [hsz]
    refine foldl_insert_get (fun i => hkey n (hRec n w cnt T PL).1[i]!) _ List.nodup_range'
      (fun a ha b hb e => ?_) _ (List.mem_range'_1.2 ⟨by omega, by omega⟩)
    have ha' := (List.mem_range'_1.1 ha).2
    have hb' := (List.mem_range'_1.1 hb).2
    simp only [Nat.zero_add] at ha' hb'
    rw [hget a ha', hget b hb'] at e
    exact hd a ha' b hb' e
  unfold closedOKH
  simp only [Id.run, Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size,
    Nat.add_sub_cancel, Nat.div_one, List.forIn_pure_yield_eq_foldl, pure_bind, Nat.sub_zero]
  rw [show ∀ x : Std.HashMap UInt64 Nat, (pure x : Id (Std.HashMap UInt64 Nat)) = x from fun _ => rfl]
  rw [Array.all_eq_true]
  intro i hi
  have hi' : i < cnt := by rwa [hsz] at hi
  rw [Array.all_eq_true]
  intro j hj
  have hj' : j < K := by rw [← hgs.1]; exact hj
  obtain ⟨hgj, hcj⟩ := hgs.2 j hj'
  have hc : i * K + j < cnt * K := by
    have := Nat.mul_le_mul_right K (Nat.succ_le_of_lt hi')
    rw [Nat.succ_mul] at this
    omega
  obtain ⟨hq, he⟩ := findPt_spec (hf _ hc)
  unfold prodQK at he
  obtain ⟨e1, e2⟩ := div_mod_pair (i := i) hj'
  change r32 POS (i * K + j) < cnt at hq
  rw [show Nat.div (i * K + j) K = i from e1, show Nat.mod (i * K + j) K = j from e2] at he
  have hy : compT n (hRec n w cnt T PL).1[i] gs[j] = (hRec n w cnt T PL).1[r32 POS (i * K + j)]! := by
    rw [← getElem!_pos _ i hi, ← getElem!_pos gs j hj, hget i hi', hgj, compT_unpack (hT i hi') hcj,
      ← he, hget _ hq]
  rw [hy, hM _ hq]
  simp only []
  rw [getElem?_pos _ _ (by rw [hsz]; exact hq), Option.map_some,
    Option.getD_some, ← getElem!_pos _ _ (by rw [hsz]; exact hq), hget _ hq]
  exact tblEq_self (hT _ hq)

theorem slAll {K L N : Nat} {P : Nat → Bool} (hN : N ≤ L * K)
    (h : ∀ s < K, slK N P (Nat.mul L s) L = true) : ∀ i < N, P i = true := by
  intro i hi
  have hL : 0 < L := by
    rcases Nat.eq_zero_or_pos L with h0 | h0
    · rw [h0, Nat.zero_mul] at hN; omega
    · exact h0
  have hs : i / L < K := Nat.div_lt_of_lt_mul (by omega)
  exact slK_spec (h _ hs) i (Nat.mul_div_le i L) (by
    have := Nat.lt_mul_div_succ i hL
    change i < L * (i / L) + L
    rw [Nat.mul_succ] at this
    exact this) hi

theorem peAll {n w m nw k K L N : Nat} {conj : Bool} {G GI T PL POS SRT SRI : Nat → Nat}
    (hN : N ≤ L * K) (h : ∀ s < K, penumSlK n w m nw conj G GI k N T PL POS SRT SRI (Nat.mul L s) L =
      true) : ∀ i < N, penumPtK n w m nw conj G GI k N T PL POS SRT SRI i = true := by
  intro i hi
  have hL : 0 < L := by
    rcases Nat.eq_zero_or_pos L with h0 | h0
    · rw [h0, Nat.zero_mul] at hN; omega
    · exact h0
  have hs : i / L < K := Nat.div_lt_of_lt_mul (by omega)
  exact penumSl_spec (h _ hs) i (Nat.mul_div_le i L) (by
    have := Nat.lt_mul_div_succ i hL
    change i < L * (i / L) + L
    rw [Nat.mul_succ] at this
    exact this) hi

theorem hkey_inj_of {n w cnt : Nat} {T HS HSI : Nat → Nat}
    (hT : ∀ i < cnt, canonK n w (mask w) (n * w) (T i) = true)
    (hs : ∀ i < cnt, hsortPtK n w (mask w) cnt T HS HSI i = true) :
    ∀ a < cnt, ∀ b < cnt, hkey n (tabT (unpack n w (T a))) = hkey n (tabT (unpack n w (T b))) →
      a = b := by
  intro a ha b hb e
  have e' := congrArg UInt64.toNat e
  rw [hkey_tabT (hT a ha), hkey_tabT (hT b hb)] at e'
  exact hkeyK_inj hs a ha b hb e'

theorem enumOKH_of {n w k cnt cap m : Nat} {G GI GJ T PL POS SRT SRI HS HSI CL : Nat → Nat}
    {gs : List Table} (hn : szOK n w = true) (hG : ∀ j < k, G j = pidn n w)
    (hg : TabsOK n w k GI gs.toArray)
    (hgj : ∀ j < k, invEqK n w (mask w) (n * w) (GI j) (GJ j) = true ∧
      canonK n w (mask w) (n * w) (GJ j) = true)
    (hh : penumHdK (pidn n w) cnt cap T PL = true)
    (hp : ∀ i < cnt, penumPtK n w (mask w) (n * w) true G GI k cnt T PL POS SRT SRI i = true)
    (hs : ∀ i < cnt, hsortPtK n w (mask w) cnt T HS HSI i = true)
    (hcl : ∀ c < cnt * (k + k),
      findPtK cnt T (prodQK n w (mask w) (k + k) T (bothK k GI GJ)) CL c = true)
    (hm : cnt = m) :
    enumOKH n cap m gs = true ∧ mulClosureH n gs.toArray cap = hRec n w cnt T PL := by
  obtain ⟨e, ht, hd⟩ := mulH_sound hn hG hg hh hp hs
  have hT : ∀ i < cnt, canonK n w (mask w) (n * w) (T i) = true :=
    fun i hi => penumPt_canon (hp i hi)
  refine ⟨?_, e⟩
  unfold enumOKH
  simp only [Bool.and_eq_true]
  rw [e]
  refine ⟨⟨⟨⟨?_, ht⟩, closedOKH_of hT (TabsOK_both hg hgj) hcl (hkey_inj_of hT hs)⟩, hd⟩, ?_⟩
  · rw [List.all_eq_true]
    intro g hgm
    obtain ⟨j, hj, rfl, hc⟩ := TabsOK_list hg hgm
    rw [invT_unpack (lt_of_canonK (hgj j hj).2) (hgj j hj).1, Bool.and_eq_true]
    exact ⟨permOK_unpack hc (hgj j hj).1, invOK_unpack hc (hgj j hj).2 (hgj j hj).1⟩
  · rw [hRec_size, hm]
    exact beq_self_eq_true m

theorem tabsW_tabs {ws : List (List Nat)} {G : Nat → Nat} (hl : ∀ w ∈ ws, lettersOK w = true)
    (hG : ∀ j < ws.length, G j = WK (ws.getD j [])) :
    TabsOK 1408 11 ws.length G (tabsW ws).toArray := by
  refine ⟨by simp [tabsW], fun j hj => ?_⟩
  have hw : ws.getD j [] ∈ ws := by
    rw [List.getD_eq_getElem _ _ hj]
    exact List.getElem_mem hj
  obtain ⟨e, c⟩ := tabW_eq (hl _ hw)
  rw [hG j hj]
  refine ⟨?_, c⟩
  rw [getElem!_pos _ j (by simpa [tabsW] using hj)]
  simp only [tabsW, List.getElem_toArray, List.getElem_map]
  rw [← e, List.getD_eq_getElem _ _ hj]

theorem wordOK_of {w : List Nat} (h : lettersOK w = true) : wordOK w = true := by
  unfold wordOK
  unfold lettersOK at h
  rw [List.all_eq_true] at h ⊢
  intro l hl
  have := h l hl
  simp only [Bool.and_eq_true, decide_eq_true_eq] at this ⊢
  exact this

theorem gensOK_true : gensOK = true := gens_all

theorem enumW_of {cap m cnt : Nat} {ws : List (List Nat)} {G GI GJ T PL POS SRT SRI HS HSI CL : Nat → Nat}
    (hl : ∀ w ∈ ws, lettersOK w = true) (hG : ∀ j < ws.length, G j = idK)
    (hGI : ∀ j < ws.length, GI j = WK (ws.getD j []))
    (hgj : ∀ j < ws.length, invEqK 1408 11 (mask 11) (1408 * 11) (GI j) (GJ j) = true ∧
      canonK 1408 11 (mask 11) (1408 * 11) (GJ j) = true)
    (hh : penumHdK idK cnt cap T PL = true)
    (hp : ∀ i < cnt, penumPtK 1408 11 (mask 11) (1408 * 11) true G GI ws.length cnt T PL POS SRT SRI i =
      true)
    (hs : ∀ i < cnt, hsortPtK 1408 11 (mask 11) cnt T HS HSI i = true)
    (hcl : ∀ c < cnt * (ws.length + ws.length),
      findPtK cnt T (prodQK 1408 11 (mask 11) (ws.length + ws.length) T (bothK ws.length GI GJ)) CL c =
        true)
    (hm : cnt = m) :
    enumW cap m ws = true ∧ subgroupList cap ws = (hRec 1408 11 cnt T PL).1 := by
  obtain ⟨h1, h2⟩ := enumOKH_of (n := 1408) (w := 11) hn hG (tabsW_tabs hl hGI) hgj hh hp hs hcl hm
  refine ⟨?_, by unfold subgroupList; rw [h2]⟩
  unfold enumW
  rw [gensOK_true, h1, Bool.true_and, Bool.and_true, List.all_eq_true]
  exact fun w hw => wordOK_of (hl w hw)

end CFSG.KD.HN1408

end
