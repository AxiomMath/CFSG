module

public import Certificates.Kernel.LyTr.Tr

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelLyTr

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KS.PEnum CFSG.KS.MulH CFSG.KC.BfsPin
open CFSG.Sporadic.Th.Native CFSG.Sporadic.Schreier.Native CFSG.Sporadic.SmallOddCore
open CFSG.Sporadic.SmallOddCore.Native CFSG.Sporadic.Recognition.LyonsSims
open CFSG.Monster.B.Co2.Native

theorem step_tab {n w X G : Nat} (hid : idT n = tabT (unpack n w (pidn n w)))
    (hidc : canonK n w (mask w) (n * w) (pidn n w) = true)
    (hX : canonK n w (mask w) (n * w) X = true) (hG : canonK n w (mask w) (n * w) G = true) :
    tabT (unpack n w (pcomp n w (mask w) (pcomp n w (mask w) (pidn n w) X) G)) =
      compT n (tabT (unpack n w X)) (tabT (unpack n w G)) := by
  rw [← compT_unpack (canonK_pcomp hidc hX) hG, ← compT_unpack hidc hX, ← hid, idT_tabT,
    compT_tabT _ _ (fun i _ => unpack_lt hX), compA_idA_unpack hX]

theorem txy1080_tabs : TabsOK 1080 11 5 R1.GI Ly1080.txyTabs.toList.toArray := by
  have hs : Ly1080.txyWords.length = 5 := by decide
  rw [Array.toArray_toList]
  exact ⟨by simp [Ly1080.txyTabs, hs], fun j hj => ⟨txy1080T hj, (base11.2.2.2.2.1 j hj).1⟩⟩

theorem r1G : ∀ j < 5, R1.G j = pidn 1080 11 := fun j hj => (base11.2.2.2.2.1 j hj).2.1

theorem yEnum_eq : Tau.yEnum = hRec 1080 11 R1.cnt R1.T R1.PL :=
  (mulH_sound base11.1 r1G txy1080_tabs base11.2.2.2.2.2.2 r1_pe r1_hs).1

theorem r2_tree : mulTreeOK 243 Ly243.txyTabs.toList.toArray (hRec 243 8 R2.cnt R2.T R2.PL).1
    (hRec 243 8 R2.cnt R2.T R2.PL).2.1 (hRec 243 8 R2.cnt R2.T R2.PL).2.2 = true :=
  (mulH_sound base8.1 r2G txy_tabs base8.2.2.2.2.2.2.2.2 r2_pe r2_hs).2.1

theorem r2_hk : hkeysDistinct 243 (hRec 243 8 R2.cnt R2.T R2.PL).1.toList = true :=
  (mulH_sound base8.1 r2G txy_tabs base8.2.2.2.2.2.2.2.2 r2_pe r2_hs).2.2

theorem r1c {i : Nat} (hi : i < R1.cnt) : C11 (R1.T i) := penumPt_canon (r1_pe i hi)

theorem cnt_eq : R1.cnt = R2.cnt := by rw [base11.2.2.2.2.2.1, base8.2.2.2.2.2.2.2.1]

theorem r32_eq {F G : Nat → Nat} {R : Nat} (h : allN R (fun r => Nat.beq (F r) (G r)) = true)
    {i : Nat} (hi : i < 32 * R) : r32 F i = r32 G i := by
  have hr : Nat.shiftRight i 5 < R := by
    change i >>> 5 < R
    rw [Nat.shiftRight_eq_div_pow]
    omega
  have e := Nat.eq_of_beq_eq_true (allN_spec h _ hr)
  have e0 : Nat.add 0 (Nat.shiftRight i 5) = Nat.shiftRight i 5 := Nat.zero_add _
  unfold r32 CFSG.KS.Row.rg
  rw [e0, e]

theorem trees : (∀ i < R1.cnt, r32 R1.PL i = r32 R2.PL i) ∧
    (∀ c < R1.cnt * 5, r32 R1.POS c = r32 R2.POS c) := by
  have h := k_tree
  simp only [bAnd_iff] at h
  have hc := base11.2.2.2.2.2.1
  exact ⟨fun i hi => r32_eq h.1 (by omega), fun c hc' => r32_eq h.2 (by omega)⟩

theorem hRec_snd : (hRec 1080 11 R1.cnt R1.T R1.PL).2 = (hRec 243 8 R2.cnt R2.T R2.PL).2 := by
  have e : ∀ i < R1.cnt, parOf R1.PL i = parOf R2.PL i ∧ labOf R1.PL i = labOf R2.PL i := by
    intro i hi
    unfold parOf labOf
    rw [trees.1 i hi]
    exact ⟨rfl, rfl⟩
  have e1 : (fun i : Fin R1.cnt => parOf R1.PL i.val) = fun i => parOf R2.PL i.val :=
    funext fun i => (e i.val i.isLt).1
  have e2 : (fun i : Fin R1.cnt => labOf R1.PL i.val) = fun i => labOf R2.PL i.val :=
    funext fun i => (e i.val i.isLt).2
  unfold hRec
  simp only
  rw [← cnt_eq, e1, e2]

theorem push_ofFn {m : Nat} (U : Nat → Table) :
    (Array.ofFn (n := m + 1) fun i => U i.val).push (U (m + 1)) =
      Array.ofFn (n := m + 2) fun i => U i.val := by
  apply Array.ext (by simp)
  intro i h1 h2
  simp only [Array.size_push, Array.size_ofFn] at h1
  rw [Array.getElem_ofFn, Array.getElem_push]
  split
  · rw [Array.getElem_ofFn]
  · rename_i h
    have e : i = m + 1 := by simp at h; omega
    subst e
    rfl

theorem replay_foldl {N : Nat} (U : Nat → Table) (f : Array Table → Nat → Table)
    (hstep : ∀ k, 1 ≤ k → k < N → f (Array.ofFn (n := k) fun i => U i.val) k = U k) :
    ∀ m, m + 1 ≤ N → (List.range' 1 m).foldl (fun out k => out.push (f out k)) #[U 0] =
      Array.ofFn (n := m + 1) fun i => U i.val
  | 0, _ => by
    apply Array.ext (by simp)
    intro i h1 _
    have : i = 0 := by simpa using h1
    subst this
    simp
  | m + 1, hm => by
    rw [List.range'_concat, List.foldl_append, replay_foldl U f hstep m (by omega)]
    simp only [List.foldl_cons, List.foldl_nil]
    rw [show 1 + 1 * m = m + 1 by omega, hstep (m + 1) (by omega) (by omega), push_ofFn]

theorem tEnum_eq : Tau.tEnum = (hRec 243 8 R2.cnt R2.T R2.PL).1 := by
  have hpar : Tau.yEnum.2.1.size = R2.cnt := by rw [yEnum_eq, hRec_snd]; simp [hRec]
  have hc2 := base8.2.2.2.2.2.2.2.1
  have hstep : ∀ k, 1 ≤ k → k < R2.cnt →
      compT Ly243.deg (Array.ofFn (n := k) fun i => tabT (unpack 243 8 (R2.T i.val)))[Tau.yEnum.2.1[k]!]!
        Ly243.txyTabs[Tau.yEnum.2.2[k]!]! = tabT (unpack 243 8 (R2.T k)) := by
    intro k hk1 hk
    obtain ⟨-, hs, -, -⟩ := penumPt_specH (r2_pe k hk)
    obtain ⟨hp, hl, he, -⟩ := hs (by omega)
    have ep : Tau.yEnum.2.1[k]! = parOf R2.PL k := by
      rw [yEnum_eq, hRec_snd, getElem!_pos _ k (by simp [hRec]; omega)]
      simp [hRec]
    have el : Tau.yEnum.2.2[k]! = labOf R2.PL k := by
      rw [yEnum_eq, hRec_snd, getElem!_pos _ k (by simp [hRec]; omega)]
      simp [hRec]
    rw [ep, el, getElem!_pos _ _ (by simp; exact hp), Array.getElem_ofFn, txy243T hl, he]
    unfold stepK
    rw [r2G _ hl]
    exact (step_tab hid8 base8.2.1 (r2c (by omega)) (tc hl)).symm
  unfold Tau.tEnum
  simp only [Id.run, Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size,
    Nat.add_sub_cancel, Nat.div_one, List.forIn_pure_yield_eq_foldl]
  rw [hpar]
  have h0 : idT Ly243.deg = tabT (unpack 243 8 (R2.T 0)) := by
    have hh := base8.2.2.2.2.2.2.2.2
    unfold penumHdK at hh
    simp only [bAnd_iff, Nat.beq_eq] at hh
    rw [hh.2.2.1]
    exact hid8
  rw [h0]
  have := replay_foldl (N := R2.cnt) (fun i => tabT (unpack 243 8 (R2.T i)))
    (fun out k => compT Ly243.deg out[Tau.yEnum.2.1[k]!]! Ly243.txyTabs[Tau.yEnum.2.2[k]!]!)
    hstep (R2.cnt - 1) (by omega)
  rw [show R2.cnt - 1 + 1 = R2.cnt by omega] at this
  simp only [pure_bind]
  exact this

theorem getD_foldl_notin (l : List (UInt64 × Nat)) (m : Std.HashMap UInt64 Nat) (a : UInt64)
    (h : ∀ p ∈ l, p.1 ≠ a) : (l.foldl (fun m p => m.insert p.1 p.2) m).getD a 0 = m.getD a 0 := by
  induction l generalizing m with
  | nil => rfl
  | cons p l ih =>
    rw [List.foldl_cons, ih _ fun q hq => h q (List.mem_cons_of_mem _ hq),
      Std.HashMap.getD_insert]
    have : (p.1 == a) = false := by simpa using h p List.mem_cons_self
    simp [this]

theorem getD_foldl_insert (l : List (UInt64 × Nat)) (hnd : (l.map Prod.fst).Nodup)
    (m : Std.HashMap UInt64 Nat) {p : UInt64 × Nat} (hp : p ∈ l) :
    (l.foldl (fun m p => m.insert p.1 p.2) m).getD p.1 0 = p.2 := by
  induction l generalizing m with
  | nil => simp at hp
  | cons q l ih =>
    rw [List.map_cons, List.nodup_cons] at hnd
    rw [List.foldl_cons]
    rcases List.mem_cons.1 hp with rfl | hp'
    · rw [getD_foldl_notin _ _ _ fun r hr e => hnd.1 (List.mem_map.2 ⟨r, hr, e⟩),
        Std.HashMap.getD_insert_self]
    · exact ih hnd.2 _ hp'

theorem hkey_inj : ∀ a < R1.cnt, ∀ b < R1.cnt,
    hkey 1080 (tabT (unpack 1080 11 (R1.T a))) = hkey 1080 (tabT (unpack 1080 11 (R1.T b))) →
      a = b := by
  intro a ha b hb e
  have e' := congrArg UInt64.toNat e
  rw [hkey_tabT (r1c ha), hkey_tabT (r1c hb)] at e'
  exact hkeyK_inj r1_hs a ha b hb e'

theorem yKeys_getD {q : Nat} (hq : q < R1.cnt) :
    Tau.yKeys.getD (hkey 1080 (tabT (unpack 1080 11 (R1.T q)))) 0 = q := by
  unfold Tau.yKeys
  have ef : ∀ L : List (Table × Nat),
      List.foldl (fun m p => m.insert (hkey Ly1080.deg p.1) p.2) (∅ : Std.HashMap UInt64 Nat) L =
        List.foldl (fun m p => m.insert p.1 p.2) ∅ (L.map fun p => (hkey 1080 p.1, p.2)) := by
    intro L
    rw [List.foldl_map]
  rw [ef, yEnum_eq]
  have hL : (hRec 1080 11 R1.cnt R1.T R1.PL).1.toList =
      List.ofFn (n := R1.cnt) fun i => tabT (unpack 1080 11 (R1.T i.val)) := by
    simp [hRec]
  rw [hL]
  have hmem : (hkey 1080 (tabT (unpack 1080 11 (R1.T q))), q) ∈
      ((List.ofFn (n := R1.cnt) fun i => tabT (unpack 1080 11 (R1.T i.val))).zipIdx.map
        fun p => (hkey 1080 p.1, p.2)) := by
    rw [List.mem_map]
    refine ⟨(tabT (unpack 1080 11 (R1.T q)), q), ?_, rfl⟩
    rw [List.mem_zipIdx_iff_getElem?]
    simp [hq]
  refine getD_foldl_insert _ ?_ _ hmem
  rw [List.map_map]
  have e : ((fun p : UInt64 × Nat => p.1) ∘ fun p : Table × Nat => (hkey 1080 p.1, p.2)) =
      fun p => hkey 1080 p.1 := rfl
  have e2 : (fun p : Table × Nat => hkey 1080 p.1) = (fun T => hkey 1080 T) ∘ Prod.fst := rfl
  rw [e, e2, ← List.map_map, List.zipIdx_map_fst, List.map_ofFn, List.nodup_ofFn]
  intro a b h
  exact Fin.ext (hkey_inj a.val a.isLt b.val b.isLt h)

theorem succ1 {k l : Nat} (hk : k < R1.cnt) (hl : l < 5) :
    r32 R1.POS (k * 5 + l) < R1.cnt ∧
      tabT (unpack 1080 11 (R1.T (r32 R1.POS (k * 5 + l)))) =
        compT 1080 (tabT (unpack 1080 11 (R1.T k))) Ly1080.txyTabs[l]! := by
  obtain ⟨-, -, hp, -⟩ := penumPt_specH (r1_pe k hk)
  obtain ⟨hq, he, -⟩ := hp l hl
  refine ⟨hq, ?_⟩
  rw [he, txy1080T hl]
  unfold stepK
  rw [r1G _ hl]
  exact step_tab hid11 base11.2.1 (r1c hk) (base11.2.2.2.2.1 l hl).1

theorem succ2 {k l : Nat} (hk : k < R2.cnt) (hl : l < 5) :
    r32 R2.POS (k * 5 + l) < R2.cnt ∧
      tabT (unpack 243 8 (R2.T (r32 R2.POS (k * 5 + l)))) =
        compT 243 (tabT (unpack 243 8 (R2.T k))) Ly243.txyTabs[l]! := by
  obtain ⟨-, -, hp, -⟩ := penumPt_specH (r2_pe k hk)
  obtain ⟨hq, he, -⟩ := hp l hl
  refine ⟨hq, ?_⟩
  rw [he, txy243T hl]
  unfold stepK
  rw [r2G _ hl]
  exact step_tab hid8 base8.2.1 (r2c hk) (tc hl)

theorem succTab_get {k l : Nat} (hk : k < R1.cnt) (hl : l < 5) :
    (Tau.succTab[k]!)[l]! = r32 R1.POS (k * 5 + l) := by
  have hsz : Tau.yEnum.1.size = R1.cnt := by rw [yEnum_eq]; simp [hRec]
  unfold Tau.succTab
  rw [getElem!_pos _ k (by simp [hsz, hk]), Array.getElem_map,
    getElem!_pos _ l (by simp [hl]), Array.getElem_map, Array.getElem_range]
  have ex : Tau.yEnum.1[k]'(by rw [hsz]; exact hk) = tabT (unpack 1080 11 (R1.T k)) := by
    have : Tau.yEnum.1[k]'(by rw [hsz]; exact hk) = (hRec 1080 11 R1.cnt R1.T R1.PL).1[k]'(by
        simp [hRec, hk]) := by
      congr 1
      exact congrArg Prod.fst yEnum_eq
    rw [this]
    simp [hRec]
  rw [ex, ← (succ1 hk hl).2]
  exact yKeys_getD (succ1 hk hl).1

theorem tauOK_of : Tau.tauOK = true := by
  have hsz : Tau.yEnum.1.size = R1.cnt := by rw [yEnum_eq]; simp [hRec]
  have hc := cnt_eq
  unfold Tau.tauOK
  simp only [Bool.and_eq_true, List.all_eq_true, List.mem_range, decide_eq_true_eq, beq_iff_eq]
  refine ⟨⟨⟨⟨?_, ?_⟩, ?_⟩, ?_⟩, ?_⟩
  · rw [tEnum_eq, yEnum_eq, hRec_snd]
    have h := r2_tree
    rwa [Array.toArray_toList] at h
  · rw [tEnum_eq]
    exact r2_hk
  · rw [tEnum_eq, hsz, hc]
    simp [hRec]
  · unfold Tau.succTab
    simp
  · intro k hk l hl
    rw [hsz] at hk
    rw [succTab_get hk hl]
    obtain ⟨hq1, he1⟩ := succ1 hk hl
    have hk2 : k < R2.cnt := by omega
    have epos : r32 R1.POS (k * 5 + l) = r32 R2.POS (k * 5 + l) := trees.2 _ (by omega)
    obtain ⟨hq2, he2⟩ := succ2 hk2 hl
    refine ⟨⟨by rw [hsz]; exact hq1, ?_⟩, ?_⟩
    · rw [yEnum_eq]
      simp only [hRec]
      rw [getElem!_pos _ _ (by simp; exact hq1), getElem!_pos _ _ (by simp; exact hk),
        Array.getElem_ofFn, Array.getElem_ofFn, ← he1]
      exact tblEq_self (r1c hq1)
    · rw [tEnum_eq]
      simp only [hRec]
      rw [epos, getElem!_pos _ _ (by simp; exact hq2), getElem!_pos _ _ (by simp; exact hk2),
        Array.getElem_ofFn, Array.getElem_ofFn, ← he2]
      exact tblEq_self (r2c hq2)

end CertificateChecks.KernelLyTr

end
