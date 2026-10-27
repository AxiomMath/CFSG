module

public import CFSG.Certificates.Kernel.Spor.MulHInvSound
public import Certificates.Data.Kernel.Spor.MulHQ
public import CFSG.Sporadic.SmallOddCore.LocalCheck
public import Certificates.Kernel.Sporadic.OddCore.PEnumGlue2
public import Certificates.Kernel.Sporadic.OddCore.PEnumGlue

public section

namespace CFSG.KS.MulH

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KS.PEnum CFSG.KC.BfsPin
open CFSG.Sporadic.Th.Native CFSG.Sporadic.Schreier.Native CFSG.Sporadic.SmallOddCore.Native
open CFSG.Monster.B.Co2.Native

theorem natArr_tabT {n w X : Nat} (hX : canonK n w (mask w) (n * w) X = true) :
    natArr (tabT (unpack n w X)) = unpack n w X := by
  unfold natArr tabT
  apply Array.ext (by simp)
  intro i h1 h2
  have h := unpack_lt (i := i) hX
  rw [getElem!_pos _ i h2] at h
  simp only [Array.getElem_map, UInt32.toNat_ofNat']
  exact Nat.mod_eq_of_lt h

theorem tabT_natArr (x : Table) : tabT (natArr x) = x := by
  unfold tabT natArr
  apply Array.ext (by simp)
  intro i h1 h2
  simp

theorem compT_unpack {n w p q : Nat} (hp : canonK n w (mask w) (n * w) p = true)
    (hq : canonK n w (mask w) (n * w) q = true) :
    compT n (tabT (unpack n w p)) (tabT (unpack n w q)) =
      tabT (unpack n w (pcomp n w (mask w) p q)) := by
  rw [compT_tabT _ _ (fun i _ => unpack_lt hq), compA_unpack hp hq]

theorem conjT_unpack {n w g gi x : Nat} (hg : canonK n w (mask w) (n * w) g = true)
    (hgi : canonK n w (mask w) (n * w) gi = true) (hx : canonK n w (mask w) (n * w) x = true) :
    conjT n (tabT (unpack n w g)) (tabT (unpack n w gi)) (tabT (unpack n w x)) =
      tabT (unpack n w (pcomp n w (mask w) (pcomp n w (mask w) g x) gi)) := by
  unfold conjT
  rw [compT_unpack hg hx, compT_unpack (canonK_pcomp hg hx) hgi]

theorem tblEq_self {n w p : Nat} (hp : canonK n w (mask w) (n * w) p = true) :
    tblEq n (tabT (unpack n w p)) (tabT (unpack n w p)) = true := by
  rw [tblEq_unpack hp hp, Nat.beq_refl]

theorem commTT_unpack {n w p q : Nat} (hp : canonK n w (mask w) (n * w) p = true)
    (hq : canonK n w (mask w) (n * w) q = true) :
    CFSG.Sporadic.SmallOddCore.commTT n (tabT (unpack n w p)) (tabT (unpack n w q)) =
      Nat.beq (pcomp n w (mask w) p q) (pcomp n w (mask w) q p) := by
  unfold CFSG.Sporadic.SmallOddCore.commTT
  rw [compT_unpack hp hq, compT_unpack hq hp,
    tblEq_unpack (canonK_pcomp hp hq) (canonK_pcomp hq hp)]

theorem permOK_unpack {n w p r : Nat} (hp : canonK n w (mask w) (n * w) p = true)
    (h : invEqK n w (mask w) (n * w) p r = true) :
    CFSG.Sporadic.SmallOddCore.permOK n (tabT (unpack n w p)) = true := by
  obtain ⟨h1, h2⟩ := invEqK_sound h
  unfold CFSG.Sporadic.SmallOddCore.permOK
  rw [natArr_tabT hp, h1]
  exact h2

theorem invOK_unpack {n w p r : Nat} (hp : canonK n w (mask w) (n * w) p = true)
    (hr : canonK n w (mask w) (n * w) r = true) (h : invEqK n w (mask w) (n * w) p r = true) :
    invOK n (tabT (unpack n w p)) (tabT (unpack n w r)) = true := by
  obtain ⟨_, h2⟩ := invEqK_sound h
  unfold isInvA at h2
  rw [allLt_iff'] at h2
  unfold invOK
  rw [CFSG.KS.TW.allIn_iff]
  intro i hi
  have hb := h2 i hi
  simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at hb
  rw [ap_tabT _ (unpack_lt hp), ap_tabT _ (unpack_lt hr), hb.2]
  exact beq_self_eq_true i

theorem wfoldK_cons (n w m : Nat) (S : Nat → Nat) (l : Nat) (rest : List Nat) (acc : Nat) :
    wfoldK n w m S (l :: rest) acc = wfoldK n w m S rest (pcomp n w m acc (S l)) := by
  change strictN (pcomp n w m acc (S l)) (wfoldK n w m S rest) = _
  rw [CFSG.KS.PEnum.strictN_app']

theorem foldl_unpack {n w : Nat} {gs : List Table} {S : Nat → Nat} :
    ∀ (wd : List Nat) (acc : Nat), canonK n w (mask w) (n * w) acc = true →
      (∀ l ∈ wd, gs.getD (l - 1) (idT n) = tabT (unpack n w (S l)) ∧
        canonK n w (mask w) (n * w) (S l) = true) →
      wd.foldl (fun a l => compT n a (gs.getD (l - 1) (idT n))) (tabT (unpack n w acc)) =
          tabT (unpack n w (wfoldK n w (mask w) S wd acc)) ∧
        canonK n w (mask w) (n * w) (wfoldK n w (mask w) S wd acc) = true
  | [], acc, ha, _ => ⟨rfl, ha⟩
  | l :: rest, acc, ha, h => by
    obtain ⟨h1, h2⟩ := h l List.mem_cons_self
    rw [List.foldl_cons, h1, compT_unpack ha h2, wfoldK_cons]
    exact foldl_unpack rest _ (canonK_pcomp ha h2) fun l' hl' => h l' (List.mem_cons_of_mem l hl')

theorem wordTbl_unpack {n w : Nat} {gs : List Table} {S : Nat → Nat}
    (hid : idT n = tabT (unpack n w (pidn n w)))
    (hidc : canonK n w (mask w) (n * w) (pidn n w) = true)
    {wd : List Nat}
    (h : ∀ l ∈ wd, gs.getD (l - 1) (idT n) = tabT (unpack n w (S l)) ∧
      canonK n w (mask w) (n * w) (S l) = true) :
    CFSG.Sporadic.SmallOddCore.wordTbl n gs wd =
        tabT (unpack n w (wfoldK n w (mask w) S wd (pidn n w))) ∧
      canonK n w (mask w) (n * w) (wfoldK n w (mask w) S wd (pidn n w)) = true := by
  have e : CFSG.Sporadic.SmallOddCore.wordTbl n gs wd =
      wd.foldl (fun a l => compT n a (gs.getD (l - 1) (idT n))) (tabT (unpack n w (pidn n w))) := by
    unfold CFSG.Sporadic.SmallOddCore.wordTbl
    rw [← hid]
  rw [e]
  exact foldl_unpack wd _ hidc h

theorem hRec_size (n w cnt : Nat) (T PL : Nat → Nat) : (hRec n w cnt T PL).1.size = cnt := by
  simp [hRec]

theorem hRec_get {n w cnt i : Nat} {T PL : Nat → Nat} (hi : i < cnt) :
    (hRec n w cnt T PL).1[i]! = tabT (unpack n w (T i)) := by
  rw [getElem!_pos _ i (by simpa [hRec] using hi)]
  simp [hRec]

theorem div_mod_pair {i j K : Nat} (hj : j < K) : (i * K + j) / K = i ∧ (i * K + j) % K = j := by
  have hK : 0 < K := by omega
  constructor
  · rw [Nat.add_comm, Nat.add_mul_div_right _ _ hK, Nat.div_eq_of_lt hj, Nat.zero_add]
  · rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hj]

theorem closedOK_of {n w cnt K : Nat} {T PL S POS : Nat → Nat} {gs : Array Table}
    (hT : ∀ i < cnt, canonK n w (mask w) (n * w) (T i) = true) (hgs : TabsOK n w K S gs)
    (hf : ∀ c < cnt * K, findPtK cnt T (prodQK n w (mask w) K T S) POS c = true) :
    closedOK n gs (hRec n w cnt T PL).1 = true := by
  unfold closedOK
  rw [Array.all_eq_true]
  intro i hi
  have hi' : i < cnt := by simpa [hRec] using hi
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
  have hx : (hRec n w cnt T PL).1[i] = tabT (unpack n w (T i)) := by simp [hRec]
  rw [hx, ← getElem!_pos gs j hj, hgj, compT_unpack (hT i hi') hcj, ← he]
  exact memT_of hq (tblEq_self (hT _ hq))

theorem conjAll_of {n w cnt K : Nat} {T PL C CI POS : Nat → Nat} {cs : List Table}
    (hT : ∀ i < cnt, canonK n w (mask w) (n * w) (T i) = true) (hcs : TabsOK n w K C cs.toArray)
    (hci : ∀ j < K, invEqK n w (mask w) (n * w) (C j) (CI j) = true ∧
      canonK n w (mask w) (n * w) (CI j) = true)
    (hf : ∀ c < cnt * K, findPtK cnt T (conjQK n w (mask w) K T C CI) POS c = true) :
    cs.all (fun c => (hRec n w cnt T PL).1.all fun x =>
      memT n (hRec n w cnt T PL).1 (conjT n c (invT n c) x)) = true := by
  rw [List.all_eq_true]
  intro c hc
  obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hc
  have hj' : j < K := by rw [← hcs.1]; simpa using hj
  obtain ⟨hgj, hcj⟩ := hcs.2 j hj'
  have hcj' : cs[j] = tabT (unpack n w (C j)) := by
    rw [← hgj, getElem!_pos _ j (by simpa using hj)]
    simp
  rw [Array.all_eq_true]
  intro i hi
  have hi' : i < cnt := by simpa [hRec] using hi
  have hc : i * K + j < cnt * K := by
    have := Nat.mul_le_mul_right K (Nat.succ_le_of_lt hi')
    rw [Nat.succ_mul] at this
    omega
  obtain ⟨hq, he⟩ := findPt_spec (hf _ hc)
  unfold conjQK at he
  obtain ⟨e1, e2⟩ := div_mod_pair (i := i) hj'
  change r32 POS (i * K + j) < cnt at hq
  rw [show Nat.div (i * K + j) K = i from e1, show Nat.mod (i * K + j) K = j from e2] at he
  have hx : (hRec n w cnt T PL).1[i] = tabT (unpack n w (T i)) := by simp [hRec]
  rw [hx, hcj', invT_unpack (lt_of_canonK (hci j hj').2) (hci j hj').1, conjT_unpack hcj (hci j hj').2 (hT i hi'), ← he]
  exact memT_of hq (tblEq_self (hT _ hq))

theorem countP_range_lt (q : Nat → Bool) {cnt N : Nat} (h : cnt ≤ N) :
    (List.range N).countP (fun i => bAnd(Nat.blt i cnt, q i)) = (List.range cnt).countP q := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le h
  rw [List.range_add, List.countP_append]
  have h1 : (List.range cnt).countP (fun i => bAnd(Nat.blt i cnt, q i)) =
      (List.range cnt).countP q := by
    apply List.countP_congr
    intro i hi
    have hb : Nat.blt i cnt = true := Eq.mpr Nat.blt_eq (List.mem_range.1 hi)
    rw [hb]
  have h2 : ((List.range d).map (cnt + ·)).countP (fun i => bAnd(Nat.blt i cnt, q i)) = 0 := by
    rw [List.countP_eq_zero]
    intro i hi
    obtain ⟨a, _, rfl⟩ := List.mem_map.1 hi
    have hb : Nat.blt (cnt + a) cnt = false := by
      cases e : Nat.blt (cnt + a) cnt
      · rfl
      · have := Nat.le_of_ble_eq_true e
        omega
    rw [hb]
    simp
  rw [h1, h2, Nat.add_zero]

theorem countP_hRec {n w cnt hi : Nat} {T PL : Nat → Nat} {p : Table → Bool} {q : Nat → Bool}
    (hle : cnt ≤ 64 * hi) (hq : ∀ i < cnt, p (tabT (unpack n w (T i))) = q i) :
    (hRec n w cnt T PL).1.toList.countP p = cntBelowK cnt q hi := by
  unfold cntBelowK
  rw [cntK_eq, countP_range_lt q hle]
  simp only [hRec, Array.toList_ofFn]
  rw [List.ofFn_eq_map, List.countP_map]
  rw [← List.map_coe_finRange_eq_range, List.countP_map]
  apply List.countP_congr
  intro i _
  simp only [Function.comp, hq i.val i.isLt]

theorem bothK_lt {k j : Nat} {G GI : Nat → Nat} (h : j < k) : bothK k G GI j = G j := by
  have hb : Nat.blt j k = true := Eq.mpr Nat.blt_eq h
  unfold bothK
  rw [hb]

theorem bothK_ge {k j : Nat} {G GI : Nat → Nat} (h : k ≤ j) : bothK k G GI j = GI (j - k) := by
  have hb : Nat.blt j k = false := by
    cases e : Nat.blt j k
    · rfl
    · have := Nat.le_of_ble_eq_true e
      omega
  unfold bothK
  rw [hb]
  rfl

theorem TabsOK_both {n w k : Nat} {GI GJ : Nat → Nat} {A : Array Table} (hA : TabsOK n w k GI A)
    (hgj : ∀ j < k, invEqK n w (mask w) (n * w) (GI j) (GJ j) = true ∧
      canonK n w (mask w) (n * w) (GJ j) = true) :
    TabsOK n w (k + k) (bothK k GI GJ) (A ++ A.map (invT n)) := by
  refine ⟨by simp [hA.1], fun j hj => ?_⟩
  have hsz : (A ++ A.map (invT n)).size = k + k := by simp [hA.1]
  rw [getElem!_pos _ j (by rw [hsz]; exact hj)]
  by_cases h : j < k
  · rw [Array.getElem_append_left (by rw [hA.1]; exact h),
      ← getElem!_pos A j (by rw [hA.1]; exact h), bothK_lt h]
    exact hA.2 j h
  · have hjk : j - k < k := by omega
    rw [Array.getElem_append_right (by rw [hA.1]; omega), bothK_ge (by omega)]
    simp only [Array.getElem_map, hA.1]
    rw [← getElem!_pos A (j - k) (by rw [hA.1]; exact hjk), (hA.2 _ hjk).1,
      invT_unpack (lt_of_canonK (hgj _ hjk).2) (hgj _ hjk).1]
    exact ⟨rfl, (hgj _ hjk).2⟩

theorem TabsOK_list {n w k : Nat} {G : Nat → Nat} {gs : List Table} (h : TabsOK n w k G gs.toArray)
    {g : Table} (hg : g ∈ gs) :
    ∃ j < k, g = tabT (unpack n w (G j)) ∧ canonK n w (mask w) (n * w) (G j) = true := by
  obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hg
  have hj' : j < k := by rw [← h.1]; simpa using hj
  obtain ⟨h1, h2⟩ := h.2 j hj'
  refine ⟨j, hj', ?_, h2⟩
  rw [← h1, getElem!_pos _ j (by simpa using hj)]
  simp

theorem enumOK_of {n w k cnt cap m : Nat} {G GI GJ T PL POS SRT SRI HS HSI CL : Nat → Nat}
    {gs : List Table} (hn : szOK n w = true) (hG : ∀ j < k, G j = pidn n w)
    (hg : TabsOK n w k GI gs.toArray)
    (hgj : ∀ j < k, invEqK n w (mask w) (n * w) (GI j) (GJ j) = true ∧
      canonK n w (mask w) (n * w) (GJ j) = true)
    (hh : penumHdK (pidn n w) cnt cap T PL = true)
    (hp : ∀ i < cnt, penumPtK n w (mask w) (n * w) true G GI k cnt T PL POS SRT SRI i = true)
    (hs : ∀ i < cnt, hsortPtK n w (mask w) cnt T HS HSI i = true)
    (hcl : ∀ c < cnt * (k + k),
      findPtK cnt T (prodQK n w (mask w) (k + k) T (bothK k GI GJ)) CL c = true)
    (hm : cnt = m) : CFSG.Sporadic.SmallOddCore.enumOK n cap m gs = true := by
  obtain ⟨e, ht, hd⟩ := mulH_sound hn hG hg hh hp hs
  have hT : ∀ i < cnt, canonK n w (mask w) (n * w) (T i) = true :=
    fun i hi => penumPt_canon (hp i hi)
  unfold CFSG.Sporadic.SmallOddCore.enumOK
  simp only [Bool.and_eq_true]
  rw [e]
  refine ⟨⟨⟨⟨?_, ht⟩, closedOK_of hT (TabsOK_both hg hgj) hcl⟩, hd⟩, ?_⟩
  · rw [List.all_eq_true]
    intro g hgm
    obtain ⟨j, hj, rfl, hc⟩ := TabsOK_list hg hgm
    rw [invT_unpack (lt_of_canonK (hgj j hj).2) (hgj j hj).1]
    exact invOK_unpack hc (hgj j hj).2 (hgj j hj).1
  · rw [hRec_size, hm]
    exact beq_self_eq_true m

theorem normOK_of {n w k cnt cap K : Nat} {G GI T PL POS SRT SRI HS HSI C CI NP : Nat → Nat}
    {gs cs : List Table} (hn : szOK n w = true) (hG : ∀ j < k, G j = pidn n w)
    (hg : TabsOK n w k GI gs.toArray) (hh : penumHdK (pidn n w) cnt cap T PL = true)
    (hp : ∀ i < cnt, penumPtK n w (mask w) (n * w) true G GI k cnt T PL POS SRT SRI i = true)
    (hs : ∀ i < cnt, hsortPtK n w (mask w) cnt T HS HSI i = true)
    (hcs : TabsOK n w K C cs.toArray)
    (hci : ∀ j < K, invEqK n w (mask w) (n * w) (C j) (CI j) = true ∧
      canonK n w (mask w) (n * w) (CI j) = true)
    (hf : ∀ c < cnt * K, findPtK cnt T (conjQK n w (mask w) K T C CI) NP c = true) :
    CFSG.Sporadic.SmallOddCore.normOK n cap gs cs = true := by
  obtain ⟨e, _, _⟩ := mulH_sound hn hG hg hh hp hs
  have hT : ∀ i < cnt, canonK n w (mask w) (n * w) (T i) = true :=
    fun i hi => penumPt_canon (hp i hi)
  unfold CFSG.Sporadic.SmallOddCore.normOK
  simp only []
  rw [e]
  exact conjAll_of hT hcs hci hf

theorem centCount_eq {n w k cnt cap hi : Nat} {G GI T PL POS SRT SRI HS HSI : Nat → Nat}
    {cs gs : List Table} {q : Nat → Bool} (hn : szOK n w = true) (hG : ∀ j < k, G j = pidn n w)
    (hg : TabsOK n w k GI cs.toArray) (hh : penumHdK (pidn n w) cnt cap T PL = true)
    (hp : ∀ i < cnt, penumPtK n w (mask w) (n * w) true G GI k cnt T PL POS SRT SRI i = true)
    (hs : ∀ i < cnt, hsortPtK n w (mask w) cnt T HS HSI i = true) (hle : cnt ≤ 64 * hi)
    (hq : ∀ i < cnt,
      (gs.all fun g => CFSG.Sporadic.SmallOddCore.commTT n (tabT (unpack n w (T i))) g) = q i) :
    CFSG.Sporadic.SmallOddCore.centCount n cap cs gs = cntBelowK cnt q hi := by
  obtain ⟨e, _, _⟩ := mulH_sound hn hG hg hh hp hs
  unfold CFSG.Sporadic.SmallOddCore.centCount
  rw [e]
  exact countP_hRec hle hq

theorem TabsOK_congr {n w k : Nat} {G G' : Nat → Nat} {A : Array Table} (he : ∀ j < k, G' j = G j)
    (h : TabsOK n w k G A) : TabsOK n w k G' A :=
  ⟨h.1, fun j hj => by rw [he j hj]; exact h.2 j hj⟩

theorem TabsOK_inv {n w k : Nat} {G GI : Nat → Nat} {A : Array Table} (hA : TabsOK n w k G A)
    (hgi : ∀ j < k, invEqK n w (mask w) (n * w) (G j) (GI j) = true ∧
      canonK n w (mask w) (n * w) (GI j) = true) :
    TabsOK n w k GI (A.map (invT n)) := by
  refine ⟨by simp [hA.1], fun j hj => ?_⟩
  rw [getElem!_pos _ j (by simp [hA.1, hj]), Array.getElem_map,
    ← getElem!_pos A j (by rw [hA.1]; exact hj),
    (hA.2 j hj).1, invT_unpack (lt_of_canonK (hgi j hj).2) (hgi j hj).1]
  exact ⟨rfl, (hgi j hj).2⟩

end CFSG.KS.MulH

end
