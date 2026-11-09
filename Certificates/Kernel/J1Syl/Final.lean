module

public import Certificates.Kernel.J1Syl.Checks
public import Certificates.Kernel.Sporadic.J1K.Final
public import Certificates.Kernel.J1Syl.Slp
public import Certificates.Kernel.J1Syl.ChecksF
public import Certificates.Kernel.J1Syl.ChecksG
public import CFSG.Certificates.Kernel.Spor.TabWords
public import CFSG.Certificates.Kernel.Co1PTextSound
public import CFSG.Sporadic.Th.TableSpec
public import CFSG.Certificates.Kernel.SporSch.TblSound

public section

set_option maxRecDepth 400000

#kon_join CertificateChecks.KernelJ1Syl.ruleAll CertificateChecks.KernelJ1Syl.ruleSl 8
#kon_join CertificateChecks.KernelJ1Syl.normAll CertificateChecks.KernelJ1Syl.normSl 4
#kon_join CertificateChecks.KernelJ1Syl.fOrdAll CertificateChecks.KernelJ1Syl.fOrd 10
#kon_join CertificateChecks.KernelJ1Syl.fMovAll CertificateChecks.KernelJ1Syl.fMov 10

namespace CertificateChecks.KernelJ1Syl

open CFSG.KC.Enum CFSG.KS CFSG.KS.PEnum CFSG.KS.TW CFSG.Sporadic.Th CFSG.Sporadic.Th.Native
open CFSG.Sporadic.J1.Native CFSG.Sporadic.J1.Sylow.Native CertificateChecks.KernelSpor.J1K
open CFSG.KS.VO

theorem spW_eq : ∀ cs : List Char, spW cs = (cs.splitOn ',').map (·.map letterOf)
  | [] => by rw [List.splitOn_nil]; rfl
  | a :: cs => by
    have e : spW (a :: cs) = Bool.rec (motive := fun _ => List (List Int))
        (List.rec (motive := fun _ => List (List Int)) [[letterOf a]]
          (fun w ws _ => (letterOf a :: w) :: ws) (spW cs))
        ([] :: spW cs) (a == ',') := rfl
    rw [e, spW_eq cs, List.splitOn_cons_eq_if_modifyHead]
    cases h : (a == ',')
    · simp only [Bool.false_eq_true, ↓reduceIte]
      obtain ⟨w, ws, hw⟩ : ∃ w ws, cs.splitOn ',' = w :: ws := by
        cases hs : cs.splitOn ',' with
        | nil => exact absurd hs (List.splitOn_ne_nil _ _)
        | cons w ws => exact ⟨w, ws, rfl⟩
      rw [hw]
      rfl
    · simp only [↓reduceIte, List.map_cons, List.map_nil]

theorem parseWords_eq (cs : List Char) : parseWords (String.ofList cs) = (spW cs).toArray := by
  unfold parseWords parseWord
  rw [CFSG.KC.Co1P.splitOn_comma, spW_eq, List.map_map]
  congr 1
  apply List.map_congr_left
  intro c _
  simp [String.toList_ofList]

theorem tw_eq : parseWords (tWordsStr ()) = TWL.toArray := by
  rw [TW.eq, parseWords_eq]
  rfl

theorem nw_eq : parseWords (nWordsStr ()) = NWL.toArray := by
  rw [NW.eq, parseWords_eq]
  rfl

theorem compT_TR {n : Nat} {P Q : Table} {f g : Nat → Nat} (hP : TR n P f) (hQ : TR n Q g) :
    TR n (compT n P Q) fun x => f (g x) := by
  refine ⟨by simp [compT], fun i hi => ?_⟩
  obtain ⟨q1, q2⟩ := hQ.2 i hi
  obtain ⟨p1, p2⟩ := hP.2 _ q2
  refine ⟨?_, p2⟩
  unfold ap compT
  rw [getElem!_pos _ i (by simpa using hi), Array.getElem_ofFn]
  unfold ap at q1 p1
  rw [q1, p1]

theorem tabEq_true {n : Nat} {P Q : Table} {f g : Nat → Nat} (hP : TR n P f) (hQ : TR n Q g)
    (h : ∀ i < n, f i = g i) : tabEq n P Q = true := by
  unfold tabEq
  rw [allIn_eq_true]
  intro i _ hi
  rw [(hP.2 i hi).1, (hQ.2 i hi).1, h i hi]
  exact beq_self_eq_true _

theorem tabEq_false {n : Nat} {P Q : Table} {f g : Nat → Nat} (hP : TR n P f) (hQ : TR n Q g)
    {i : Nat} (hi : i < n) (h : f i ≠ g i) : tabEq n P Q = false := by
  unfold tabEq
  rw [Bool.eq_false_iff, ne_eq, allIn_eq_true]
  intro H
  have := H i (Nat.zero_le _) hi
  rw [(hP.2 i hi).1, (hQ.2 i hi).1] at this
  exact h (beq_iff_eq.1 this)

theorem tabEq_false_key {n : Nat} {P Q : Table} {f g : Nat → Nat} (hn : 1 < n) (hP : TR n P f)
    (hQ : TR n Q g) (h : keyOf (f 0) (f 1) ≠ keyOf (g 0) (g 1)) : tabEq n P Q = false := by
  by_cases h0 : f 0 = g 0
  · refine tabEq_false hP hQ hn fun h1 => h ?_
    rw [h0, h1]
  · exact tabEq_false hP hQ (by omega) h0

theorem size_alpha : OJ.alpha.size = 1540 := by simp [vorbRec]

theorem size_beta : OJ.beta.size = 1540 := by simp [vorbRec]

theorem gens_TR (z : Int) : TR 1540 (genTables OJ z) (GJ z) := by
  refine ⟨?_, fun i hi => gens_get z hi⟩
  unfold genTables
  rw [size_OJ]
  by_cases h1 : z = 1
  · rw [if_pos h1]
    exact size_alpha
  rw [if_neg h1]
  by_cases h2 : z = -1
  · rw [if_pos h2]
    exact CFSG.KS.Tbl.invT_size _ _
  rw [if_neg h2]
  by_cases h3 : z = 2
  · rw [if_pos h3]
    exact size_beta
  rw [if_neg h3]
  exact CFSG.KS.Tbl.invT_size _ _

theorem word_TR (w : List Int) : TR 1540 (wordT 1540 (genTables OJ) w) (wp w) :=
  wordT_TR (by norm_num) w fun z _ => gens_TR z

theorem be_TR : TR 1540 (genTables OJ 2) (r32 BE) := by
  have h := gens_TR 2
  have e : GJ 2 = r32 BE := funext fun x => by rw [GJ_eq]; rfl
  rwa [e] at h

theorem conj_TR (w : List Int) :
    TR 1540 (CFSG.Sporadic.J1.Sylow.Native.conjT 1540 (genTables OJ) (genTables OJ 2) w) (xp w) := by
  have h := compT_TR (word_TR w) (compT_TR be_TR (word_TR (invWord w)))
  exact h

theorem nodupB_spec : ∀ (l : List Nat) (s : Nat), nodupB l s = true →
    l.Nodup ∧ ∀ a ∈ l, s.testBit a = false
  | [], _, _ => ⟨List.nodup_nil, fun _ h => absurd h List.not_mem_nil⟩
  | a :: l, s, h => by
    have e : nodupB (a :: l) s = bAnd(Nat.beq (Nat.land (Nat.shiftRight s a) 1) 0,
        nodupB l (Nat.lor s (Nat.shiftLeft 1 a))) := rfl
    rw [e, bAnd_iff] at h
    obtain ⟨h1, h2⟩ := h
    obtain ⟨ih1, ih2⟩ := nodupB_spec l _ h2
    have ha : s.testBit a = false := by
      have e1 := Nat.eq_of_beq_eq_true h1
      rw [Nat.testBit, Nat.one_and_eq_mod_two]
      change (s >>> a) &&& 1 = 0 at e1
      rw [Nat.and_one_is_mod] at e1
      simp [e1]
    refine ⟨List.nodup_cons.2 ⟨fun hm => ?_, ih1⟩, fun b hb => ?_⟩
    · have := ih2 a hm
      change (s ||| 1 <<< a).testBit a = false at this
      rw [Nat.testBit_or, Nat.testBit_shiftLeft] at this
      simp at this
    · rcases List.mem_cons.1 hb with rfl | hb
      · exact ha
      · have := ih2 b hb
        change (s ||| 1 <<< a).testBit b = false at this
        rw [Nat.testBit_or] at this
        exact (Bool.or_eq_false_iff.1 this).1

theorem keys_disj {p q : Nat} (hpq : p < q) (hq : q < TWL.length) :
    ∀ a ∈ keys2 (TWL.getD p []), a ∉ keys2 (TWL.getD q []) := by
  have h := (nodupB_spec _ _ keysOK_ok).1
  rw [List.nodup_flatMap, List.pairwise_iff_getElem] at h
  have hd := h.2 p q (by omega) hq hpq
  rw [List.getD_eq_getElem _ _ (by omega), List.getD_eq_getElem _ _ hq]
  exact fun a ha hb => hd ha hb

theorem lens : TWL.length = 2926 ∧ NWL.length = 60 ∧ TWL.head? = some [] := by
  have h := shape_ok
  unfold shapeOK at h
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  exact ⟨h.1.1, h.1.2, h.2⟩

theorem get!_map {α β : Type} [Inhabited α] [Inhabited β] (a : Array α) (f : α → β) {i : Nat}
    (hi : i < a.size) : (a.map f)[i]! = f a[i]! := by
  rw [getElem!_pos _ i (by simpa using hi), Array.getElem_map, getElem!_pos a i hi]

theorem get!_list {α : Type} [Inhabited α] (l : List α) (d : α) {i : Nat} (hi : i < l.length) :
    l.toArray[i]! = l.getD i d := by
  rw [getElem!_pos _ i (by simpa using hi), List.getElem_toArray, List.getD_eq_getElem _ _ hi]

theorem movesAll_spec {g gi : Nat → Nat} (h : movesAll g gi = true) :
    ∀ w ∈ TWL.tail, keyOf (g (xp w (gi 0))) (g (xp w (gi 1))) ∉ keys2 w := by
  unfold movesAll at h
  generalize TWL.tail = L at h ⊢
  induction L with
  | nil => exact fun _ h => absurd h List.not_mem_nil
  | cons w L ih =>
    have e := (bAnd_iff _ _).1 h
    intro v hv
    rcases List.mem_cons.1 hv with rfl | hv
    · intro hm
      have h1 := e.1
      have hb : movesAll.memB (keyOf (g (xp v (gi 0))) (g (xp v (gi 1)))) (keys2 v) = true := by
        clear e ih h h1
        generalize keys2 v = K at hm ⊢
        induction K with
        | nil => exact absurd hm List.not_mem_nil
        | cons a K ihK =>
          change Bool.rec (motive := fun _ => Bool) (movesAll.memB _ K) true (Nat.beq a _) = true
          cases hab : Nat.beq a (keyOf (g (xp v (gi 0))) (g (xp v (gi 1))))
          · rcases List.mem_cons.1 hm with hm | hm
            · rw [← hm, Nat.beq_refl] at hab
              cases hab
            · exact ihK hm
          · rfl
      rw [hb] at h1
      cases h1
    · exact ih e.2 v hv

theorem memB_true {y : Nat} : ∀ {l : List Nat}, y ∈ l → movesAll.memB y l = true
  | a :: l, h => by
    change Bool.rec (motive := fun _ => Bool) (movesAll.memB y l) true (Nat.beq a y) = true
    cases hab : Nat.beq a y
    · rcases List.mem_cons.1 h with h | h
      · rw [← h, Nat.beq_refl] at hab
        cases hab
      · exact memB_true h
    · rfl

theorem slice_spec {L N K : Nat} {p : Nat → Bool} (hK : N ≤ K * L)
    (h : ∀ s < K, slice L N s p = true) : ∀ i < N, p i = true := by
  intro i hi
  have hL : 0 < L := by
    rcases Nat.eq_zero_or_pos L with h0 | h0
    · subst h0
      omega
    · exact h0
  have hs : i / L < K := by
    rw [Nat.div_lt_iff_lt_mul hL]
    omega
  have h' := allN_spec (h (i / L) hs) (i % L) (Nat.mod_lt _ hL)
  rw [strictB_eq] at h'
  have e : Nat.add (Nat.mul (i / L) L) (i % L) = i := by
    change i / L * L + i % L = i
    have := Nat.div_add_mod i L
    rw [Nat.mul_comm] at this
    exact this
  rw [e, Eq.mpr Nat.blt_eq hi] at h'
  exact h'

theorem tail_mem {p : Nat} (h1 : 1 ≤ p) (hp : p < TWL.length) : TWL.getD p [] ∈ TWL.tail := by
  rw [List.getD_eq_getElem _ _ hp]
  have hp' : p - 1 < TWL.tail.length := by simp; omega
  have e : TWL.tail[p - 1] = TWL[p] := by
    rw [List.getElem_tail]
    congr 1
    omega
  rw [← e]
  exact List.getElem_mem hp'

theorem tabS_lt5 {s x : Nat} (hs : s < 5) (hx : x < 1540) :
    tabS s x < 1540 ∧ tabS s x = wp (lW s) x := by
  have hf := inv_facts hx
  interval_cases s
  · exact ⟨hx, rfl⟩
  · refine ⟨hf.1, ?_⟩
    change r32 AL x = GJ 1 x
    rw [GJ_eq]
    norm_num
  · refine ⟨hf.2.2.2.2.1, ?_⟩
    change r32 AI x = GJ (-1) x
    rw [GJ_eq]
    norm_num
  · refine ⟨hf.2.2.1, ?_⟩
    change r32 BE x = GJ 2 x
    rw [GJ_eq]
    norm_num
  · refine ⟨hf.2.2.2.2.2, ?_⟩
    change r32 BI x = GJ (-2) x
    rw [GJ_eq]
    norm_num

theorem expK_lt5 : ∀ (n : Nat) {s : Nat}, s < 5 → expK n s = lW s
  | 0, _, _ => rfl
  | n + 1, s, hs => by
    have e : Nat.blt s 5 = true := Eq.mpr Nat.blt_eq hs
    change Bool.rec (motive := fun _ => List Int) _ (lW s) (Nat.blt s 5) = lW s
    rw [e]

theorem expK_rule (n k : Nat) :
    expK (n + 1) (k + 5) = List.append (expK n (ruA k)) (expK n (ruB k)) := by
  have e : Nat.blt (k + 5) 5 = false := by
    cases h : Nat.blt (k + 5) 5
    · rfl
    · have := Eq.mp Nat.blt_eq h
      omega
  have e2 : Nat.sub (k + 5) 5 = k := by
    change k + 5 - 5 = k
    omega
  change Bool.rec (motive := fun _ => List Int)
    (List.append (expK n (ruA (Nat.sub (k + 5) 5))) (expK n (ruB (Nat.sub (k + 5) 5))))
    (lW (k + 5)) (Nat.blt (k + 5) 5) = _
  rw [e, e2]

theorem ruleOK_spec {k : Nat} (h : ruleOK k = true) : ruA k < k + 5 ∧ ruB k < k + 5 ∧
    ∀ x < 1540, tabS (ruB k) x < 1540 ∧ tabS (k + 5) x = tabS (ruA k) (tabS (ruB k) x) := by
  unfold ruleOK at h
  rw [strictB_eq, strictB_eq] at h
  have h1 := (bAnd_iff _ _).1 h
  have h2 := (bAnd_iff _ _).1 h1.2
  refine ⟨Eq.mp Nat.blt_eq h1.1, Eq.mp Nat.blt_eq h2.1, fun x hx => ?_⟩
  have h3 := allN_spec h2.2 x hx
  rw [strictB_eq] at h3
  have h4 := (bAnd_iff _ _).1 h3
  exact ⟨Eq.mp Nat.blt_eq h4.1, Nat.eq_of_beq_eq_true h4.2⟩

theorem tabS_spec : ∀ (n s : Nat), s < n + 5 → s < 231 → ∀ x < 1540,
    tabS s x < 1540 ∧ tabS s x = wp (expK n s) x := by
  intro n
  induction n with
  | zero =>
    intro s hs _ x hx
    rw [expK_lt5 0 (s := s) (by omega)]
    exact tabS_lt5 (by omega) hx
  | succ n ih =>
    intro s hs hK x hx
    by_cases h5 : s < 5
    · rw [expK_lt5 _ h5]
      exact tabS_lt5 h5 hx
    · obtain ⟨k, rfl⟩ : ∃ k, s = k + 5 := ⟨s - 5, by omega⟩
      obtain ⟨ha, hb, hp⟩ := ruleOK_spec
        (slice_spec (L := 29) (N := 226) (K := 8) (p := ruleOK) (by norm_num) ruleAll k (by omega))
      obtain ⟨hy, he⟩ := hp x hx
      have IHb := ih (ruB k) (by omega) (by omega) x hx
      have IHa := ih (ruA k) (by omega) (by omega) _ hy
      rw [expK_rule, List.append_eq, he]
      refine ⟨IHa.1, ?_⟩
      rw [IHa.2, IHb.2]
      unfold wp
      rw [List.foldr_append]

theorem words_spec {i : Nat} (hi : i < 60) : wsV i < 231 ∧ wsI i < 231 ∧
    expK 300 (wsV i) = NWL.getD i [] ∧ expK 300 (wsI i) = invWord (NWL.getD i []) := by
  have h := allN_spec wordsOK_ok i hi
  rw [strictB_eq, strictB_eq] at h
  have h1 := (bAnd_iff _ _).1 h
  have h2 := (bAnd_iff _ _).1 h1.2
  have h3 := (bAnd_iff _ _).1 h2.2
  exact ⟨Eq.mp Nat.blt_eq h1.1, Eq.mp Nat.blt_eq h2.1, beq_iff_eq.1 h3.1, beq_iff_eq.1 h3.2⟩

theorem norm_pt {i : Nat} (hi : i < 60) :
    (∀ x < 1540, wp (NWL.getD i []) (r32 BE (wp (invWord (NWL.getD i [])) x)) = r32 BE x) ∨
    (∀ x < 1540, wp (NWL.getD i []) (r32 BE (wp (invWord (NWL.getD i [])) x)) =
      r32 BE (r32 BE x)) := by
  obtain ⟨hs, ht, es, et⟩ := words_spec hi
  have key : ∀ x < 1540, tabS (wsV i) (r32 BE (tabS (wsI i) x)) =
      wp (NWL.getD i []) (r32 BE (wp (invWord (NWL.getD i [])) x)) := by
    intro x hx
    have h1 := tabS_spec 300 _ (by omega) ht x hx
    rw [et] at h1
    have h2 : r32 BE (tabS (wsI i) x) < 1540 := (gens_get 2 h1.1).2
    have h3 := tabS_spec 300 _ (by omega) hs _ h2
    rw [es] at h3
    rw [h3.2, h1.2]
  have hn := slice_spec (L := 15) (N := 60) (K := 4) (p := normK) (by norm_num) normAll i hi
  unfold normK at hn
  rw [strictB_eq, strictB_eq] at hn
  cases h1 : normAtK (wsV i) (wsI i) 1
  · rw [h1] at hn
    refine Or.inr fun x hx => ?_
    rw [← key x hx]
    exact Nat.eq_of_beq_eq_true (allN_spec hn x hx)
  · refine Or.inl fun x hx => ?_
    rw [← key x hx]
    exact Nat.eq_of_beq_eq_true (allN_spec h1 x hx)

theorem sy_hTW : ∀ p < 2926, TR 1540 ((TWL.toArray.map
    (CFSG.Sporadic.J1.Sylow.Native.conjT 1540 (genTables OJ) (genTables OJ 2)))[p]!)
      (xp (TWL.getD p [])) := fun p hp => by
  obtain ⟨hl1, -, -⟩ := lens
  rw [get!_map _ _ (by simpa [hl1] using hp), get!_list TWL [] (by omega)]
  exact conj_TR _

theorem sy_hTW2 : ∀ p < 2926, TR 1540 (((TWL.toArray.map
    (CFSG.Sporadic.J1.Sylow.Native.conjT 1540 (genTables OJ) (genTables OJ 2))).map
      fun t => compT 1540 t t)[p]!) (fun x => xp (TWL.getD p []) (xp (TWL.getD p []) x)) :=
  fun p hp => by
    obtain ⟨hl1, -, -⟩ := lens
    rw [get!_map _ _ (by simpa [hl1] using hp)]
    exact compT_TR (sy_hTW p hp) (sy_hTW p hp)

theorem sy_hV : ∀ i < 60, TR 1540 ((NWL.toArray.map (wordT 1540 (genTables OJ)))[i]!)
    (wp (NWL.getD i [])) := fun i hi => by
  obtain ⟨-, hl2, -⟩ := lens
  rw [get!_map _ _ (by simpa [hl2] using hi), get!_list NWL [] (by omega)]
  exact word_TR _

theorem sy_hVi : ∀ i < 60, TR 1540 ((NWL.toArray.map fun w => wordT 1540 (genTables OJ) (invWord w))[i]!)
    (wp (invWord (NWL.getD i []))) := fun i hi => by
  obtain ⟨-, hl2, -⟩ := lens
  rw [get!_map _ _ (by simpa [hl2] using hi), get!_list NWL [] (by omega)]
  exact word_TR _

theorem sy_hb2 : TR 1540 (compT 1540 (genTables OJ 2) (genTables OJ 2)) fun x => r32 BE (r32 BE x) :=
  compT_TR be_TR be_TR

theorem sy_hkey : ∀ p < 2926, ∀ q < 2926, p < q →
    keyOf (xp (TWL.getD p []) 0) (xp (TWL.getD p []) 1) ∉ keys2 (TWL.getD q []) := by
  obtain ⟨hl1, -, -⟩ := lens
  exact fun p _ q hq hpq => keys_disj hpq (by omega) _ List.mem_cons_self

theorem sy_hfm : ∀ p < 2926, 1 ≤ p → keyOf (wp fW (xp (TWL.getD p []) (wp (invWord fW) 0)))
    (wp fW (xp (TWL.getD p []) (wp (invWord fW) 1))) ∉ keys2 (TWL.getD p []) := by
  intro p hp h1 hm
  have h := slice_spec (K := 10) (by norm_num) fMovAll p hp
  have e0 : Nat.beq p 0 = false := by
    cases p with
    | zero => omega
    | succ k => rfl
  rw [e0] at h
  change movesAll.notK (movesAll.memB _ _) = true at h
  rw [memB_true hm] at h
  exact absurd h Bool.false_ne_true

theorem sy_head : TWL.toArray[0]! = ([] : List Int) := by
  obtain ⟨hl1, -, hl3⟩ := lens
  rw [get!_list TWL [] (by omega), List.getD_eq_getElem _ _ (by omega)]
  rw [List.head?_eq_getElem?, List.getElem?_eq_getElem (by omega)] at hl3
  exact Option.some.inj hl3

theorem sy_pair : pairCheck 1540 (TWL.toArray.map
      (CFSG.Sporadic.J1.Sylow.Native.conjT 1540 (genTables OJ) (genTables OJ 2)))
    ((TWL.toArray.map (CFSG.Sporadic.J1.Sylow.Native.conjT 1540 (genTables OJ) (genTables OJ 2))).map
      fun t => compT 1540 t t) = true := by
  unfold pairCheck
  rw [allIn_eq_true]
  intro p _ hp
  rw [allIn_eq_true]
  intro q hpq hq
  simp only [Bool.and_eq_true, Bool.not_eq_true']
  refine ⟨tabEq_false_key (by norm_num) (sy_hTW p (by omega)) (sy_hTW q hq) fun e => ?_,
    tabEq_false_key (by norm_num) (sy_hTW p (by omega)) (sy_hTW2 q hq) fun e => ?_⟩
  · exact sy_hkey p (by omega) q hq (by omega) (by rw [e]; exact List.mem_cons_self)
  · exact sy_hkey p (by omega) q hq (by omega) (by rw [e]; exact List.mem_cons_of_mem _ List.mem_cons_self)

theorem sy_norm : normCheck 1540 (genTables OJ 2) (compT 1540 (genTables OJ 2) (genTables OJ 2))
    (NWL.toArray.map (wordT 1540 (genTables OJ)))
    (NWL.toArray.map fun w => wordT 1540 (genTables OJ) (invWord w)) = true := by
  obtain ⟨-, hl2, -⟩ := lens
  unfold normCheck
  simp only [Bool.and_eq_true, Bool.or_eq_true]
  refine ⟨allIn_eq_true.2 fun i _ hi => ?_, allIn_eq_true.2 fun i _ hi => ?_⟩
  · have hT := compT_TR (sy_hV i hi) (compT_TR be_TR (sy_hVi i hi))
    rcases norm_pt hi with h | h
    · exact Bool.or_eq_true_iff.2 (Or.inl (tabEq_true hT be_TR h))
    · exact Bool.or_eq_true_iff.2 (Or.inr (tabEq_true hT sy_hb2 h))
  · rw [allIn_eq_true]
    intro j hij hj
    simp only [Bool.not_eq_true']
    refine tabEq_false_key (by norm_num) (sy_hV i (by omega)) (sy_hV j hj) fun e => ?_
    have hnd := (nodupB_spec _ _ vKeys_ok).1
    rw [List.nodup_iff_injective_get] at hnd
    have hl : (NWL.map fun w => keyOf (wp w 0) (wp w 1)).length = 60 := by simp [hl2]
    have := @hnd ⟨i, by rw [hl]; omega⟩ ⟨j, by rw [hl]; omega⟩ (by
      simp only [List.get_eq_getElem, List.getElem_map]
      rw [List.getD_eq_getElem _ _ (by omega), List.getD_eq_getElem _ _ (by omega)] at e
      exact e)
    simp only [Fin.mk.injEq] at this
    omega

theorem sy_f : fCheck 1540 (NWL.toArray.map (wordT 1540 (genTables OJ)))[fIdx ()]!
    (NWL.toArray.map fun w => wordT 1540 (genTables OJ) (invWord w))[fIdx ()]!
    (TWL.toArray.map (CFSG.Sporadic.J1.Sylow.Native.conjT 1540 (genTables OJ) (genTables OJ 2)))
    ((TWL.toArray.map (CFSG.Sporadic.J1.Sylow.Native.conjT 1540 (genTables OJ) (genTables OJ 2))).map
      fun t => compT 1540 t t) = true := by
  have hf1 := slice_spec (K := 10) (by norm_num) fOrdAll
  have hf2 := fNe_ok
  unfold fNe at hf2
  unfold fCheck
  have hF : TR 1540 ((NWL.toArray.map (wordT 1540 (genTables OJ)))[17]!) (wp fW) :=
    sy_hV 17 (by norm_num)
  have hFi : TR 1540 ((NWL.toArray.map fun w => wordT 1540 (genTables OJ) (invWord w))[17]!)
      (wp (invWord fW)) := sy_hVi 17 (by norm_num)
  simp only [Bool.and_eq_true, Bool.not_eq_true']
  refine ⟨⟨?_, ?_⟩, allIn_eq_true.2 fun p h1 hp => ?_⟩
  · have hP : TR 1540 (powT 1540 5 ((NWL.toArray.map (wordT 1540 (genTables OJ)))[17]!))
        fun x => wp fW (wp fW (wp fW (wp fW (wp fW x)))) :=
      compT_TR hF (compT_TR hF (compT_TR hF (compT_TR hF (compT_TR hF (idT_TR (by norm_num))))))
    exact tabEq_true hP (idT_TR (by norm_num)) fun x hx =>
      Nat.eq_of_beq_eq_true (hf1 x hx)
  · have hm : ¬ (wp fW 0 = 0 ∧ wp fW 1 = 1) := fun ⟨a, b⟩ => by
      have e1 : Nat.beq (wp fW 0) 0 = true := by rw [a]; rfl
      have e2 : Nat.beq (wp fW 1) 1 = true := by rw [b]; rfl
      unfold movesAll.notK at hf2
      rw [e1, e2] at hf2
      exact absurd hf2 Bool.false_ne_true
    by_cases h0 : wp fW 0 = 0
    · exact tabEq_false hF (idT_TR (by norm_num)) (i := 1) (by norm_num) fun e => hm ⟨h0, e⟩
    · exact tabEq_false hF (idT_TR (by norm_num)) (i := 0) (by norm_num) h0
  · have hmv := sy_hfm p hp h1
    have hC := compT_TR hF (compT_TR (sy_hTW p hp) hFi)
    simp only [Bool.and_eq_true, Bool.not_eq_true']
    exact ⟨tabEq_false_key (by norm_num) hC (sy_hTW p hp) fun e => hmv (by rw [e]; exact List.mem_cons_self),
      tabEq_false_key (by norm_num) hC (sy_hTW2 p hp) fun e =>
        hmv (by rw [e]; exact List.mem_cons_of_mem _ List.mem_cons_self)⟩

theorem sy_b : bCheck 1540 (genTables OJ 2) (compT 1540 (genTables OJ 2) (genTables OJ 2))
    (TWL.toArray.map (CFSG.Sporadic.J1.Sylow.Native.conjT 1540 (genTables OJ) (genTables OJ 2)))
    ((TWL.toArray.map (CFSG.Sporadic.J1.Sylow.Native.conjT 1540 (genTables OJ) (genTables OJ 2))).map
      fun t => compT 1540 t t) = true := by
  obtain ⟨hl1, -, -⟩ := lens
  unfold bCheck
  rw [allIn_eq_true]
  intro p h1 hp
  have hmv := movesAll_spec b_ok _ (tail_mem h1 (by omega))
  have hC := compT_TR be_TR (compT_TR (sy_hTW p hp) sy_hb2)
  simp only [Bool.and_eq_true, Bool.not_eq_true']
  exact ⟨tabEq_false_key (by norm_num) hC (sy_hTW p hp) fun e => hmv (by rw [e]; exact List.mem_cons_self),
    tabEq_false_key (by norm_num) hC (sy_hTW2 p hp) fun e =>
      hmv (by rw [e]; exact List.mem_cons_of_mem _ List.mem_cons_self)⟩

theorem sylowCheck_of {O : type_of% OJ} (hn : O.pts.size = 1540)
    (hp : pairCheck 1540 (TWL.toArray.map
      (CFSG.Sporadic.J1.Sylow.Native.conjT 1540 (genTables O) (genTables O 2)))
      ((TWL.toArray.map (CFSG.Sporadic.J1.Sylow.Native.conjT 1540 (genTables O) (genTables O 2))).map
        fun t => compT 1540 t t) = true)
    (hm : normCheck 1540 (genTables O 2) (compT 1540 (genTables O 2) (genTables O 2))
      (NWL.toArray.map (wordT 1540 (genTables O)))
      (NWL.toArray.map fun w => wordT 1540 (genTables O) (invWord w)) = true)
    (hf : fCheck 1540 (NWL.toArray.map (wordT 1540 (genTables O)))[fIdx ()]!
      (NWL.toArray.map fun w => wordT 1540 (genTables O) (invWord w))[fIdx ()]!
      (TWL.toArray.map (CFSG.Sporadic.J1.Sylow.Native.conjT 1540 (genTables O) (genTables O 2)))
      ((TWL.toArray.map (CFSG.Sporadic.J1.Sylow.Native.conjT 1540 (genTables O) (genTables O 2))).map
        fun t => compT 1540 t t) = true)
    (hb : bCheck 1540 (genTables O 2) (compT 1540 (genTables O 2) (genTables O 2))
      (TWL.toArray.map (CFSG.Sporadic.J1.Sylow.Native.conjT 1540 (genTables O) (genTables O 2)))
      ((TWL.toArray.map (CFSG.Sporadic.J1.Sylow.Native.conjT 1540 (genTables O) (genTables O 2))).map
        fun t => compT 1540 t t) = true) :
    sylowCheck O = true := by
  obtain ⟨hl1, hl2, -⟩ := lens
  unfold sylowCheck share
  simp only [hn, tw_eq, nw_eq, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq]
  exact ⟨⟨⟨⟨⟨⟨⟨⟨trivial, by simp [hl1]⟩, by simp [hl2]⟩, by decide⟩, sy_head⟩, hp⟩, hm⟩, hf⟩, hb⟩

theorem sylow_ok : sylowCheck OJ = true :=
  sylowCheck_of size_OJ sy_pair sy_norm sy_f sy_b

end CertificateChecks.KernelJ1Syl

end
