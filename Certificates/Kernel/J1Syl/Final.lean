module

public import Certificates.Kernel.J1Syl.Checks
public import Certificates.Kernel.Sporadic.J1K.Final
public import Certificates.Kernel.J1Syl.ChecksN
public import Certificates.Kernel.J1Syl.ChecksM
public import Certificates.Kernel.J1Syl.ChecksF
public import Certificates.Kernel.J1Syl.ChecksG
public import CFSG.Certificates.Kernel.Spor.TabWords
public import CFSG.Certificates.Kernel.Co1PTextSound
public import CFSG.Sporadic.Th.TableSpec
public import CFSG.Certificates.Kernel.SporSch.TblSound

public section

set_option maxRecDepth 400000

#kon_join CertificateChecks.KernelJ1Syl.normAll CertificateChecks.KernelJ1Syl.normOK 60
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

theorem sylow_ok : sylowCheck OJ = true := by
  obtain ⟨hl1, hl2, hl3⟩ := lens
  have hTW : ∀ p < 2926, TR 1540 ((TWL.toArray.map
      (CFSG.Sporadic.J1.Sylow.Native.conjT 1540 (genTables OJ) (genTables OJ 2)))[p]!)
        (xp (TWL.getD p [])) := fun p hp => by
    rw [get!_map _ _ (by simpa [hl1] using hp), get!_list TWL [] (by omega)]
    exact conj_TR _
  have hTW2 : ∀ p < 2926, TR 1540 (((TWL.toArray.map
      (CFSG.Sporadic.J1.Sylow.Native.conjT 1540 (genTables OJ) (genTables OJ 2))).map
        fun t => compT 1540 t t)[p]!) (fun x => xp (TWL.getD p []) (xp (TWL.getD p []) x)) :=
    fun p hp => by
      rw [get!_map _ _ (by simpa [hl1] using hp)]
      exact compT_TR (hTW p hp) (hTW p hp)
  have hV : ∀ i < 60, TR 1540 ((NWL.toArray.map (wordT 1540 (genTables OJ)))[i]!)
      (wp (NWL.getD i [])) := fun i hi => by
    rw [get!_map _ _ (by simpa [hl2] using hi), get!_list NWL [] (by omega)]
    exact word_TR _
  have hVi : ∀ i < 60, TR 1540 ((NWL.toArray.map fun w => wordT 1540 (genTables OJ) (invWord w))[i]!)
      (wp (invWord (NWL.getD i []))) := fun i hi => by
    rw [get!_map _ _ (by simpa [hl2] using hi), get!_list NWL [] (by omega)]
    exact word_TR _
  have hb2 : TR 1540 (compT 1540 (genTables OJ 2) (genTables OJ 2)) fun x => r32 BE (r32 BE x) :=
    compT_TR be_TR be_TR
  have hkey : ∀ p < 2926, ∀ q < 2926, p < q →
      keyOf (xp (TWL.getD p []) 0) (xp (TWL.getD p []) 1) ∉ keys2 (TWL.getD q []) :=
    fun p _ q hq hpq => keys_disj hpq (by omega) _ List.mem_cons_self
  have hf1 := slice_spec (K := 10) (by norm_num) fOrdAll
  have hf2 := fNe_ok
  unfold fNe at hf2
  have hfm : ∀ p < 2926, 1 ≤ p → keyOf (wp fW (xp (TWL.getD p []) (wp (invWord fW) 0)))
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
  unfold sylowCheck share
  simp only [size_OJ, tw_eq, nw_eq, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq]
  refine ⟨⟨⟨⟨⟨⟨⟨⟨trivial, by simp [hl1]⟩, by simp [hl2]⟩, by decide⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩
  · rw [get!_list TWL [] (by omega), List.getD_eq_getElem _ _ (by omega)]
    rw [List.head?_eq_getElem?, List.getElem?_eq_getElem (by omega)] at hl3
    exact Option.some.inj hl3
  ·
    unfold pairCheck
    rw [allIn_eq_true]
    intro p _ hp
    rw [allIn_eq_true]
    intro q hpq hq
    simp only [Bool.and_eq_true, Bool.not_eq_true']
    refine ⟨tabEq_false_key (by norm_num) (hTW p (by omega)) (hTW q hq) fun e => ?_,
      tabEq_false_key (by norm_num) (hTW p (by omega)) (hTW2 q hq) fun e => ?_⟩
    · exact hkey p (by omega) q hq (by omega) (by rw [e]; exact List.mem_cons_self)
    · exact hkey p (by omega) q hq (by omega) (by rw [e]; exact List.mem_cons_of_mem _ List.mem_cons_self)
  ·
    unfold normCheck
    simp only [Bool.and_eq_true, Bool.or_eq_true]
    refine ⟨allIn_eq_true.2 fun i _ hi => ?_, allIn_eq_true.2 fun i _ hi => ?_⟩
    · have hn := normAll i hi
      have hT := compT_TR (hV i hi) (compT_TR be_TR (hVi i hi))
      unfold normOK at hn
      cases h1 : normAt (NWL.getD i []) 1
      · rw [h1] at hn
        refine Bool.or_eq_true_iff.2 (Or.inr (tabEq_true hT hb2 fun x hx => ?_))
        exact Nat.eq_of_beq_eq_true (allN_spec hn x hx)
      · refine Bool.or_eq_true_iff.2 (Or.inl (tabEq_true hT be_TR fun x hx => ?_))
        exact Nat.eq_of_beq_eq_true (allN_spec h1 x hx)
    · rw [allIn_eq_true]
      intro j hij hj
      simp only [Bool.not_eq_true']
      refine tabEq_false_key (by norm_num) (hV i (by omega)) (hV j hj) fun e => ?_
      have hnd := (nodupB_spec _ _ vKeys_ok).1
      rw [List.nodup_iff_injective_get] at hnd
      have hl : (NWL.map fun w => keyOf (wp w 0) (wp w 1)).length = 60 := by simp [hl2]
      have := @hnd ⟨i, by rw [hl]; omega⟩ ⟨j, by rw [hl]; omega⟩ (by
        simp only [List.get_eq_getElem, List.getElem_map]
        rw [List.getD_eq_getElem _ _ (by omega), List.getD_eq_getElem _ _ (by omega)] at e
        exact e)
      simp only [Fin.mk.injEq] at this
      omega
  ·
    unfold fCheck
    have hF : TR 1540 ((NWL.toArray.map (wordT 1540 (genTables OJ)))[17]!) (wp fW) :=
      hV 17 (by norm_num)
    have hFi : TR 1540 ((NWL.toArray.map fun w => wordT 1540 (genTables OJ) (invWord w))[17]!)
        (wp (invWord fW)) := hVi 17 (by norm_num)
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
    · have hmv := hfm p hp h1
      have hC := compT_TR hF (compT_TR (hTW p hp) hFi)
      simp only [Bool.and_eq_true, Bool.not_eq_true']
      exact ⟨tabEq_false_key (by norm_num) hC (hTW p hp) fun e => hmv (by rw [e]; exact List.mem_cons_self),
        tabEq_false_key (by norm_num) hC (hTW2 p hp) fun e =>
          hmv (by rw [e]; exact List.mem_cons_of_mem _ List.mem_cons_self)⟩
  ·
    unfold bCheck
    rw [allIn_eq_true]
    intro p h1 hp
    have hmv := movesAll_spec b_ok _ (tail_mem h1 (by omega))
    have hC := compT_TR be_TR (compT_TR (hTW p hp) hb2)
    simp only [Bool.and_eq_true, Bool.not_eq_true']
    exact ⟨tabEq_false_key (by norm_num) hC (hTW p hp) fun e => hmv (by rw [e]; exact List.mem_cons_self),
      tabEq_false_key (by norm_num) hC (hTW2 p hp) fun e =>
        hmv (by rw [e]; exact List.mem_cons_of_mem _ List.mem_cons_self)⟩

end CertificateChecks.KernelJ1Syl

end
