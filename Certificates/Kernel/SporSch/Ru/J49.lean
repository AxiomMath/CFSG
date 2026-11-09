module

public import Certificates.Kernel.SporSch.Ru.J49K
public import Certificates.Kernel.SporSch.Ru.G2Ru7164
public import CFSG.Certificates.Kernel.SporSch.IntLinesSound

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSporSch.RuJ49

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KC.IntLines CFSG.KC.BfsPin
  CertificateChecks.KernelSporSch.RuG CertificateChecks.KernelSporSch.G2Ru7164
  CFSG.Sporadic.RuSchreier CFSG.Sporadic.RuSchreier.J49 CFSG.Sporadic.RuSchreier.J49.Sl2
  CFSG.Monster.B.Co2.Native

theorem all_of_chunks {α : Type} {l : List α} {p : α → Bool} {d : α} {c n : Nat} (hc : 0 < c)
    (hlen : l.length ≤ c * n)
    (h : ∀ i < n, (List.range c).all (fun j => p (l.getD (c * i + j) d)) = true) :
    ∀ x ∈ l, p x = true := by
  intro x hx
  obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hx
  have hin : i / c < n :=
    (Nat.div_lt_iff_lt_mul hc).2 (lt_of_lt_of_le hi (by rw [Nat.mul_comm]; exact hlen))
  have := List.all_eq_true.1 (h (i / c) hin) (i % c) (List.mem_range.2 (Nat.mod_lt _ hc))
  rwa [Nat.div_add_mod, List.getD_eq_getElem _ _ hi] at this

theorem wordList_eq : wordList () = wordsK := by
  unfold wordList wordsK
  rw [JW_eq, List.map_map, List.map_map]
  exact lines_parse textW List.reverse

theorem parseRow_eq (s : String) :
    parseRow s = rowOf ((s.splitOn " ").filterMap String.toInt?) := by
  unfold parseRow rowOf
  cases (s.splitOn " ").filterMap String.toInt? <;> rfl

theorem rows_eq : rows () = rowsK := by
  unfold rows rowsK
  rw [JR_eq]
  have e : parseRow = fun s => rowOf ((s.splitOn " ").filterMap String.toInt?) := funext parseRow_eq
  rw [e]
  exact lines_parse textR rowOf

theorem words_facts : wordsK.length = 19 ∧ wordsK.all (lettersOK 2) = true := by
  have h := wordsOK
  simp only [Bool.and_eq_true, Nat.beq_eq] at h
  exact h

theorem letters_of {w : List Int} {j : Nat} (h : lettersOK j w = true) :
    ∀ l ∈ w, l ≠ 0 ∧ l.natAbs ≤ j := by
  intro l hl
  have := List.all_eq_true.1 h l hl
  simp only [Bool.and_eq_true, bne_iff_ne, ne_eq, decide_eq_true_eq] at this
  exact this

theorem permAB : P A0 ∧ P A1 := by
  have h := permA
  simp only [bAnd_iff] at h
  exact ⟨PP_of_permOK hsz h.1.1, PP_of_permOK hsz h.2.1⟩

theorem GabI_eq (j : Nat) : GabI j = pinv (Gab j) := by
  have h := permA
  simp only [bAnd_iff] at h
  unfold GabI Gab
  cases Nat.beq j 0
  · exact (Nat.eq_of_beq_eq_true h.2.2).symm
  · exact (Nat.eq_of_beq_eq_true h.1.2).symm

theorem P_Gab (j : Nat) : P (Gab j) := by
  unfold Gab
  cases Nat.beq j 0
  · exact permAB.2
  · exact permAB.1

theorem j49kP_letK (l : Int) : P (letK Gab l) := by
  unfold letK
  cases decide (0 < l)
  · exact P_pinv (P_Gab _)
  · exact P_Gab _

theorem letKJ_eq (l : Int) : letKJ l = letK Gab l := by
  unfold letKJ letK
  rw [GabI_eq]

theorem pc_assoc' {p q r : Nat} (hp : P p) (hr : P r) : pc (pc p q) r = pc p (pc q r) := by
  obtain ⟨hn, hw, -, -⟩ := CFSG.KS.PF.canon_facts hp.1
  obtain ⟨-, -, -, hrr⟩ := CFSG.KS.PF.canon_facts hr.1
  have hn32 : 4060 < 2 ^ 32 := by omega
  have hw0 := CFSG.KS.PF.w_pos hw
  refine CFSG.KS.PF.eq_of_fields hw0 (CFSG.KS.PF.pcomp_shr _ _ hn32 hw0)
    (CFSG.KS.PF.pcomp_shr _ _ hn32 hw0) fun i hi => ?_
  unfold pc
  rw [CFSG.KS.PF.pg_pcomp hn32 hi, CFSG.KS.PF.pg_pcomp hn32 (hrr i hi),
    CFSG.KS.PF.pg_pcomp hn32 hi, CFSG.KS.PF.pg_pcomp hn32 hi]

theorem j49kPair_eq {a b : Int} (ha : a ≠ 0 ∧ a.natAbs ≤ 2) (hb : b ≠ 0 ∧ b.natAbs ≤ 2) :
    j49kPair a b = pc (letK Gab a) (letK Gab b) := by
  have hm : ∀ l : Int, l ≠ 0 ∧ l.natAbs ≤ 2 → l ∈ ([-2, -1, 1, 2] : List Int) := by
    intro l hl
    simp only [List.mem_cons, List.not_mem_nil, or_false]
    omega
  have h := List.all_eq_true.1 (List.all_eq_true.1 j49kPairOK a (hm a ha)) b (hm b hb)
  rw [← letKJ_eq, ← letKJ_eq]
  exact (Nat.eq_of_beq_eq_true h).symm

theorem wKP_eq : ∀ (w : List Int) {acc : Nat}, (∀ l ∈ w, l ≠ 0 ∧ l.natAbs ≤ 2) → P acc →
    wKP w acc = wKA Gab w acc ∧ P (wKA Gab w acc)
  | [], _, _, hacc => ⟨rfl, hacc⟩
  | [a], acc, _, hacc => by
    have e : wKP [a] acc = pc (letKJ a) acc := by simp only [wKP]
    rw [e, letKJ_eq]
    exact ⟨rfl, P_pc (j49kP_letK a) hacc⟩
  | a :: b :: w, acc, hw, hacc => by
    obtain ⟨ih, hP⟩ := wKP_eq w (fun l hl => hw l (by simp [hl])) hacc
    have e : wKP (a :: b :: w) acc = pc (j49kPair a b) (wKP w acc) := by simp only [wKP]
    change wKP (a :: b :: w) acc = pc (letK Gab a) (pc (letK Gab b) (wKA Gab w acc)) ∧
      P (pc (letK Gab a) (pc (letK Gab b) (wKA Gab w acc)))
    rw [e, ih, j49kPair_eq (hw a (by simp)) (hw b (by simp)), pc_assoc' (j49kP_letK a) hP]
    exact ⟨rfl, P_pc (j49kP_letK a) (P_pc (j49kP_letK b) hP)⟩

theorem seed_eq {w : List Int} (hw : ∀ l ∈ w, l ≠ 0 ∧ l.natAbs ≤ 2) :
    ruSeedWordA w = unpack 4060 12 (wK Gab w) ∧ P (wK Gab w) := by
  have hb : ∀ j < 2, (#[ruA0A, ruA1A] : Array (Array Nat))[j]! = unpack 4060 12 (Gab j) := by
    intro j hj
    interval_cases j
    · exact a0_eq
    · exact a1_eq
  have hP : ∀ j < 2, P (Gab j) := by
    intro j hj
    interval_cases j
    · exact permAB.1
    · exact permAB.2
  have e : ruSeedWordA w =
      wordA 4060 #[ruA0A, ruA1A] (Array.map (invCand 4060) #[ruA0A, ruA1A]) w := by
    unfold ruSeedWordA
    simp [ruInv]
  rw [e]
  exact wordA_eq (by rfl) hb hP w hw

theorem wK_append (G : Nat → Nat) (b : List Int) : ∀ a : List Int, wK G (a ++ b) = wKA G a (wK G b)
  | [] => rfl
  | l :: a => congrArg (pc (letK G l)) (wK_append G b a)

theorem j49kWord_eq {k : Nat} (hk : k < 19) (hw : ∀ l ∈ wordsK.getD k [], l ≠ 0 ∧ l.natAbs ≤ 2) :
    wK Gab (wordsK.getD k []) = W k := by
  have he := List.all_eq_true.1 chunkEnds k (List.mem_range.2 hk)
  simp only [Bool.and_eq_true] at he
  obtain ⟨⟨h13, hend⟩, hstart⟩ := he
  have h13' : j49kNChk k < 13 := Nat.blt_eq.mp h13
  rw [← Nat.eq_of_beq_eq_true hstart]
  refine CFSG.KS.SporSch.chunks_eq (f := wK Gab) (wd := wordsK.getD k []) (c := 32)
    (K := j49kNChk k) (P := fun q => Suf (13 * k + q)) (by unfold j49kNChk; omega)
    (Nat.eq_of_beq_eq_true hend).symm fun q hq ih => ?_
  have h := SufC.all (13 * k + q) (by change 13 * k + q < 247; omega)
  have e1 : (13 * k + q) / 13 = k := by omega
  have e2 : (13 * k + q) % 13 = q := by omega
  unfold j49kChunkOK at h
  rw [e1, e2, Nat.blt_eq.mpr hq] at h
  have h' := Nat.eq_of_beq_eq_true h
  rw [CFSG.KS.SporSch.takeK_eq, CFSG.KS.SporSch.dropK_eq, Nat.add_assoc] at h'
  have hP : P (Suf (13 * k + (q + 1))) := by
    rw [← ih]
    exact (seed_eq fun l hl => hw l (List.mem_of_mem_drop hl)).2
  have hc := wKP_eq (List.take 32 (List.drop (32 * q) (wordsK.getD k []))) (fun l hl => hw l (List.mem_of_mem_drop (List.mem_of_mem_take hl))) hP
  rw [wK_append, ih, ← hc.1]
  exact h'

theorem tabs_size : (tabs ()).size = 19 := by
  unfold tabs
  rw [wordList_eq, List.size_toArray, List.length_map, words_facts.1]

theorem tab_get {k : Nat} (hk : k < 19) : (tabs ())[k]! = unpack 4060 12 (W k) ∧ P (W k) := by
  have hl : k < wordsK.length := by rw [words_facts.1]; exact hk
  have e : (tabs ())[k]! = ruSeedWordA (wordsK.getD k []) := by
    rw [getElem!_pos _ k (by rw [tabs_size]; exact hk)]
    unfold tabs
    simp only [wordList_eq, List.getElem_toArray, List.getElem_map, List.getD_eq_getElem _ _ hl]
  have hw : ∀ l ∈ wordsK.getD k [], l ≠ 0 ∧ l.natAbs ≤ 2 := by
    rw [List.getD_eq_getElem _ _ hl]
    exact letters_of (List.all_eq_true.1 words_facts.2 _ (List.getElem_mem hl))
  have hc : wK Gab (wordsK.getD k []) = W k := j49kWord_eq hk hw
  rw [e, ← hc]
  exact seed_eq hw

theorem tabOf_eq {k : Nat} (hk : k < 19) : tabOf (tabs ()) k = unpack 4060 12 (W k) ∧ P (W k) := by
  unfold tabOf
  rw [if_pos (by rw [tabs_size]; exact hk)]
  exact tab_get hk

theorem ex_eq (e : Ex) : e.evalA (tabs ()) = unpack 4060 12 (exK W e) ∧ P (exK W e) := by
  induction e with
  | el k =>
    change tabOf (tabs ()) k = unpack 4060 12
      (Bool.rec (motive := fun _ => Nat) pid (W k) (Nat.blt k 19)) ∧
      P (Bool.rec (motive := fun _ => Nat) pid (W k) (Nat.blt k 19))
    by_cases hk : k < 19
    · have hb : Nat.blt k 19 = true := by simpa using hk
      rw [hb]
      exact tabOf_eq hk
    · have hb : Nat.blt k 19 = false := Bool.eq_false_iff.2 fun h => hk (by simpa using h)
      rw [hb]
      unfold tabOf
      rw [if_neg (by rw [tabs_size]; exact hk)]
      exact ⟨G2Ru7164.id_eq, P_pid⟩
  | one => exact ⟨G2Ru7164.id_eq, P_pid⟩
  | mul a b iha ihb =>
    change compA 4060 (a.evalA (tabs ())) (b.evalA (tabs ())) = unpack 4060 12 (pc (exK W a) (exK W b)) ∧
      P (pc (exK W a) (exK W b))
    rw [iha.1, ihb.1, comp_eq iha.2 ihb.2]
    exact ⟨rfl, P_pc iha.2 ihb.2⟩
  | pow a n ih =>
    change powA 4060 (a.evalA (tabs ())) n = unpack 4060 12 (powK (exK W a) n) ∧ P (powK (exK W a) n)
    rw [ih.1]
    exact powA_eq ih.2 n

theorem exEq_eq (a b : Ex) :
    eqA 4060 (a.evalA (tabs ())) (b.evalA (tabs ())) = Nat.beq (exK W a) (exK W b) := by
  rw [(ex_eq a).1, (ex_eq b).1, eq_eq (ex_eq a).2 (ex_eq b).2]

theorem at_eq (x : At) : x.checkA (tabs ()) = atK W x := by
  induction x with
  | eq a b =>
    change eqA 4060 (a.evalA (tabs ())) (b.evalA (tabs ())) = Nat.beq (exK W a) (exK W b)
    exact exEq_eq a b
  | ne a b =>
    change (!eqA 4060 (a.evalA (tabs ())) (b.evalA (tabs ()))) = !Nat.beq (exK W a) (exK W b)
    rw [exEq_eq a b]
  | eqAny a cs =>
    change (cs.any fun c => eqA 4060 (a.evalA (tabs ())) (c.evalA (tabs ()))) =
      cs.any fun c => Nat.beq (exK W a) (exK W c)
    congr 1
    funext c
    exact exEq_eq a c
  | imp h c ih ic =>
    change (!h.checkA (tabs ()) || c.checkA (tabs ())) = (!atK W h || atK W c)
    rw [ih, ic]

theorem atChunk_all : ∀ i < 37, atChunk i = true := by
  intro i hi
  interval_cases i
  exacts [atChunk0, atChunk1, atChunk2, atChunk3, atChunk4, atChunk5, atChunk6, atChunk7,
    atChunk8, atChunk9, atChunk10, atChunk11, atChunk12, atChunk13, atChunk14, atChunk15,
    atChunk16, atChunk17, atChunk18, atChunk19, atChunk20, atChunk21, atChunk22, atChunk23,
    atChunk24, atChunk25, atChunk26, atChunk27, atChunk28, atChunk29, atChunk30, atChunk31,
    atChunk32, atChunk33, atChunk34, atChunk35, atChunk36]

theorem atoms_ok : (atoms ()).all (·.checkA (tabs ())) = true := by
  rw [List.all_eq_true]
  intro x hx
  rw [at_eq]
  exact all_of_chunks (p := atK W) (d := At.eq .one .one) (c := 20) (n := 37) (by norm_num)
    (by rw [Nat.eq_of_beq_eq_true atomsLen]; norm_num) (fun i hi => atChunk_all i hi) x hx

open Certificates in
theorem c7350 : CFSG.Sporadic.RuSchreier.J49.check () = true := by
  have h1 : ((wordList ()).length == 19) = true := by
    rw [wordList_eq, words_facts.1]
    rfl
  have h2 : (wordList ()).all (lettersOK 2) = true := by
    rw [wordList_eq]
    exact words_facts.2
  unfold J49.check
  simp only [h1, h2, atoms_ok, Bool.and_self]

theorem lookup_prop {Q : List Int → Prop} (k : Nat) :
    ∀ R : List (Nat × List Int), (∀ r ∈ R, Q r.2) → Q [] → Q ((R.lookup k).getD [])
  | [], _, h0 => h0
  | (a, b) :: R, h, h0 => by
    by_cases hk : k = a
    · subst hk
      simp only [List.lookup, beq_self_eq_true, Option.getD_some]
      exact h (k, b) List.mem_cons_self
    · have hb : (k == a) = false := by simpa using hk
      simp only [List.lookup, hb]
      exact lookup_prop k R (fun r hr => h r (List.mem_cons_of_mem _ hr)) h0

theorem rows_letters : ∀ r ∈ rowsK, ∀ l ∈ r.2, l ≠ 0 ∧ l.natAbs ≤ 2 := by
  have h := sl2Pure
  simp only [Bool.and_eq_true] at h
  intro r hr l hl
  have := List.all_eq_true.1 (List.all_eq_true.1 h.2 r hr) l hl
  simp only [Bool.or_eq_true, beq_iff_eq] at this
  rcases this with rfl | rfl <;> decide

theorem key_letters (k : Nat) : ∀ l ∈ wordOf rowsK k, l ≠ 0 ∧ l.natAbs ≤ 2 := by
  unfold wordOf
  exact lookup_prop (Q := fun w => ∀ l ∈ w, l ≠ 0 ∧ l.natAbs ≤ 2) k rowsK rows_letters
    (fun l hl => absurd hl List.not_mem_nil)

theorem tab_eq (k : Nat) :
    tabK #[unpack 4060 12 (W 0), unpack 4060 12 (W 3)]
      #[ruInv (unpack 4060 12 (W 0)), ruInv (unpack 4060 12 (W 3))] rowsK k =
      unpack 4060 12 (tabKK k) ∧ P (tabKK k) := by
  have hb : ∀ j < 2, (#[unpack 4060 12 (W 0), unpack 4060 12 (W 3)] : Array (Array Nat))[j]! =
      unpack 4060 12 (G03 j) := by
    intro j hj
    interval_cases j <;> rfl
  have hP : ∀ j < 2, P (G03 j) := by
    intro j hj
    interval_cases j
    · exact (tab_get (k := 0) (by norm_num)).2
    · exact (tab_get (k := 3) (by norm_num)).2
  have e : tabK #[unpack 4060 12 (W 0), unpack 4060 12 (W 3)]
      #[ruInv (unpack 4060 12 (W 0)), ruInv (unpack 4060 12 (W 3))] rowsK k =
      wordA 4060 #[unpack 4060 12 (W 0), unpack 4060 12 (W 3)]
        (Array.map (invCand 4060) #[unpack 4060 12 (W 0), unpack 4060 12 (W 3)]) (wordOf rowsK k) := by
    unfold tabK
    simp [ruInv]
  rw [e]
  exact wordA_eq (by rfl) hb hP _ (key_letters k)

theorem keyChunk_all : ∀ i < 12, keyChunk i = true := by
  intro i hi
  interval_cases i
  exacts [keyChunk0, keyChunk1, keyChunk2, keyChunk3, keyChunk4, keyChunk5, keyChunk6, keyChunk7,
    keyChunk8, keyChunk9, keyChunk10, keyChunk11]

theorem keys_ok : ∀ k ∈ slKeys (), keyK k = true := by
  have h := sl2Pure
  simp only [Bool.and_eq_true] at h
  obtain ⟨⟨-, hlen⟩, -⟩ := h
  have hl : (slKeys ()).length = 120 := by simpa using hlen
  exact all_of_chunks (p := keyK) (d := 126) (c := 10) (n := 12) (by norm_num) (by rw [hl])
    (fun i hi => keyChunk_all i hi)

open Certificates in
theorem c7351 : CFSG.Sporadic.RuSchreier.J49.Sl2.check () = true := by
  have h1 : ((wordList ()).length == 19) = true := by
    rw [wordList_eq, words_facts.1]
    rfl
  have h2 : (wordList ()).all (lettersOK 2) = true := by
    rw [wordList_eq]
    exact words_facts.2
  have P0 := (tab_get (k := 0) (by norm_num)).2
  have P3 := (tab_get (k := 3) (by norm_num)).2
  have h3 : checkG (tabOf (tabs ()) 0) (tabOf (tabs ()) 3) = true := by
    rw [(tabOf_eq (k := 0) (by norm_num)).1, (tabOf_eq (k := 3) (by norm_num)).1]
    have hp := sl2Pure
    simp only [Bool.and_eq_true] at hp
    obtain ⟨⟨⟨⟨⟨⟨hr, hkp⟩, h126⟩, h533⟩, h107⟩, -⟩, -⟩ := hp
    have i0 := (inv_of rfl permChk0).2
    have i3 := (inv_of rfl permChk3).2
    have hA : (slKeys ()).all (fun k =>
        eqA 4060 (tabK #[unpack 4060 12 (W 0), unpack 4060 12 (W 3)]
          #[ruInv (unpack 4060 12 (W 0)), ruInv (unpack 4060 12 (W 3))] rowsK (keyMul k 533))
          (compA 4060 (tabK #[unpack 4060 12 (W 0), unpack 4060 12 (W 3)]
            #[ruInv (unpack 4060 12 (W 0)), ruInv (unpack 4060 12 (W 3))] rowsK k)
            (unpack 4060 12 (W 0))) &&
        eqA 4060 (tabK #[unpack 4060 12 (W 0), unpack 4060 12 (W 3)]
          #[ruInv (unpack 4060 12 (W 0)), ruInv (unpack 4060 12 (W 3))] rowsK (keyMul k 107))
          (compA 4060 (tabK #[unpack 4060 12 (W 0), unpack 4060 12 (W 3)]
            #[ruInv (unpack 4060 12 (W 0)), ruInv (unpack 4060 12 (W 3))] rowsK k)
            (unpack 4060 12 (W 3)))) = true := by
      rw [List.all_eq_true]
      intro k hk
      have hK := keys_ok k hk
      unfold keyK at hK
      simp only [Bool.and_eq_true] at hK
      rw [(tab_eq (keyMul k 533)).1, (tab_eq k).1, (tab_eq (keyMul k 107)).1,
        comp_eq (tab_eq k).2 P0, comp_eq (tab_eq k).2 P3,
        eq_eq (tab_eq (keyMul k 533)).2 (P_pc (tab_eq k).2 P0),
        eq_eq (tab_eq (keyMul k 107)).2 (P_pc (tab_eq k).2 P3), hK.1.1, hK.1.2]
      rfl
    have hB : (slKeys ()).all (fun k => k == 126 ||
        !eqA 4060 (tabK #[unpack 4060 12 (W 0), unpack 4060 12 (W 3)]
          #[ruInv (unpack 4060 12 (W 0)), ruInv (unpack 4060 12 (W 3))] rowsK k) (idA 4060)) =
        true := by
      rw [List.all_eq_true]
      intro k hk
      have hK := keys_ok k hk
      unfold keyK at hK
      simp only [Bool.and_eq_true] at hK
      rw [(tab_eq k).1, G2Ru7164.id_eq, eq_eq (tab_eq k).2 P_pid]
      exact hK.2
    unfold checkG
    simp only [rows_eq, i0, i3, hr, hkp, h126, h533, h107, hA, hB, Bool.and_self]
  unfold Sl2.check
  simp only [h1, h2, h3, Bool.and_self]

end CertificateChecks.KernelSporSch.RuJ49

end
