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
  exact ⟨PP_of_permOK hsz h.1, PP_of_permOK hsz h.2⟩

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

theorem wordChk_all : ∀ k < 19, wordChk k = true := by
  intro k hk
  interval_cases k
  exacts [wordChk0, wordChk1, wordChk2, wordChk3, wordChk4, wordChk5, wordChk6, wordChk7,
    wordChk8, wordChk9, wordChk10, wordChk11, wordChk12, wordChk13, wordChk14, wordChk15,
    wordChk16, wordChk17, wordChk18]

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
  have hc : wK Gab (wordsK.getD k []) = W k := Nat.eq_of_beq_eq_true (wordChk_all k hk)
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

theorem atChunk_all : ∀ i < 19, atChunk i = true := by
  intro i hi
  interval_cases i
  exacts [atChunk0, atChunk1, atChunk2, atChunk3, atChunk4, atChunk5, atChunk6, atChunk7,
    atChunk8, atChunk9, atChunk10, atChunk11, atChunk12, atChunk13, atChunk14, atChunk15,
    atChunk16, atChunk17, atChunk18]

theorem atoms_ok : (atoms ()).all (·.checkA (tabs ())) = true := by
  rw [List.all_eq_true]
  intro x hx
  rw [at_eq]
  exact all_of_chunks (p := atK W) (d := At.eq .one .one) (c := 40) (n := 19) (by norm_num)
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
