module

public import Certificates.Kernel.Sporadic.ON2.Checks
public import Certificates.Kernel.Sporadic.ON.Assemble
public import CFSG.Certificates.Kernel.Spor.TabWords
public import CFSG.Certificates.Kernel.Spor.WordsTxtSound
import CFSG.Certificates.Kernel.Common.Harness
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.IntervalCases
public import Std.Tactic.BVDecide.Normalize.Prop

public section

set_option maxRecDepth 400000

#ks_chars CertificateChecks.KernelSpor.ONRootW CFSG.Sporadic.ON.Native.rootDigits

namespace CertificateChecks.KernelSpor.ON2

open CFSG.KC.Enum CFSG.KS CFSG.KS.ON CFSG.KS.Words CFSG.KS.TW CFSG.F3.Native CFSG.Sporadic.Fi23.Native
open CFSG.Sporadic.ON.Native CFSG.Sporadic.Th.Native CFSG.Perm.Native
open CFSG.Sporadic.Bridge.ONGPL.Native CFSG.ONSchreier.Native
open CertificateChecks.KernelSpor.ON (cols_of canon_of list_eq colsAK colsBK pt_of strictB_eq')

theorem colsAK2 : colsK ONW.CA ONSeedA.chars = true := by quickRfl
theorem colsBK2 : colsK ONW.CB ONSeedB.chars = true := by quickRfl
theorem rootK2 : digitsK ONRootW.chars (key ONW.K 0) = true := by quickRfl
theorem listA2 : allN 154 (fun j => Nat.beq (List.getD ONW.LA j 0) (ONW.CA j)) = true := by quickRfl
theorem listB2 : allN 154 (fun j => Nat.beq (List.getD ONW.LB j 0) (ONW.CB j)) = true := by quickRfl
theorem nx0 : Nat.beq (ONW.NX 0) 1 = true := by quickRfl
theorem nx1 : Nat.beq (ONW.NX 1023) 245520 = true := by quickRfl

theorem codesI : allN 7 (fun k => allN (IMW.WL k) fun p =>
    Nat.blt (Nat.land (Nat.shiftRight (IMW.WC k) (Nat.mul 4 p)) 15) 4) = true := by quickRfl

theorem codesS : allN 2 (fun k => allN (SRW.WL k) fun p =>
    Nat.blt (Nat.land (Nat.shiftRight (SRW.WC k) (Nat.mul 4 p)) 15) 14) = true := by quickRfl

theorem codesR : allN 29 (fun k => allN (RLW.WL k) fun p =>
    Nat.blt (Nat.land (Nat.shiftRight (RLW.WC k) (Nat.mul 4 p)) 15) 14) = true := by quickRfl

theorem relN : Nat.beq RLW.N 29 = true := by quickRfl

theorem cqOK : allN 154 (fun t => Nat.blt (cq t) 245520) = true := by quickRfl

theorem invWords : ∀ k < 7, decW (IIW.WC k) (IIW.WL k) =
    (decW (IMW.WC k) (IMW.WL k)).reverse.map fun z => -z := by
  decide +kernel

theorem relWords : ((rels ()).map fun r => r.map letterOf) =
    List.ofFn (n := 29) fun j => decW (RLW.WC j.val) (RLW.WL j.val) := by
  decide +kernel

variable (mvAll : ∀ s < 1023, mvS s = true) (ordAll : ∀ s < 1023, ordS s = true)
  (sortAll : ∀ s < 1023, sortS s = true) (invAll : ∀ s < 1023, invS s = true)
  (relAll : ∀ t < 154, relQ t = true) (surjAll : ∀ t < 154, surjQ t = true)

include mvAll ordAll sortAll in
theorem orb_tabs : natTab (orbitData ()).alpha = tabArr ONW.A 245520 ∧
    natTab (orbitData ()).beta = tabArr ONW.B 245520 := by
  have hla := list_eq ONW.LA ONW.CA (allN_spec listA2)
  have hlb := list_eq ONW.LB ONW.CB (allN_spec listB2)
  have hA : (colsA ()).size = 154 ∧ ONW.LA.length = 154 ∧
      ∀ j < 154, (colsA ())[j]! = wOfK (ONW.LA.getD j 0) := by
    unfold colsA rowsA
    exact cols_of ONSeedA.eq colsAK2 hla rfl
  have hB : (colsB ()).size = 154 ∧ ONW.LB.length = 154 ∧
      ∀ j < 154, (colsB ())[j]! = wOfK (ONW.LB.getD j 0) := by
    unfold colsB rowsB
    exact cols_of ONSeedB.eq colsBK2 hlb rfl
  have hr : rootW () = wOfK (key ONW.K 0) := by
    rw [← digitsK_sound rootK2, ← ONRootW.eq]
    rfl
  unfold orbitData
  exact bfsK_sound (SL := 240) (NS := 1023) (SO := ONW.SO) (SOI := ONW.SOI) (NX := ONW.NX)
    (K := ONW.K) hA hB (canon_of colsAK2 hla) (canon_of colsBK2 hlb) hr (by norm_num)
    (pt_of mvAll fun _ => rfl) (by norm_num) (Nat.eq_of_beq_eq_true nx0) (Nat.eq_of_beq_eq_true nx1)
    ordAll (pt_of sortAll fun _ => rfl)

theorem natTab_TR {t : Table} {f : Nat → Nat} (h : natTab t = Array.ofFn (n := 245520) fun i => f i.val)
    (hf : ∀ i < 245520, f i < 245520) : TR 245520 t f := by
  have hs : t.size = 245520 := by
    have := congrArg Array.size h
    simpa [natTab] using this
  refine ⟨hs, fun i hi => ⟨?_, hf i hi⟩⟩
  have := congrArg (fun a => a[i]!) h
  simp only [natTab] at this
  rw [getElem!_pos _ i (by simpa [hs] using hi), Array.getElem_map,
    getElem!_pos _ i (by simpa using hi), Array.getElem_ofFn] at this
  unfold ap
  rw [getElem!_pos _ i (by simpa [hs] using hi)]
  exact this

include invAll in
theorem inv_facts {i : Nat} (hi : i < 245520) : tab ONW.A i < 245520 ∧ tab ONW.B i < 245520 ∧
    tab ONW.U0 i < 245520 ∧ tab ONW.U1 i < 245520 ∧ tab ONW.U0 (tab ONW.A i) = i ∧
    tab ONW.U1 (tab ONW.B i) = i ∧ tab ONW.A (tab ONW.U0 i) = i ∧ tab ONW.B (tab ONW.U1 i) = i := by
  have h := pt_of invAll (fun _ => rfl) i hi
  obtain ⟨a1, a2, a3, a4, a5, a6, a7, a8⟩ := (by simpa only [bAnd_iff] using h :
    Nat.blt (tab ONW.A i) 245520 = true ∧ Nat.blt (tab ONW.B i) 245520 = true ∧
    Nat.blt (tab ONW.U0 i) 245520 = true ∧ Nat.blt (tab ONW.U1 i) 245520 = true ∧
    Nat.beq (tab ONW.U0 (tab ONW.A i)) i = true ∧ Nat.beq (tab ONW.U1 (tab ONW.B i)) i = true ∧
    Nat.beq (tab ONW.A (tab ONW.U0 i)) i = true ∧ Nat.beq (tab ONW.B (tab ONW.U1 i)) i = true)
  exact ⟨Nat.blt_eq ▸ a1, Nat.blt_eq ▸ a2, Nat.blt_eq ▸ a3, Nat.blt_eq ▸ a4,
    Nat.eq_of_beq_eq_true a5, Nat.eq_of_beq_eq_true a6, Nat.eq_of_beq_eq_true a7,
    Nat.eq_of_beq_eq_true a8⟩

theorem mem_decW {W L : Nat} {z : Int} (hz : z ∈ decW W L) :
    ∃ p < L, z = letterOfCode ((W >>> (4 * p)) % 16) := by
  induction L with
  | zero => simp [decW] at hz
  | succ L ih =>
    rw [decW, List.mem_cons] at hz
    rcases hz with h | h
    · exact ⟨L, by omega, h⟩
    · obtain ⟨p, hp, e⟩ := ih h
      exact ⟨p, by omega, e⟩

theorem code_bound {W L B : Nat} (h : allN L (fun p =>
    Nat.blt (Nat.land (Nat.shiftRight W (Nat.mul 4 p)) 15) B) = true) {z : Int} (hz : z ∈ decW W L) :
    ∃ c < B, z = letterOfCode c := by
  obtain ⟨p, hp, e⟩ := mem_decW hz
  refine ⟨(W >>> (4 * p)) % 16, ?_, e⟩
  have := allN_spec h p hp
  have h15 : Nat.land (Nat.shiftRight W (Nat.mul 4 p)) 15 = (W >>> (4 * p)) % 16 :=
    Nat.and_two_pow_sub_one_eq_mod _ 4
  rw [h15] at this
  exact Nat.blt_eq ▸ this

theorem seed_cases {z : Int} (hz : ∃ c < 4, z = letterOfCode c) : z = 1 ∨ z = -1 ∨ z = 2 ∨ z = -2 := by
  obtain ⟨c, hc, rfl⟩ := hz
  interval_cases c <;> simp [letterOfCode]

theorem img_cases {z : Int} (hz : ∃ c < 14, z = letterOfCode c) :
    ∃ i < 7, z = ((i + 1 : Nat) : Int) ∨ z = -((i + 1 : Nat) : Int) := by
  obtain ⟨c, hc, rfl⟩ := hz
  refine ⟨c / 2, by omega, ?_⟩
  unfold letterOfCode
  split <;> simp

@[expose] noncomputable def G4 : Array Table :=
  #[(orbitData ()).alpha, invT nPts (orbitData ()).alpha, (orbitData ()).beta, invT nPts (orbitData ()).beta]

include mvAll ordAll sortAll invAll in
theorem seed_TR {z : Int} (hz : z = 1 ∨ z = -1 ∨ z = 2 ∨ z = -2) :
    TR 245520 (seedLetter G4 z) (GZ ST SU z) := by
  have hb := fun i hi => inv_facts invAll (i := i) hi
  have hA : TR 245520 (orbitData ()).alpha (tab ONW.A) :=
    natTab_TR (orb_tabs mvAll ordAll sortAll).1 fun i hi => (hb i hi).1
  have hB : TR 245520 (orbitData ()).beta (tab ONW.B) :=
    natTab_TR (orb_tabs mvAll ordAll sortAll).2 fun i hi => (hb i hi).2.1
  rcases hz with rfl | rfl | rfl | rfl
  · have e : GZ ST SU 1 = tab ONW.A := by
      funext y
      rfl
    rw [e]
    simpa [seedLetter, G4] using hA
  · have e : GZ ST SU (-1) = tab ONW.U0 := by
      funext y
      rfl
    rw [e]
    have := invT_TR (by norm_num) hA (g := tab ONW.U0) fun i hi =>
      ⟨(hb i hi).2.2.1, (hb i hi).2.2.2.2.2.2.1, (hb i hi).2.2.2.2.1⟩
    simpa [seedLetter, G4] using this
  · have e : GZ ST SU 2 = tab ONW.B := by
      funext y
      rfl
    rw [e]
    simpa [seedLetter, G4] using hB
  · have e : GZ ST SU (-2) = tab ONW.U1 := by
      funext y
      rfl
    rw [e]
    have := invT_TR (by norm_num) hB (g := tab ONW.U1) fun i hi =>
      ⟨(hb i hi).2.2.2.1, (hb i hi).2.2.2.2.2.2.2, (hb i hi).2.2.2.2.2.1⟩
    simpa [seedLetter, G4] using this

include invAll in
theorem seed_inv {z : Int} (hz : z = 1 ∨ z = -1 ∨ z = 2 ∨ z = -2) :
    ∀ y < 245520, GZ ST SU z y < 245520 ∧ GZ ST SU (-z) (GZ ST SU z y) = y := by
  intro y hy
  have hb := inv_facts invAll hy
  rcases hz with rfl | rfl | rfl | rfl
  · exact ⟨hb.1, hb.2.2.2.2.1⟩
  · exact ⟨hb.2.2.1, hb.2.2.2.2.2.2.1⟩
  · exact ⟨hb.2.1, hb.2.2.2.2.2.1⟩
  · exact ⟨hb.2.2.2.1, hb.2.2.2.2.2.2.2⟩

theorem codes_img {k : Nat} (hk : k < 7) : allN (IMW.WL k) (fun p =>
    Nat.blt (Nat.land (Nat.shiftRight (IMW.WC k) (Nat.mul 4 p)) 15) 4) = true :=
  allN_spec codesI k hk

theorem img_words : imgWords () = Array.ofFn (n := 7) fun k => decW (IMW.WC k.val) (IMW.WL k.val) := by
  unfold imgWords
  rw [ONGI.eq]
  exact wordsK_sound imgOK

theorem surj_words : surjWords () = Array.ofFn (n := 2) fun k => decW (SRW.WC k.val) (SRW.WL k.val) := by
  unfold surjWords
  rw [ONGS.eq]
  exact wordsK_sound surjOK

@[expose] noncomputable def I7 : Array Table := (imgWords ()).map (wordT nPts (seedLetter G4))

include mvAll ordAll sortAll invAll in
theorem I7_TR {k : Nat} (hk : k < 7) : TR 245520 I7[k]! (IMG k) := by
  have e : I7[k]! = wordT 245520 (seedLetter G4) (decW (IMW.WC k) (IMW.WL k)) := by
    unfold I7
    rw [img_words, getElem!_pos _ k (by simpa using hk), Array.getElem_map, Array.getElem_ofFn]
  rw [e]
  have h := wordT_TR (by norm_num) (G := GZ ST SU) (gens := seedLetter G4)
    (decW (IMW.WC k) (IMW.WL k)) fun z hz =>
      seed_TR mvAll ordAll sortAll invAll (seed_cases (code_bound (codes_img hk) hz))
  have e2 : (fun x => (decW (IMW.WC k) (IMW.WL k)).foldr (GZ ST SU) x) = IMG k := by
    funext x
    rw [IMG, trace_eq]
  rw [e2] at h
  exact h

include invAll in
theorem IMG_inv {k : Nat} (hk : k < 7) : ∀ y < 245520,
    IMGI k y < 245520 ∧ IMG k (IMGI k y) = y ∧ IMGI k (IMG k y) = y := by
  intro y hy
  have hw : ∀ z ∈ decW (IMW.WC k) (IMW.WL k), z = 1 ∨ z = -1 ∨ z = 2 ∨ z = -2 :=
    fun z hz => seed_cases (code_bound (codes_img hk) hz)
  have hI : ∀ x, IMGI k x = ((decW (IMW.WC k) (IMW.WL k)).reverse.map fun z => -z).foldr (GZ ST SU) x := by
    intro x
    rw [IMGI, trace_eq, invWords k hk]
  have hG : ∀ x, IMG k x = (decW (IMW.WC k) (IMW.WL k)).foldr (GZ ST SU) x := by
    intro x
    rw [IMG, trace_eq]
  have f1 := foldr_inv (G := GZ ST SU) (n := 245520) (decW (IMW.WC k) (IMW.WL k))
    (fun z hz => seed_inv invAll (hw z hz))
  have hw' : ∀ z ∈ ((decW (IMW.WC k) (IMW.WL k)).reverse.map fun z => -z),
      ∀ y < 245520, GZ ST SU z y < 245520 ∧ GZ ST SU (-z) (GZ ST SU z y) = y := by
    intro z hz
    simp only [List.mem_map, List.mem_reverse] at hz
    obtain ⟨a, ha, rfl⟩ := hz
    apply seed_inv invAll
    rcases hw a ha with rfl | rfl | rfl | rfl <;> simp
  have f2 := foldr_inv (G := GZ ST SU) (n := 245520) _ hw'
  have hrr : (((decW (IMW.WC k) (IMW.WL k)).reverse.map fun z => -z).reverse.map fun z => -z) =
      decW (IMW.WC k) (IMW.WL k) := by
    simp [List.map_reverse, List.reverse_reverse]
  rw [hrr] at f2
  refine ⟨?_, ?_, ?_⟩
  · rw [hI]
    exact (f2 y hy).1
  · rw [hG, hI]
    exact (f2 y hy).2
  · rw [hG, hI]
    exact (f1 y hy).2

include mvAll ordAll sortAll invAll in
theorem Iv7_TR {k : Nat} (hk : k < 7) : TR 245520 (I7.map (invT nPts))[k]! (IMGI k) := by
  have e : (I7.map (invT nPts))[k]! = invT 245520 I7[k]! := by
    rw [getElem!_pos _ k (by simp [I7, img_words]; omega), Array.getElem_map,
      ← getElem!_pos I7 k (by simp [I7, img_words]; omega)]
  rw [e]
  exact invT_TR (by norm_num) (I7_TR mvAll ordAll sortAll invAll hk) fun y hy =>
    IMG_inv invAll hk y hy

include mvAll ordAll sortAll invAll in
theorem imgLetter_TR {z : Int} (hz : ∃ i < 7, z = ((i + 1 : Nat) : Int) ∨ z = -((i + 1 : Nat) : Int)) :
    TR 245520 (imgLetter I7 (I7.map (invT nPts)) z) (GZ IMG IMGI z) := by
  obtain ⟨i, hi, h | h⟩ := hz
  · subst h
    have e : GZ IMG IMGI ((i + 1 : Nat) : Int) = IMG i := by
      funext y
      simp [GZ]
    rw [e]
    have e2 : imgLetter I7 (I7.map (invT nPts)) ((i + 1 : Nat) : Int) = I7[i]! := by
      simp [imgLetter]
    rw [e2]
    exact I7_TR mvAll ordAll sortAll invAll hi
  · subst h
    have e : GZ IMG IMGI (-((i + 1 : Nat) : Int)) = IMGI i := by
      funext y
      simp [GZ]
    rw [e]
    have e2 : imgLetter I7 (I7.map (invT nPts)) (-((i + 1 : Nat) : Int)) = (I7.map (invT nPts))[i]! := by
      simp [imgLetter]
    rw [e2]
    exact Iv7_TR mvAll ordAll sortAll invAll hi

theorem cq_lt {t : Nat} (ht : t < 154) : cq t < 245520 :=
  Nat.blt_eq ▸ allN_spec cqOK t ht

theorem chainQ_size : chainQ.size = 154 := rfl

include mvAll ordAll sortAll invAll in
theorem word_tuple {W L : Nat} (hc : allN L (fun p =>
      Nat.blt (Nat.land (Nat.shiftRight W (Nat.mul 4 p)) 15) 14) = true) :
    apT (wordT nPts (imgLetter I7 (I7.map (invT nPts))) (decW W L)) chainQ =
      chainQ.map fun x => trace IMG IMGI W L x := by
  rw [apT_map]
  apply Array.ext (by simp)
  intro t h1 h2
  have ht : t < 154 := by simpa [chainQ_size] using h2
  have h := wordT_TR (by norm_num) (G := GZ IMG IMGI) (gens := imgLetter I7 (I7.map (invT nPts)))
    (decW W L) fun z hz => imgLetter_TR mvAll ordAll sortAll invAll (img_cases (code_bound hc hz))
  rw [Array.getElem_map, Array.getElem_map, (h.2 _ (by
    rw [← getElem!_pos chainQ t (by simpa using h2)]
    exact cq_lt ht)).1, trace_eq]

include mvAll ordAll sortAll invAll relAll surjAll in
theorem bridge_ok : bridgeCheck () = true := by
  have hb := fun i hi => inv_facts invAll (i := i) hi
  have hA : TR 245520 (orbitData ()).alpha (tab ONW.A) :=
    natTab_TR (orb_tabs mvAll ordAll sortAll).1 fun i hi => (hb i hi).1
  have hB : TR 245520 (orbitData ()).beta (tab ONW.B) :=
    natTab_TR (orb_tabs mvAll ordAll sortAll).2 fun i hi => (hb i hi).2.1
  have cS := codesS
  have cR := codesR
  have hN : RLW.N = 29 := Nat.eq_of_beq_eq_true relN
  unfold bridgeCheck seedChecks tableChecks inverseChecks imageChecks
  simp only [Bool.and_eq_true, beq_iff_eq]
  have hG : (#[(orbitData ()).alpha, invT nPts (orbitData ()).alpha, (orbitData ()).beta,
      invT nPts (orbitData ()).beta] : Array Table) = G4 := rfl
  have hI : (imgWords ()).map (wordT nPts (seedLetter G4)) = I7 := rfl
  rw [hG, hI]
  refine ⟨⟨?_, ?_⟩, ⟨⟨⟨⟨⟨⟨?_, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩⟩
  · exact invOK_of hA (invT_TR (by norm_num) hA (g := tab ONW.U0) fun i hi =>
      ⟨(hb i hi).2.2.1, (hb i hi).2.2.2.2.2.2.1, (hb i hi).2.2.2.2.1⟩) fun i hi => (hb i hi).2.2.2.2.1
  · exact invOK_of hB (invT_TR (by norm_num) hB (g := tab ONW.U1) fun i hi =>
      ⟨(hb i hi).2.2.2.1, (hb i hi).2.2.2.2.2.2.2, (hb i hi).2.2.2.2.2.1⟩) fun i hi => (hb i hi).2.2.2.2.2.1
  · rw [img_words]
    simp
  · rw [surj_words]
    simp
  · rw [surj_words, Array.all_eq_true]
    intro k hk
    simp only [Array.size_ofFn] at hk
    rw [Array.getElem_ofFn, List.all_eq_true]
    intro z hz
    obtain ⟨c, hc, rfl⟩ := code_bound (allN_spec cS k hk) hz
    unfold letterOfCode
    split <;> simp <;> omega
  · rw [List.all_eq_true]
    intro k hk
    have hk7 : k < 7 := List.mem_range.1 hk
    exact invOK_of (I7_TR mvAll ordAll sortAll invAll hk7) (Iv7_TR mvAll ordAll sortAll invAll hk7)
      fun y hy => (IMG_inv invAll hk7 y hy).2.2
  · rw [List.all_eq_true]
    intro r hr
    have hm : r.map letterOf ∈ (rels ()).map fun r => r.map letterOf := List.mem_map_of_mem hr
    rw [relWords, List.mem_ofFn] at hm
    obtain ⟨⟨j, hj⟩, e⟩ := hm
    rw [← e, word_tuple mvAll ordAll sortAll invAll (allN_spec cR j hj), tupleEq_iff]
    refine ⟨by simp, fun t ht => ?_⟩
    have ht' : t < 154 := by simpa [chainQ_size] using ht
    have h := relAll t ht'
    unfold relQ at h
    rw [strictB_eq', hN] at h
    have := Nat.eq_of_beq_eq_true (allN_spec h j hj)
    unfold cq at this
    rw [getElem!_pos _ t (by simpa using ht), Array.getElem_map]
    rw [getElem!_pos chainQ t ht] at this ⊢
    exact this
  · have e0 : (surjWords ())[0]! = decW (SRW.WC 0) (SRW.WL 0) := by
      rw [surj_words, getElem!_pos _ 0 (by simp), Array.getElem_ofFn]
    rw [e0, word_tuple mvAll ordAll sortAll invAll (allN_spec cS 0 (by norm_num)), apT_map, tupleEq_iff]
    refine ⟨by simp, fun t ht => ?_⟩
    have ht' : t < 154 := by simpa [chainQ_size] using ht
    have h := surjAll t ht'
    unfold surjQ at h
    rw [strictB_eq'] at h
    have := Nat.eq_of_beq_eq_true ((bAnd_iff _ _).1 h).1
    unfold cq at this
    have hq : chainQ[t]! < 245520 := cq_lt ht'
    rw [getElem!_pos _ t (by simpa using ht), getElem!_pos _ t (by simpa using ht), Array.getElem_map,
      Array.getElem_map, ← getElem!_pos chainQ t (by simpa using ht), (hA.2 _ hq).1]
    exact this
  · have e1 : (surjWords ())[1]! = decW (SRW.WC 1) (SRW.WL 1) := by
      rw [surj_words, getElem!_pos _ 1 (by simp), Array.getElem_ofFn]
    rw [e1, word_tuple mvAll ordAll sortAll invAll (allN_spec cS 1 (by norm_num)), apT_map, tupleEq_iff]
    refine ⟨by simp, fun t ht => ?_⟩
    have ht' : t < 154 := by simpa [chainQ_size] using ht
    have h := surjAll t ht'
    unfold surjQ at h
    rw [strictB_eq'] at h
    have := Nat.eq_of_beq_eq_true ((bAnd_iff _ _).1 h).2
    unfold cq at this
    have hq : chainQ[t]! < 245520 := cq_lt ht'
    rw [getElem!_pos _ t (by simpa using ht), getElem!_pos _ t (by simpa using ht), Array.getElem_map,
      Array.getElem_map, ← getElem!_pos chainQ t (by simpa using ht), (hB.2 _ hq).1]
    exact this

end CertificateChecks.KernelSpor.ON2

end
