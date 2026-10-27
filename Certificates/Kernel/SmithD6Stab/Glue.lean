module

public import Certificates.Kernel.SmithD6Stab.ChecksN
public import Certificates.Kernel.SmithD6Trees.Facts
public import CFSG.Certificates.Kernel.SmithD6StabSound
public import CFSG.Certificates.Kernel.SmithD6StabNSound
public import Certificates.Data.SmithD6Facts
import all Certificates.Data.SmithD6Stab
import all Certificates.Data.SmithD6Facts

public section

namespace CertificateChecks.SmithD6Stab

open CFSG.SmithD6 CFSG.KD.SmithD6 CFSG.KD.SmithD6Stab CFSG.KC.KeyTree
  CertificateChecks.SmithD6Trees

theorem clsChunks_ok : ∀ c < 179, clsChunkOK J.lineKeysC S.clsCntC c = true := fun c hc => by
  rw [← clsChunkOKN_eq]
  exact clsChunksN_ok c hc

theorem map_range_getElem! (l : List Nat) : (List.range l.length).map (fun i => l[i]!) = l := by
  apply List.ext_getElem
  · simp
  · intro i h1 h2
    simp [List.getElem_map, List.getElem_range, getElem!_pos l i h2, List.getElem?_eq_getElem h2]

theorem key_zero : J.lineKeysC.flatten[0]! = 4098 := by
  obtain ⟨h0, h⟩ := List.getElem?_eq_some_iff.1 lineKeysC_head
  rw [getElem!_pos _ 0 h0, h]

theorem key_inj {a b : Nat} (ha : a < 365211) (hb : b < 365211)
    (h : J.lineKeysC.flatten[a]! = J.lineKeysC.flatten[b]!) : a = b := by
  obtain ⟨hp, hn, -, -⟩ := lineKeys_facts
  have ha' : a < J.lineKeysC.flatten.length := hn ▸ ha
  have hb' : b < J.lineKeysC.flatten.length := hn ▸ hb
  rw [getElem!_pos _ a ha', getElem!_pos _ b hb'] at h
  rcases Nat.lt_trichotomy a b with hab | hab | hab
  · have := List.pairwise_iff_getElem.1 hp a b ha' hb' hab
    omega
  · exact hab
  · have := List.pairwise_iff_getElem.1 hp b a hb' ha' hab
    omega

theorem key_of_find {x v : Nat} (h : KT.find x lineTree = v + 1) :
    v < 365211 ∧ J.lineKeysC.flatten[v]! = x := by
  obtain ⟨-, hn, -, hs⟩ := lineKeys_facts
  obtain ⟨hv, hx⟩ := hs x v h
  exact ⟨hn ▸ hv, by rw [getElem!_pos _ v hv, hx]⟩

theorem find?_range {p : Nat → Bool} {n r : Nat} (hr : r < n) (hp : p r = true)
    (hlt : ∀ a < r, p a = false) : (List.range n).find? p = some r := by
  rw [List.find?_eq_some_iff_append]
  refine ⟨hp, List.range r, List.range' (r + 1) (n - r - 1), ?_, ?_⟩
  · rw [List.range_eq_range', List.range_eq_range']
    have h1 := List.range'_append (s := 0) (m := r) (n := n - r - 1 + 1) (step := 1)
    rw [List.range'_succ] at h1
    simp only [Nat.zero_add, Nat.one_mul] at h1
    rw [h1]
    congr 1
    omega
  · intro a ha
    simp [hlt a (List.mem_range.1 ha)]

theorem all_first : ∀ k ∈ J.lineKeysC.flatten, repKeys.getD (clsK k) 0 ≤ k := by
  have hl : J.lineKeysC.length = 179 := by rw [← lenC_eq, lineKeysC_lenC]
  intro k hk
  obtain ⟨ch, hch, hk⟩ := List.mem_flatten.1 hk
  obtain ⟨c, hc, rfl⟩ := List.mem_iff_getElem.1 hch
  have h := (band_true (clsChunks_ok c (by rw [hl] at hc; exact hc))).1
  rw [nthC_eq, getD_eq hc] at h
  exact firstGo_sound _ _ h k hk

theorem d6s_forIn_flag (q : Nat → Bool) (b : Bool) (L : List Nat) :
    forIn L ((none : Option Bool), ()) (fun i _ => if q i = true then
        (pure (ForInStep.done ((some b : Option Bool), ())) : Id (ForInStep (Option Bool × Unit)))
      else pure (ForInStep.yield ((none : Option Bool), ()))) =
    (pure (if L.any q = true then ((some b : Option Bool), ()) else ((none : Option Bool), ())) :
      Id (Option Bool × Unit)) := by
  induction L with
  | nil => simp
  | cons a L ih =>
    simp only [List.forIn_cons, List.any_cons]
    by_cases ha : q a = true
    · simp [ha]
    · simp only [ha, if_false, Bool.false_or] at ih ⊢
      simp [ha, ih]

theorem d6s_mf7All_iff (n : Nat) (p : Nat → Bool) :
    mf7All n p = true ↔ ∀ i < n, p i = true := by
  have : mf7All n p = !((List.range' 0 n).any fun i => !p i) := by
    unfold mf7All
    simp only [Id.run, Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size,
      Nat.sub_zero, Nat.add_sub_cancel, Nat.div_one]
    simp only [d6s_forIn_flag, pure_bind]
    by_cases hA : (List.range' 0 n).any (fun i => !p i) = true
    · simp [hA] <;> rfl
    · simp [hA] <;> rfl
  rw [this]
  simp [List.any_eq_true, List.mem_range'_1]

section Model

variable (hK : lineKeys.toList = J.lineKeysC.flatten)
include hK

theorem linePair_eq {a : Nat} : linePair a = pairK J.lineKeysC.flatten[a]! := by
  have : lineKeys[a]! = J.lineKeysC.flatten[a]! := by rw [← hK, Array.getElem!_toList]
  simp only [linePair, pairK, this]

theorem stabCls_eq {a : Nat} (ha : a < 365211) : stabCls a = clsK J.lineKeysC.flatten[a]! := by
  have h1 : stabCls a = clsP (a == 0) (linePair 0) (linePair a) := rfl
  have hz : (a == 0) = (J.lineKeysC.flatten[a]! == 4098) := by
    by_cases h0 : a = 0
    · subst h0
      rw [key_zero]
      rfl
    · have : J.lineKeysC.flatten[a]! ≠ 4098 := by
        intro h
        rw [← key_zero] at h
        exact h0 (key_inj ha (by decide) h)
      rw [beq_false_of_ne h0, beq_false_of_ne this]
  rw [h1, linePair_eq hK (a := a), linePair_eq hK (a := 0), key_zero, hz]
  rfl

theorem count_eq (c : Nat) : ((List.range 365211).filter fun a => stabCls a == c).length =
    J.lineKeysC.flatten.countP (fun k => clsK k == c) := by
  obtain ⟨-, hn, -, -⟩ := lineKeys_facts
  rw [← List.countP_eq_length_filter]
  conv => rhs; rw [← map_range_getElem! J.lineKeysC.flatten, hn]
  rw [List.countP_map]
  apply List.countP_congr
  intro a ha
  rw [stabCls_eq hK (List.mem_range.1 ha)]
  rfl

end Model

theorem chunk_sums :
    J.lineKeysC.map (fun ch => (ch.map fun k => 2 ^ (19 * clsK k)).sum) = S.clsCntC := by
  have hl : J.lineKeysC.length = 179 := by rw [← lenC_eq, lineKeysC_lenC]
  apply List.ext_getElem
  · rw [List.length_map, hl, clsCntC_length]
  · intro c h1 h2
    rw [List.length_map, hl] at h1
    have h := Nat.eq_of_beq_eq_true (band_true (clsChunks_ok c h1)).2
    rw [nthC_eq, cntGo_eq, Nat.zero_add, getD_eq (by rw [hl]; exact h1), getD_eq h2] at h
    rw [List.getElem_map, h]

theorem sum_map_flatten (f : Nat → Nat) : ∀ L : List (List Nat),
    (L.flatten.map f).sum = (L.map fun ch => (ch.map f).sum).sum
  | [] => rfl
  | ch :: L => by
    rw [List.flatten_cons, List.map_append, List.sum_append, sum_map_flatten f L, List.map_cons,
      List.sum_cons]

theorem lanes_eq {n0 n1 n2 n3 n4 n5 : Nat} (h0 : n0 ≤ 365211) (h1 : n1 ≤ 365211)
    (h2 : n2 ≤ 365211) (h3 : n3 ≤ 365211) (h4 : n4 ≤ 365211)
    (h : 1 + 810 * 2 ^ 19 + 768 * 2 ^ 38 + 25200 * 2 ^ 57 + 207360 * 2 ^ 76 + 131072 * 2 ^ 95 =
      n0 + n1 * 2 ^ 19 + n2 * 2 ^ 38 + n3 * 2 ^ 57 + n4 * 2 ^ 76 + n5 * 2 ^ 95) :
    n0 = 1 ∧ n1 = 810 ∧ n2 = 768 ∧ n3 = 25200 ∧ n4 = 207360 ∧ n5 = 131072 := by
  simp only [Nat.reducePow, Nat.reduceMul, Nat.reduceAdd] at h
  omega

theorem key_counts :
    J.lineKeysC.flatten.countP (fun k => clsK k == 0) = 1 ∧
    J.lineKeysC.flatten.countP (fun k => clsK k == 1) = 810 ∧
    J.lineKeysC.flatten.countP (fun k => clsK k == 2) = 768 ∧
    J.lineKeysC.flatten.countP (fun k => clsK k == 3) = 25200 ∧
    J.lineKeysC.flatten.countP (fun k => clsK k == 4) = 207360 ∧
    J.lineKeysC.flatten.countP (fun k => clsK k == 5) = 131072 := by
  obtain ⟨-, hn, -, -⟩ := lineKeys_facts
  have hs := sum_lanes J.lineKeysC.flatten
  rw [sum_map_flatten, chunk_sums, clsCntC_sum] at hs
  have hb : ∀ c, J.lineKeysC.flatten.countP (fun k => clsK k == c) ≤ 365211 := fun c =>
    hn ▸ List.countP_le_length
  exact lanes_eq (hb 0) (hb 1) (hb 2) (hb 3) (hb 4) hs

section Model

variable (hK : lineKeys.toList = J.lineKeysC.flatten)
include hK

theorem chkStabCard_true : chkStabCard = true := by
  obtain ⟨h0, h1, h2, h3, h4, h5⟩ := key_counts
  simp only [chkStabCard, List.all_eq_true, List.mem_range, beq_iff_eq]
  intro c hc
  rw [count_eq hK]
  obtain rfl | rfl | rfl | rfl | rfl | rfl : c = 0 ∨ c = 1 ∨ c = 2 ∨ c = 3 ∨ c = 4 ∨ c = 5 := by
    omega
  · rw [h0]; rfl
  · rw [h1]; rfl
  · rw [h2]; rfl
  · rw [h3]; rfl
  · rw [h4]; rfl
  · rw [h5]; rfl

theorem rep_facts {c : Nat} (hc : c < 6) :
    repPos.getD c 0 < 365211 ∧ J.lineKeysC.flatten[repPos.getD c 0]! = repKeys.getD c 0 ∧
    stabCls (repPos.getD c 0) = c ∧
    ordOKP (pairK 4098) (pairK (repKeys.getD c 0)) (ordL.getD c 0) = true := by
  have h := reps_ok c hc
  simp only [repOK, Bool.and_eq_true, beq_iff_eq] at h
  obtain ⟨⟨hcl, hf⟩, hord⟩ := h
  obtain ⟨hlt, hkey⟩ := key_of_find hf
  exact ⟨hlt, hkey, by rw [stabCls_eq hK hlt, hkey, hcl], hord⟩

theorem stabRep_eq {c : Nat} (hc : c < 6) : stabRep c = repPos.getD c 0 := by
  obtain ⟨hp, hn, -, -⟩ := lineKeys_facts
  obtain ⟨hlt, hkey, hcls, -⟩ := rep_facts hK hc
  have hfirst : ∀ a < repPos.getD c 0, (stabCls a == c) = false := by
    intro a ha
    have ha' : a < 365211 := Nat.lt_trans ha hlt
    have hmem : J.lineKeysC.flatten[a]! ∈ J.lineKeysC.flatten := by
      rw [getElem!_pos _ a (hn ▸ ha')]
      exact List.getElem_mem _
    have hle := all_first _ hmem
    have hlt2 : J.lineKeysC.flatten[a]! < J.lineKeysC.flatten[repPos.getD c 0]! := by
      rw [getElem!_pos _ a (hn ▸ ha'), getElem!_pos _ _ (hn ▸ hlt)]
      exact List.pairwise_iff_getElem.1 hp _ _ _ _ ha
    rw [stabCls_eq hK ha']
    cases h : clsK J.lineKeysC.flatten[a]! == c
    · rfl
    · rw [beq_iff_eq] at h
      rw [h, ← hkey] at hle
      omega
  have hf := find?_range (p := fun a => stabCls a == c) hlt
    (by simp only [hcls, beq_self_eq_true]) hfirst
  simp only [stabRep, stabReps]
  rw [getElem!_pos]
  all_goals simp [hc, hf]

theorem chkStabOrd_true : chkStabOrd = true := by
  have hpow : ∀ a b n x, prodPow a b n x = prodPowP (linePair a) (linePair b) n x := by
    intro a b n
    induction n with
    | zero => intro x; rfl
    | succ n ih => intro x; exact ih _
  have hstep : ∀ a b x, prodStep a b x = prodStepP (linePair a) (linePair b) x := fun _ _ _ => rfl
  have h0 : linePair 0 = pairK 4098 := by rw [linePair_eq hK, key_zero]
  simp only [chkStabOrd, Bool.and_eq_true, List.all_eq_true, List.mem_range, beq_iff_eq]
  refine ⟨⟨⟨rfl, ?_⟩, ?_⟩, ?_⟩
  · intro c hc
    obtain ⟨-, hkey, -, hord⟩ := rep_facts hK hc
    have hr : linePair (stabRep c) = pairK (repKeys.getD c 0) := by
      rw [stabRep_eq hK hc, linePair_eq hK, hkey]
    have ho : stabOrd[c]! = ordL.getD c 0 := by
      obtain rfl | rfl | rfl | rfl | rfl | rfl : c = 0 ∨ c = 1 ∨ c = 2 ∨ c = 3 ∨ c = 4 ∨ c = 5 := by
        omega
      all_goals rfl
    simp only [hpow, hstep, hr, h0, ho]
    simpa only [ordOKP, Bool.and_eq_true, List.all_eq_true, List.mem_range, beq_iff_eq] using hord
  · have h5 := (rep_facts hK (c := 5) (by decide)).2.1
    change J.lineKeysC.flatten[31899]! = 262272 at h5
    rw [linePair_eq hK, h5]
    rfl
  · exact (rep_facts hK (c := 5) (by decide)).2.2.1

theorem mf7ChkRepCls_true : mf7ChkRepCls () = true := by
  rw [mf7ChkRepCls, d6s_mf7All_iff]
  intro c hc
  obtain ⟨hlt, -, hcls, -⟩ := rep_facts hK hc
  have hr : mf7Reps[c]! = repPos.getD c 0 := by
    obtain rfl | rfl | rfl | rfl | rfl | rfl : c = 0 ∨ c = 1 ∨ c = 2 ∨ c = 3 ∨ c = 4 ∨ c = 5 := by
      omega
    all_goals rfl
  rw [hr, hcls]
  simp only [beq_self_eq_true, Bool.and_true, decide_eq_true_eq]
  exact hlt

end Model

end CertificateChecks.SmithD6Stab

end
