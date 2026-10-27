module

public import Certificates.Kernel.SmithD6Wt.Facts
public import Certificates.Kernel.SmithD6Wt.Gram
public import CFSG.GF2Type.SmithTypeE.DMod.WtAnn

set_option maxRecDepth 100000

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CertificateChecks.SmithD6Wt

open CFSG.SmithD6 CFSG.KC.KeyTree CFSG.KD.SmithD6 CFSG.GF2Type.SmithTypeE.DMod

theorem getD_append_left' {α : Type} {l l' : List α} {i : ℕ} (d : α) (h : i < l.length) :
    (l ++ l').getD i d = l.getD i d := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_left h]

theorem getD_append_right' {α : Type} {l l' : List α} {i : ℕ} (d : α) (h : l.length ≤ i) :
    (l ++ l').getD i d = l'.getD (i - l.length) d := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_right h]

theorem forall_flatten {α β : Type} (R : α → β → Prop) (da : α) (db : β) :
    ∀ (A : List (List α)) (B : List (List β)), A.length = B.length →
    (∀ c < A.length, (A.getD c []).length = (B.getD c []).length ∧
      ∀ i < (A.getD c []).length, R ((A.getD c []).getD i da) ((B.getD c []).getD i db)) →
    A.flatten.length = B.flatten.length ∧
      ∀ i < A.flatten.length, R (A.flatten.getD i da) (B.flatten.getD i db)
  | [], [], _, _ => by simp
  | [], _ :: _, h, _ => by simp at h
  | _ :: _, [], h, _ => by simp at h
  | a :: A, b :: B, hl, h => by
    obtain ⟨h0, h0'⟩ := h 0 (by simp)
    simp only [List.getD_cons_zero] at h0 h0'
    obtain ⟨ih1, ih2⟩ := forall_flatten R da db A B (by simpa using hl) fun c hc => by
      simpa [List.getD_cons_succ] using h (c + 1) (by simpa using hc)
    refine ⟨by simp [h0, ih1], fun i hi => ?_⟩
    simp only [List.flatten_cons, List.length_append] at hi ⊢
    by_cases hia : i < a.length
    · rw [getD_append_left' _ hia, getD_append_left' _ (by omega)]
      exact h0' i hia
    · rw [getD_append_right' _ (by omega), getD_append_right' _ (by omega), ← h0]
      exact ih2 (i - a.length) (by omega)

theorem wtC_length : J.wtC.length = 37 := by rw [← lenC_eq, SmithD6Trees.wtC_lenC]

theorem wt64C_length : J.wt64C.length = 37 := by rw [← lenC_eq, wt64C_lenC]

theorem wt64C_chunk {c : ℕ} (hc : c < 37) : J.wt64C.getD c [] = (J.wtC.getD c []).map exC := by
  have h := exChunks_ok c hc
  rw [d6ExOK, nthC_eq, nthC_eq] at h
  exact (exPinGo_sound _ _ h).1

theorem wtC_flatten_length : J.wtC.flatten.length = 75735 := by
  have h := wt64_facts.2.1
  rwa [wt64_eq_map.1, List.length_map] at h

theorem wt64_getD (i : ℕ) : J.wt64C.flatten.getD i 0 = exC (J.wtC.flatten.getD i 0) := by
  rw [wt64_eq_map.1, List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_map]
  cases J.wtC.flatten[i]? with
  | none => rfl
  | some x => rfl

theorem planes_flat : J.pbC.flatten.length = 75735 ∧ ∀ i < 75735, ∃ P : Array ℕ,
    planeL (exC (J.wtC.flatten.getD i 0)) (J.pbC.flatten.getD i #[]).toList P.toList = true := by
  obtain ⟨hl, hR⟩ := forall_flatten
    (fun s (B : Array ℕ) => ∃ P : Array ℕ, planeL s B.toList P.toList = true) 0 #[]
    J.wt64C J.pbC (by rw [wt64C_length, pbC_ppC_length.1]) fun c hc => by
      obtain ⟨h1, -, h3⟩ := planes c (by rw [wt64C_length] at hc; exact hc)
      exact ⟨h1.symm, fun i hi => ⟨_, h3 i hi⟩⟩
  have hlen : J.wt64C.flatten.length = 75735 := wt64_facts.2.1
  refine ⟨by omega, fun i hi => ?_⟩
  obtain ⟨P, hP⟩ := hR i (by omega)
  rw [wt64_getD] at hP
  exact ⟨P, hP⟩

theorem ann : ∀ i < 75735,
    planeSpan (J.pbC.flatten.getD i #[]) = annSub (exL (decode32 (J.wtC.flatten.getD i 0))) := by
  intro i hi
  obtain ⟨P, hP⟩ := planes_flat.2 i hi
  rw [planeSpan_eq_annSub_of_planeL (exC_lt_two_pow _) hP, decode64_exC]

theorem closure32 : ∀ s ∈ J.wtC.flatten, ∀ g < 13, ∃ t ∈ J.wtC.flatten,
    tlift (dec12 (gensV.getD g (0, 0)).1) (dec12 (gensV.getD g (0, 0)).2) (exL (decode32 s)) =
      exL (decode32 t) := by
  intro s hs g hg
  have hs64 : exC s ∈ J.wt64C.flatten := by
    rw [wt64_eq_map.1]
    exact List.mem_map_of_mem hs
  have hm := closure (exC s) hs64 g hg
  have hpos : 0 < wt64Tree.find (liftT (JT.gensT.getD g []) (exC s)) := Nat.le_of_ble_eq_true hm
  obtain ⟨v, hvdef⟩ : ∃ v, v = wt64Tree.find (liftT (JT.gensT.getD g []) (exC s)) - 1 := ⟨_, rfl⟩
  obtain ⟨hv, hx⟩ := wt64_facts.2.2.2 (liftT (JT.gensT.getD g []) (exC s)) v (by omega)
  have hv32 : v < J.wtC.flatten.length := by
    rw [wtC_flatten_length]
    rw [wt64_facts.2.1] at hv
    exact hv
  have e : liftT (JT.gensT.getD g []) (exC s) = exC (J.wtC.flatten.getD v 0) := by
    rw [← wt64_getD, List.getD_eq_getElem _ _ hv, hx]
  refine ⟨J.wtC.flatten.getD v 0, ?_, ?_⟩
  · rw [List.getD_eq_getElem _ _ hv32]
    exact List.getElem_mem hv32
  · rw [← decode64_exC, ← decode64_exC, ← e, decode64_liftT (gensT_ok g hg) (exC_lt_two_pow s)]

theorem first : J.wtC.flatten.getD 0 0 = 1 ∧ J.pbC.flatten.getD 0 #[] = fBasis := by
  obtain ⟨h1, h2⟩ := first_facts
  have hF : fBasis = #[64, 128, 256, 512, 1024, 2048] := rfl
  rw [hF]
  constructor
  · rcases hc : J.wtC with _ | ⟨c0, cs⟩
    · rw [hc] at h1
      simp at h1
    · rw [hc] at h1
      rw [List.flatten_cons, getD_append_left']
      · simpa using h1
      · rcases c0 with _ | ⟨x, c0⟩
        · simp at h1
        · simp
  · rcases hc : J.pbC with _ | ⟨c0, cs⟩
    · rw [hc] at h2
      simp at h2
    · rw [hc] at h2
      rw [List.flatten_cons, getD_append_left']
      · simpa using h2
      · rcases c0 with _ | ⟨x, c0⟩
        · simp at h2
        · simp

theorem gram_testBit : ∀ j < 75735, (J.wtC.flatten.getD j 0).testBit 31 = true ↔
    Disjoint (planeSpan fBasis) (planeSpan (J.pbC.flatten.getD j #[])) := by
  obtain ⟨-, hR⟩ := forall_flatten
    (fun s (B : Array ℕ) => s.testBit 31 = true ∨ FComb B.toList) 0 #[]
    J.wtC J.pbC (by rw [wtC_length, pbC_ppC_length.1]) fun c hc => by
      rw [wtC_length] at hc
      have hlen : (J.wtC.getD c []).length = (J.pbC.getD c []).length := by
        rw [(planes c hc).1, wt64C_chunk hc, List.length_map]
      refine ⟨hlen, fun i hi => ?_⟩
      have h := gramChunks_ok c hc
      rw [d6GramOK, nthC_eq, nthA_eq, nthC_eq] at h
      exact gramGo_sound _ _ _ h i hi (by omega)
  intro j hj
  rw [ann j hj]
  constructor
  · exact disjoint_annSub_of_testBit
  · intro hd
    rcases hR j (by rw [wtC_flatten_length]; exact hj) with h | h
    · exact h
    · exfalso
      obtain ⟨P, hP⟩ := planes_flat.2 j hj
      have hsz : (J.pbC.flatten.getD j #[]).size = 6 := by
        rw [← Array.length_toList]
        exact (planeL_sound hP).2.1
      apply not_disjoint_of_fComb hsz h
      rw [ann j hj]
      exact hd

theorem gram : ∀ j < 75735,
    fModel (decode32 (J.wtC.flatten.getD 0 0)) (decode32 (J.wtC.flatten.getD j 0)) = 1 ↔
      Disjoint (planeSpan (J.pbC.flatten.getD 0 #[])) (planeSpan (J.pbC.flatten.getD j #[])) := by
  intro j hj
  rw [first.1, first.2, fModel_decode, fB_one_left, ← gram_testBit j hj]
  cases (J.wtC.flatten.getD j 0).testBit 31 <;> simp [bit]

end CertificateChecks.SmithD6Wt

end
