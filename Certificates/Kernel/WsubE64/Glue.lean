module

public import Certificates.Kernel.WsubE64.Checks
public import CFSG.Certificates.Kernel.WrPackSound
public import CFSG.Certificates.Kernel.AE117AdjSound

public section

namespace CFSG.KD.WsubE64

open CFSG.KC.WrTwin CFSG.KC.WrPack CFSG.ClassicalInvolution.Q3.AE CFSG.ClassicalInvolution.Q3.AE.Wr
  Certificates.AE117 Certificates.Kernel.AE117Adj Certificates.WsubMembersE64

theorem h6 : 6 ≤ 8 := by norm_num

theorem pm6 (a b : Wr 6) : pm 6 (enc a) (enc b) = enc (a * b) := pm_enc h6 a b

theorem mem_map_enc {x : Wr 6} {L : List (Wr 6)} : enc x ∈ L.map enc ↔ x ∈ L := by
  constructor
  · intro h
    obtain ⟨y, hy, he⟩ := List.mem_map.1 h
    exact enc_inj h6 he ▸ hy
  · exact List.mem_map_of_mem

theorem any_beq (y : Nat) (B : List Nat) : B.any (Nat.beq y) = decide (y ∈ B) := by
  rw [Bool.eq_iff_iff]
  simp [List.any_eq_true, Nat.beq_eq]

theorem memP_eq (y : Nat) (B : List Nat) : memP y B = decide (y ∈ B) := any_beq y B

theorem fst_encI (L : List (Wr 6)) : (encI L).map (·.1) = L.map enc := by
  simp [encI]

theorem conjP_eq (g h : Wr 6) (K K' : List (Wr 6)) :
    conjP (enc g) (enc h) (encI K) (encI K') = K.all fun x => decide (g * x * h ∈ K') := by
  unfold conjP
  rw [fst_encI, encI, List.all_map]
  simp only [Function.comp_def, any_beq, pm6, mem_map_enc]

theorem subP_eq (K K' : List (Wr 6)) :
    subP (encI K) (encI K') = K.all fun x => decide (x ∈ K') := by
  unfold subP
  rw [fst_encI, encI, List.all_map]
  simp only [Function.comp_def, any_beq, mem_map_enc]

theorem normP_eq (A K : List (Wr 6)) : normP (A.map enc) (encI K) =
    K.all fun x => A.all fun a => decide (x * a * x⁻¹ ∈ A) && decide (x⁻¹ * a * x ∈ A) := by
  simp only [normP, encI, Function.comp_def, List.all_map, memP_eq, pm6, mem_map_enc]

theorem subL_eq (g h : Wr 6) (K K' : List (Wr 6)) :
    subL ((encI K).map fun y => pm 6 (pm 6 (enc g) y.1) (enc h)) (encI K') =
      K.all fun x => decide (g * x * h ∈ K') := by
  unfold subL
  rw [fst_encI, encI, List.map_map, List.all_map]
  simp only [Function.comp_def, any_beq, pm6, mem_map_enc]

theorem quads6_ok : ∀ q ∈ quads 6, [q.1, q.2.1, q.2.2.1, q.2.2.2].Nodup ∧
    [q.1, q.2.1, q.2.2.1, q.2.2.2].Pairwise (· ≤ ·) := by
  decide +kernel

theorem lab_props {l : Lab} (hl : l ∈ labels) :
    (qset l.1).card = 4 ∧ memAtL (qset l.1) l.2 = memQ l.1 l.2 := by
  unfold labels at hl
  obtain ⟨q, hq, hl⟩ := List.mem_flatMap.1 hl
  have h1 : l.1 = q := by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hl
    rcases hl with rfl | rfl <;> rfl
  rw [h1]
  obtain ⟨hn, hs⟩ := quads6_ok q hq
  refine ⟨?_, memAtL_eq ((List.toFinset_sort (· ≤ ·) hn).2 hs) l.2⟩
  rw [qset, List.toFinset_card_of_nodup hn]
  rfl

theorem lab_of {L : Finset (Fin 6) × Bool} (h : L.1.card = 4) :
    ∃ l ∈ labels, L = (qset l.1, l.2) ∧ memAtL L.1 L.2 = memQ l.1 l.2 := by
  obtain ⟨q, hq, hs, he⟩ :=
    exists_quad (n := 6) (Finset.mem_powersetCard.2 ⟨Finset.subset_univ _, h⟩)
  refine ⟨(q, L.2), ?_, Prod.ext he rfl, memAtL_eq hs L.2⟩
  unfold labels
  refine List.mem_flatMap.2 ⟨q, hq, ?_⟩
  cases L.2 <;> simp

theorem mem_LM {l : Lab} (hl : l ∈ labels) : (l, encI (memQ l.1 l.2)) ∈ LM () :=
  List.mem_map_of_mem (f := fun l : Lab => (l, encI (memQ l.1 l.2))) hl

theorem of_mem_LM {X : Lab × List (Nat × Nat)} (hX : X ∈ LM ()) :
    X.1 ∈ labels ∧ X.2 = encI (memQ X.1.1 X.1.2) := by
  obtain ⟨l, hl, rfl⟩ := List.mem_map.1 hX
  exact ⟨hl, rfl⟩

theorem wsum_blk (k : ℕ) : wsum (blk k) = 0 := by
  have key : ∀ a b c : ZMod 2, a + a + b + c + c + b = 0 := by decide
  rw [wsum, Fin.sum_univ_six]
  exact key _ _ _

theorem nodupP_sound : ∀ {B : List Nat}, nodupP B = true → B.Nodup
  | [], _ => List.nodup_nil
  | x :: B, h => by
    simp only [nodupP, Bool.and_eq_true, Bool.not_eq_true', memP_eq, decide_eq_false_iff_not] at h
    exact List.nodup_cons.2 ⟨h.1, nodupP_sound h.2⟩

theorem e64B_k (h : e64P (enc (1 : Wr 6)) ((a0List ()).map enc) = true) :
    e64B (a0List ()) = true := by
  simp only [e64P, Bool.and_eq_true, List.all_map, Function.comp_def, memP_eq, pm6, mem_map_enc,
    beq_enc h6] at h
  obtain ⟨⟨hn, hc⟩, he⟩ := h
  have hA : (a0List ()).length = 64 := by simp [a0List]
  simp only [e64B, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at hc he ⊢
  refine ⟨⟨⟨hA, (nodupP_sound hn).of_map enc⟩, hc⟩, fun a ha => ⟨he a ha, ?_⟩⟩
  rw [a0List] at ha
  obtain ⟨k, -, rfl⟩ := List.mem_map.1 ha
  exact wsum_blk k

theorem permB_k {s : Wr 6} (h : permP (LM ()) (enc s) (enc s⁻¹) = true) :
    permB s = true := by
  unfold permB
  refine decide_eq_true ?_
  intro L hL
  obtain ⟨l, hl, rfl, hm⟩ := lab_of hL
  simp only [permP, List.all_eq_true, List.any_eq_true, Bool.and_eq_true] at h
  obtain ⟨X, hX, h1, h2⟩ := h _ (mem_LM hl)
  obtain ⟨hX1, hX2⟩ := of_mem_LM hX
  obtain ⟨hc, hm'⟩ := lab_props hX1
  refine ⟨(qset X.1.1, X.1.2), hc, ?_⟩
  rw [hX2, subL_eq] at h1
  rw [hX2, conjP_eq] at h2
  unfold conjToB
  rw [hm, hm']
  simp only [h1, h2, Bool.and_self]

theorem distinctB_k (h : distinctP (LM ()) = true) : distinctB () = true := by
  unfold distinctB
  refine decide_eq_true ?_
  intro L₁ L₂ h₁ h₂ hs
  obtain ⟨l₁, hl₁, rfl, hm₁⟩ := lab_of h₁
  obtain ⟨l₂, hl₂, rfl, hm₂⟩ := lab_of h₂
  simp only [distinctP, List.all_eq_true, Bool.or_eq_true, Bool.not_eq_true',
    decide_eq_true_eq] at h
  rcases h _ (mem_LM hl₁) _ (mem_LM hl₂) with h' | h'
  · rw [hm₁, hm₂] at hs
    rw [subP_eq, hs] at h'
    cases h'
  · have e : l₁ = l₂ := h'
    rw [e]

theorem six_sub : ∀ l ∈ six, l ∈ labels := by decide +kernel

theorem countB_k (h : countP ((a0List ()).map enc) (LM ()) six = true) :
    countB (a0List ()) = true := by
  have key : ∀ l ∈ labels, normB (a0List ()) (qset l.1, l.2) = decide (l ∈ six) := by
    intro l hl
    simp only [countP, List.all_eq_true, beq_iff_eq] at h
    have := h _ (mem_LM hl)
    dsimp only at this
    rw [normP_eq] at this
    unfold normB
    dsimp only
    rw [(lab_props hl).2, this]
  have hS : (Finset.univ.filter fun L : Finset (Fin 6) × Bool =>
      L.1.card = 4 ∧ normB (a0List ()) L = true) = (six.map fun l => (qset l.1, l.2)).toFinset := by
    ext L
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, List.mem_toFinset, List.mem_map]
    constructor
    · rintro ⟨hc, hn⟩
      obtain ⟨l, hl, rfl, -⟩ := lab_of hc
      rw [key l hl, decide_eq_true_eq] at hn
      exact ⟨l, hn, rfl⟩
    · rintro ⟨l, hl, rfl⟩
      exact ⟨(lab_props (six_sub l hl)).1, by rw [key l (six_sub l hl), decide_eq_true_eq]; exact hl⟩
  unfold countB
  refine decide_eq_true ?_
  rw [hS]
  decide +kernel

theorem wsubCheck_k : wsubCheck () = true := by
  have h := wsub550843_ok
  simp only [wsubK, Bool.and_eq_true, List.all_eq_true] at h
  obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := h
  have hs : ∀ s ∈ conjs (), permB s = true := fun s hs => permB_k (h2 s hs)
  unfold wsubCheck checkWith
  simp only [Bool.and_eq_true, decide_eq_true_eq]
  refine ⟨⟨⟨⟨e64B_k h1, fun v hv => hs _ ?_⟩, fun i => hs _ ?_⟩, distinctB_k h3⟩, countB_k h4⟩
  · exact List.mem_append_left _ (mem_VevenW hv)
  · exact List.mem_append_right _ (List.mem_map_of_mem (List.mem_finRange i))

end CFSG.KD.WsubE64
