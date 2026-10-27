module

public import Certificates.Kernel.McLCls.Glue3

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelMcLCls

open Subgroup CFSG.KC.Enum CFSG.KS CFSG.KS.Prim CFSG.KS.Raw CFSG.KS.Raw.Orb CFSG.KC.M305
  CertificateChecks.KernelLC.McLC CFSG.Sporadic.Th CFSG.Sporadic.SmallOddCore CFSG.Quasithin.KGC31
  CFSG.SectionRank.QTK.Insp443.McLCls CFSG.Sporadic.Th.Native CFSG.Sporadic.Schreier
  CFSG.Sporadic.SmallOddCore.Native CFSG.KS.MulH

theorem W_eq : F.W = eSub basis_fact := (eSub_eq_closure basis_fact).symm

theorem bit_oPts : ∀ i < 275, m305bit (m305mask oPts) i = oPts.contains i := by
  decide +kernel

theorem allfix_iff {i : Nat} (hi : i < 275) :
    m305all (fun b => Nat.beq (pg 9 (mask 9) b i) i) bs = true ↔ ∀ j, F.v j ⟨i, hi⟩ = ⟨i, hi⟩ := by
  rw [m305all_iff, v_eq]
  constructor
  · intro h j
    have e := Nat.eq_of_beq_eq_true (h _ (mem_bsF j))
    rw [prep_bsF j ⟨i, hi⟩] at e
    exact Fin.ext e
  · intro h b hb
    have key : ∀ j : Fin 4, Nat.beq (pg 9 (mask 9) (bsF j) i) i = true := fun j => by
      have e : pg 9 (mask 9) (bsF j) i = (vs[j] ⟨i, hi⟩ : ℕ) := prep_bsF j ⟨i, hi⟩
      have h' : vs[j] ⟨i, hi⟩ = ⟨i, hi⟩ := h j
      rw [e, h']
      exact Nat.beq_refl _
    simp only [bs, List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · exact key 0
    · exact key 1
    · exact key 2
    · exact key 3

theorem fixO (i : Fin 275) : (∀ u ∈ eSub basis_fact, u i = i) ↔ i ∈ F.O := by
  rw [fix_eSub_iff basis_fact i]
  have hf := CFSG.KS.Raw.Orb.allN_iff.1 fix i i.2
  have hb := bit_oPts i i.2
  simp only [F.O, Finset.mem_filter, Finset.mem_univ, true_and]
  have key := allfix_iff (i := i.val) i.2
  have ei : (⟨i.val, i.2⟩ : Fin 275) = i := rfl
  rw [ei] at key
  rw [← key, ← List.contains_iff_mem, ← hb]
  revert hf
  cases m305bit (m305mask oPts) i
  · intro hf
    change bIf(_, false, true) = true at hf
    rcases bif_iff.1 hf with ⟨-, h⟩ | ⟨h, -⟩
    · exact absurd h Bool.false_ne_true
    · simp [h]
  · intro hf
    simp [hf]

theorem dist_nodup : ∀ {L : List Nat}, m305dist L = true → L.Nodup
  | [], _ => List.nodup_nil
  | x :: xs, h => by
    change bAnd(m305all (fun y => bIf(Nat.beq x y, false, true)) xs, m305dist xs) = true at h
    rw [band] at h
    refine List.nodup_cons.mpr ⟨fun hx => ?_, dist_nodup h.2⟩
    have h1 := (m305all_iff xs).1 h.1 x hx
    rw [Nat.beq_refl] at h1
    exact Bool.noConfusion h1

theorem testBit_img {P : Nat} {g : Equiv.Perm (Fin 275)} (hP : PRep 275 9 P g) :
    ∀ (L : List Nat) (hL : ∀ p ∈ L, p < 275) (q : Nat),
      (m305img L P).testBit q = true ↔ ∃ p, ∃ hp : p ∈ L, ((g ⟨p, hL p hp⟩ : Fin 275) : ℕ) = q
  | [], _, q => by
    change (0 : Nat).testBit q = true ↔ _
    simp
  | p :: L, hL, q => by
    have hp : p < 275 := hL p List.mem_cons_self
    have ih := testBit_img hP L (fun x hx => hL x (List.mem_cons_of_mem p hx)) q
    change (Nat.lor (m305img L P) (Nat.shiftLeft 1 (pg 9 (mask 9) P p))).testBit q = true ↔ _
    have e : pg 9 (mask 9) P p = (g ⟨p, hp⟩ : ℕ) := hP ⟨p, hp⟩
    rw [e]
    change (m305img L P ||| 1 <<< ((g ⟨p, hp⟩ : Fin 275) : ℕ)).testBit q = true ↔ _
    rw [Nat.testBit_or, Bool.or_eq_true, ih, Nat.one_shiftLeft, Nat.testBit_two_pow,
      decide_eq_true_eq]
    constructor
    · rintro (⟨x, hx, e⟩ | e)
      · exact ⟨x, List.mem_cons_of_mem p hx, e⟩
      · exact ⟨p, List.mem_cons_self, e⟩
    · rintro ⟨x, hx, e⟩
      rcases List.mem_cons.mp hx with rfl | hx'
      · exact Or.inr e
      · exact Or.inl ⟨x, hx', e⟩

theorem oS_lt : ∀ p ∈ oS, p < 275 := by decide

theorem mem_oS_iff (i : Fin 275) : i.val ∈ oS ↔ i ∈ F.O := by
  simp only [F.O, Finset.mem_filter, Finset.mem_univ, true_and]
  have h : ∀ p < 275, (p ∈ oS ↔ p ∈ oPts) := by decide
  exact h i i.2

theorem img_eq {P Q : Nat} {g h : Equiv.Perm (Fin 275)} (hP : PRep 275 9 P g)
    (hQ : PRep 275 9 Q h) (e : F.O.image g = F.O.image h) : m305img oS P = m305img oS Q := by
  apply Nat.eq_of_testBit_eq
  intro q
  have key : ∀ (R : Nat) (f : Equiv.Perm (Fin 275)), PRep 275 9 R f →
      ((m305img oS R).testBit q = true ↔ ∃ i ∈ F.O.image f, (i : ℕ) = q) := by
    intro R f hR
    rw [testBit_img hR oS oS_lt q]
    constructor
    · rintro ⟨p, hp, e⟩
      exact ⟨f ⟨p, oS_lt p hp⟩, Finset.mem_image_of_mem _ ((mem_oS_iff _).1 hp), e⟩
    · rintro ⟨i, hi, e⟩
      obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hi
      exact ⟨j.val, (mem_oS_iff j).2 hj, e⟩
  have h1 := key P g hP
  have h2 := key Q h hQ
  rw [e] at h1
  cases e1 : (m305img oS P).testBit q <;> cases e2 : (m305img oS Q).testBit q
  · rfl
  · exact absurd (h1.2 (h2.1 e2)) (by rw [e1]; exact Bool.false_ne_true)
  · exact absurd (h2.2 (h1.1 e1)) (by rw [e2]; exact Bool.false_ne_true)
  · rfl


@[expose] noncomputable def hO (k : Fin 15) : Equiv.Perm (Fin 275) :=
  ((oWd.getD k []).map gH).prod

theorem hO_mem (k : Fin 15) : hO k ∈ F.H := word_mem _

theorem img_inj {k l : Fin 15} (e : F.O.image (hO k) = F.O.image (hO l)) : k = l := by
  have hd := dist_nodup orbO
  have hk : ∀ k : Fin 15, (oWd.map fun wd => m305img oS (m305word hL wd))[k.val]'(by
      simp [oWd]) = m305img oS (m305word hL (oWd.getD k [])) := by
    intro k
    rw [List.getElem_map, List.getD_eq_getElem _ _ (by simp [oWd])]
  have em := img_eq (prep_word prep_hL (oWd.getD k [])) (prep_word prep_hL (oWd.getD l [])) e
  rw [← hk k, ← hk l] at em
  exact Fin.ext ((List.Nodup.getElem_inj_iff hd).1 em)

theorem image_stab {s : Equiv.Perm (Fin 275)} (hs : s ∈ setStab F.O) : F.O.image s = F.O := by
  refine Finset.eq_of_subset_of_card_le ?_ ?_
  · intro i hi
    obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hi
    exact (hs j).1 hj
  · rw [Finset.card_image_of_injective _ s.injective]

theorem card_stab : Nat.card ↥(F.H ⊓ setStab F.O) ≤ 2688 := by
  classical
  let f : Fin 15 × ↥(F.H ⊓ setStab F.O) → ↥F.H := fun ks =>
    ⟨hO ks.1 * (ks.2 : Equiv.Perm (Fin 275)),
      F.H.mul_mem (hO_mem ks.1) (Subgroup.mem_inf.mp ks.2.2).1⟩
  have hf : Function.Injective f := by
    rintro ⟨k, s⟩ ⟨l, t⟩ e
    have e1 : hO k * (s : Equiv.Perm (Fin 275)) = hO l * (t : Equiv.Perm (Fin 275)) :=
      congrArg Subtype.val e
    have ek : k = l := by
      apply img_inj
      have hs := image_stab (Subgroup.mem_inf.mp s.2).2
      have ht := image_stab (Subgroup.mem_inf.mp t.2).2
      calc F.O.image (hO k) = (F.O.image (s : Equiv.Perm (Fin 275))).image (hO k) := by rw [hs]
        _ = F.O.image (hO k * (s : Equiv.Perm (Fin 275))) := by rw [Finset.image_image]; rfl
        _ = F.O.image (hO l * (t : Equiv.Perm (Fin 275))) := by rw [e1]
        _ = (F.O.image (t : Equiv.Perm (Fin 275))).image (hO l) := by rw [Finset.image_image]; rfl
        _ = F.O.image (hO l) := by rw [ht]
    subst ek
    have : (s : Equiv.Perm (Fin 275)) = t := mul_left_cancel e1
    exact Prod.ext rfl (Subtype.ext this)
  have h := Nat.card_le_card_of_injective f hf
  rw [Nat.card_prod, Nat.card_eq_fintype_card (α := Fin 15), Fintype.card_fin, card_H] at h
  omega

theorem card_normH :
    Nat.card ↥(F.H ⊓ normalizer (F.W : Set (Equiv.Perm (Fin 275)))) ≤ 2688 := by
  refine le_trans (Subgroup.card_le_of_le ?_) card_stab
  intro g hg
  refine Subgroup.mem_inf.mpr ⟨(Subgroup.mem_inf.mp hg).1, ?_⟩
  have hN : g ∈ eNorm basis_fact := by
    have h := (Subgroup.mem_inf.mp hg).2
    rw [W_eq] at h
    exact h
  exact mem_setStab_of_normalizer basis_fact (fun i => fixO i) hN

end CertificateChecks.KernelMcLCls

end
