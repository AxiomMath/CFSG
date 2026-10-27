module

public import Certificates.Kernel.PhanD4Dce.CTNet
public import Certificates.Kernel.PhanD4Dce.Residue

public section

set_option maxRecDepth 100000

namespace CFSG.KD.PhanD4Dce

open CFSG.CosetTable CFSG.Certificates CFSG.Certificates.CosetEnumeration CFSG.KC.MiscCoset
  CFSG.ClassicalInvolution.Phan.Q3G

@[expose] noncomputable def ctWs : List (List (Fin 29 × Bool)) :=
  (CFSG.KAct.PhanD4CT.R ++ CFSG.KAct.PhanD4CT.RD ++ CFSG.KAct.PhanD4CT.RC ++
    CFSG.KAct.PhanD4CT.RS).map (decodeWord 29)

theorem codes_ctWs : codes ctWs = CFSG.KAct.PhanD4CT.R ++ CFSG.KAct.PhanD4CT.RD ++
    CFSG.KAct.PhanD4CT.RC ++ CFSG.KAct.PhanD4CT.RS := by
  decide +kernel

@[expose] def lo8 : Fin 8 → Fin 29 := Fin.castLE (by decide)

@[expose] def hi8 : Fin 8 → Fin 29 := fun k => ⟨k.val + 8, by omega⟩

abbrev CTGroup : Type := PG 29 ctWs

theorem rel29 {w : List (Fin 29 × Bool)} (hw : w ∈ ctWs) :
    wordVal (fun i => (PresentedGroup.of i : CTGroup)) w = 1 := by
  rw [wordVal_of]
  exact PresentedGroup.one_of_mem (List.mem_map_of_mem hw)

theorem lo8_rels : ∀ r ∈ phanD4Rels, r.map (fun l => (lo8 l.1, l.2)) ∈ ctWs := by
  decide +kernel

@[expose] noncomputable def toCT : PhanD4Group →* CTGroup :=
  PresentedGroup.toGroup (f := fun i => PresentedGroup.of (lo8 i)) (by
    intro r hr
    simp only [Set.mem_ofPred_eq, List.mem_map] at hr
    obtain ⟨w, hw, rfl⟩ := hr
    rw [FreeGroup.lift_mk]
    exact (wordVal_reindex _ lo8 w).symm.trans (rel29 (lo8_rels w hw)))

theorem toCT_mk (w : List (Fin 8 × Bool)) :
    toCT (PresentedGroup.mk _ (FreeGroup.mk w)) =
      wordVal (fun i => (PresentedGroup.of i : CTGroup)) (w.map fun l => (lo8 l.1, l.2)) :=
  (wordVal_reindex _ lo8 w).symm

theorem rd_mem : ∀ k : Fin 8,
    (hi8 k, false) :: (decodeWord 8 ctInPhanCodes[k.val]!).map (fun l => (lo8 l.1, l.2)) ∈
      ctWs := by
  decide +kernel

theorem wordVal_cons {n : ℕ} {G : Type*} [Group G] (g : Fin n → G) (l : Fin n × Bool)
    (L : List (Fin n × Bool)) : wordVal g (l :: L) = letterVal g l * wordVal g L := by
  simp only [wordVal, List.map_cons, List.prod_cons]

theorem toCT_ctEltP (k : Fin 8) : toCT (ctEltP k) = PresentedGroup.of (hi8 k) := by
  have h := rel29 (rd_mem k)
  rw [wordVal_cons] at h
  change (PresentedGroup.of (hi8 k))⁻¹ * _ = 1 at h
  rw [ctEltP, toCT_mk]
  exact (inv_mul_eq_one.1 h).symm

theorem toCT_wordVal_ctEltP (v : List (Fin 8 × Bool)) :
    toCT (wordVal ctEltP v) =
      wordVal (fun i => (PresentedGroup.of i : CTGroup)) (v.map fun l => (hi8 l.1, l.2)) := by
  rw [← wordVal_map]
  simp only [toCT_ctEltP]
  exact (wordVal_reindex _ hi8 v).symm

theorem ct_rels_mem : ∀ v ∈ d4CtRels, v.map (fun l => (hi8 l.1, l.2)) ∈ ctWs := by
  decide +kernel

theorem toCT_ct_rel {v : List (Fin 8 × Bool)} (hv : v ∈ d4CtRels) : toCT (wordVal ctEltP v) = 1 := by
  rw [toCT_wordVal_ctEltP]
  exact rel29 (ct_rels_mem v hv)

theorem gen_mem : ∀ i : Fin 8,
    (decodeWord 8 phanInCtCodes[i.val]!).map (fun l => (hi8 l.1, l.2)) ++ [(lo8 i, false)] ∈
      ctWs := by
  decide +kernel

theorem toCT_gen (i : Fin 8) :
    toCT ((wordVal ctEltP (decodeWord 8 phanInCtCodes[i.val]!))⁻¹ * PresentedGroup.of i) = 1 := by
  have h := rel29 (gen_mem i)
  rw [wordVal_append, wordVal_cons] at h
  change _ * ((PresentedGroup.of (lo8 i))⁻¹ * 1) = 1 at h
  rw [mul_one] at h
  have e2 : toCT (PresentedGroup.of i) = PresentedGroup.of (lo8 i) := PresentedGroup.toGroup.of _
  rw [map_mul, map_inv, toCT_wordVal_ctEltP, e2, mul_inv_eq_one.1 h, inv_mul_cancel]

theorem rs_mem : ∀ j : Fin 13,
    ((⟨16 + j.val, by omega⟩ : Fin 29), false) :: decodeWord 29 (CFSG.KAct.PhanD4CT.RS[j.val]!).tail
      ∈ ctWs ∧ ∀ l ∈ decodeWord 29 (CFSG.KAct.PhanD4CT.RS[j.val]!).tail, l.1.val < 16 + j.val := by
  decide +kernel

theorem wordVal_mem {n : ℕ} {G : Type*} [Group G] (S : Subgroup G) (g : Fin n → G)
    (w : List (Fin n × Bool)) (h : ∀ l ∈ w, g l.1 ∈ S) : wordVal g w ∈ S := by
  induction w with
  | nil => exact S.one_mem
  | cons l w ih =>
    rw [wordVal_cons]
    refine S.mul_mem ?_ (ih fun l' hl' => h l' (List.mem_cons_of_mem _ hl'))
    obtain ⟨i, b⟩ := l
    have hi := h (i, b) (List.mem_cons_self ..)
    cases b
    · exact S.inv_mem hi
    · exact hi

theorem of_mem_range (n : ℕ) : ∀ g : Fin 29, g.val = n →
    (PresentedGroup.of g : CTGroup) ∈ toCT.range := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro g hg
  by_cases h8 : n < 8
  · have e : g = lo8 ⟨n, h8⟩ := Fin.ext (by simp [lo8, hg])
    exact ⟨PresentedGroup.of ⟨n, h8⟩, by rw [e]; exact PresentedGroup.toGroup.of _⟩
  by_cases h16 : n < 16
  · have e : g = hi8 ⟨n - 8, by omega⟩ := Fin.ext (by simp only [hi8]; omega)
    exact ⟨ctEltP _, by rw [e, toCT_ctEltP]⟩
  obtain ⟨hmem, hlt⟩ := rs_mem ⟨n - 16, by omega⟩
  have h := rel29 hmem
  rw [wordVal_cons] at h
  change (PresentedGroup.of _)⁻¹ * _ = 1 at h
  have e : (⟨16 + (n - 16), by omega⟩ : Fin 29) = g := Fin.ext (by simp only; omega)
  rw [← e, inv_mul_eq_one.1 h]
  exact wordVal_mem _ _ _ fun l hl => ih l.1.val (by have := hlt l hl; simp only at this; omega)
    l.1 rfl

theorem toCT_surjective : Function.Surjective toCT := by
  rw [← MonoidHom.range_eq_top, eq_top_iff, ← PresentedGroup.closure_range_of,
    Subgroup.closure_le]
  rintro _ ⟨g, rfl⟩
  exact of_mem_range _ g rfl

theorem exists_ctAct : ∃ ψ : CTGroup →* (Equiv.Perm {c : ℕ // c < 1120})ᵐᵒᵖ,
    ∀ y < 2 * 29, ∀ c : {c : ℕ // c < 1120},
      ((ψ (presLetter {r : FreeGroup (Fin 29) | r ∈ ctWs.map FreeGroup.mk} y)).unop c).1 =
        Act.step CFSG.KAct.PhanD4CT.A (29 + 29) c.1 y :=
  Act.exists_act ctWs (fun r hr => by rw [codes_ctWs] at hr; exact hr)
    (fun x hx => Act.allR_spec CFSG.KAct.PhanD4CT.all x (Nat.zero_le _) (by omega))

end CFSG.KD.PhanD4Dce

end
