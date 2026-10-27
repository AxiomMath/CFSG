module

public import Certificates.Kernel.PhanB3.CT
public import Certificates.Kernel.PhanB3.Glue
public import CFSG.ClassicalInvolution.Phan.Phan3B3CTData

public section

set_option maxRecDepth 100000

namespace CertificateChecks.KernelPhanB3

open CFSG.CosetTable CFSG.Certificates CFSG.Certificates.CosetEnumeration CFSG.KC.MiscCoset
  CFSG.ClassicalInvolution.Phan.Q3G

@[expose] noncomputable def ctWs : List (List (Fin 14 × Bool)) :=
  (CFSG.KAct.PhanB3CT.R ++ CFSG.KAct.PhanB3CT.RD ++ CFSG.KAct.PhanB3CT.RC).map (decodeWord 14)

theorem codes_ctWs :
    codes ctWs = CFSG.KAct.PhanB3CT.R ++ CFSG.KAct.PhanB3CT.RD ++ CFSG.KAct.PhanB3CT.RC := by
  decide +kernel

@[expose] def lo8 : Fin 8 → Fin 14 := Fin.castLE (by decide)

@[expose] def hi6 : Fin 6 → Fin 14 := fun k => ⟨k.val + 8, by omega⟩

abbrev CTGroup : Type := PG 14 ctWs

theorem rel14 {w : List (Fin 14 × Bool)} (hw : w ∈ ctWs) :
    wordVal (fun i => (PresentedGroup.of i : CTGroup)) w = 1 := by
  rw [wordVal_of]
  exact PresentedGroup.one_of_mem (List.mem_map_of_mem hw)

theorem lo8_rels : ∀ r ∈ phanB3Rels, r.map (fun l => (lo8 l.1, l.2)) ∈ ctWs := by
  decide +kernel

@[expose] noncomputable def toCT : PhanB3Group →* CTGroup :=
  PresentedGroup.toGroup (f := fun i => PresentedGroup.of (lo8 i)) (by
    intro r hr
    simp only [Set.mem_ofPred_eq, List.mem_map] at hr
    obtain ⟨w, hw, rfl⟩ := hr
    rw [FreeGroup.lift_mk]
    exact (wordVal_reindex _ lo8 w).symm.trans (rel14 (lo8_rels w hw)))

theorem toCT_mk (w : List (Fin 8 × Bool)) :
    toCT (PresentedGroup.mk _ (FreeGroup.mk w)) =
      wordVal (fun i => (PresentedGroup.of i : CTGroup)) (w.map fun l => (lo8 l.1, l.2)) :=
  (wordVal_reindex _ lo8 w).symm

@[expose] noncomputable def ctElt (k : Fin 6) : PhanB3Group :=
  PresentedGroup.mk _ (FreeGroup.mk (decodeWord 8 b3CtInPhanCodes[k.val]!))

theorem rd_mem : ∀ k : Fin 6,
    (hi6 k, false) :: (decodeWord 8 b3CtInPhanCodes[k.val]!).map (fun l => (lo8 l.1, l.2)) ∈
      ctWs := by
  decide +kernel

theorem wordVal_cons {n : ℕ} {G : Type*} [Group G] (g : Fin n → G) (l : Fin n × Bool)
    (L : List (Fin n × Bool)) : wordVal g (l :: L) = letterVal g l * wordVal g L := by
  simp only [wordVal, List.map_cons, List.prod_cons]

theorem toCT_ctElt (k : Fin 6) : toCT (ctElt k) = PresentedGroup.of (hi6 k) := by
  have h := rel14 (rd_mem k)
  rw [wordVal_cons] at h
  change (PresentedGroup.of (hi6 k))⁻¹ * _ = 1 at h
  rw [ctElt, toCT_mk]
  exact (inv_mul_eq_one.1 h).symm

theorem toCT_wordVal_ctElt (v : List (Fin 6 × Bool)) :
    toCT (wordVal ctElt v) =
      wordVal (fun i => (PresentedGroup.of i : CTGroup)) (v.map fun l => (hi6 l.1, l.2)) := by
  rw [← wordVal_map]
  simp only [toCT_ctElt]
  exact (wordVal_reindex _ hi6 v).symm

theorem ct_rels_mem : ∀ v ∈ b3Sl3EdgeRels ++ b3Sp4EdgeRels ++ b3CtCommRels,
    v.map (fun l => (hi6 l.1, l.2)) ∈ ctWs := by
  decide +kernel

theorem toCT_ct_rel {v : List (Fin 6 × Bool)}
    (hv : v ∈ b3Sl3EdgeRels ++ b3Sp4EdgeRels ++ b3CtCommRels) : toCT (wordVal ctElt v) = 1 := by
  rw [toCT_wordVal_ctElt]
  exact rel14 (ct_rels_mem v hv)

theorem gen_mem : ∀ i : Fin 8,
    (decodeWord 6 b3PhanInCtCodes[i.val]!).map (fun l => (hi6 l.1, l.2)) ++ [(lo8 i, false)] ∈
      ctWs := by
  decide +kernel

theorem toCT_gen (i : Fin 8) :
    toCT ((wordVal ctElt (decodeWord 6 b3PhanInCtCodes[i.val]!))⁻¹ * PresentedGroup.of i) = 1 := by
  have h := rel14 (gen_mem i)
  rw [wordVal_append, wordVal_cons] at h
  change _ * ((PresentedGroup.of (lo8 i))⁻¹ * 1) = 1 at h
  rw [mul_one] at h
  have e2 : toCT (PresentedGroup.of i) = PresentedGroup.of (lo8 i) := PresentedGroup.toGroup.of _
  rw [map_mul, map_inv, toCT_wordVal_ctElt, e2, mul_inv_eq_one.1 h, inv_mul_cancel]

theorem exists_ctAct : ∃ ψ : CTGroup →* (Equiv.Perm {c : ℕ // c < 1120})ᵐᵒᵖ,
    ∀ y < 2 * 14, ∀ c : {c : ℕ // c < 1120},
      ((ψ (presLetter {r : FreeGroup (Fin 14) | r ∈ ctWs.map FreeGroup.mk} y)).unop c).1 =
        Act.step CFSG.KAct.PhanB3CT.A (14 + 14) c.1 y :=
  Act.exists_act ctWs (fun r hr => by rw [codes_ctWs] at hr; exact hr)
    (fun x hx => Act.allR_spec CFSG.KAct.PhanB3CT.all x (Nat.zero_le _) (by omega))

theorem ct_facts : ∃ χ : PhanB3Group →* (Equiv.Perm {c : ℕ // c < 1120})ᵐᵒᵖ,
    (∀ (w : List (Fin 8 × Bool)) (c : {c : ℕ // c < 1120}),
      ((χ (PresentedGroup.mk _ (FreeGroup.mk w))).unop c).1 =
        Act.walk CFSG.KAct.PhanB3CT.A (14 + 14)
          ((w.map fun l => (lo8 l.1, l.2)).map letterCode) c.1) ∧
    (∀ v ∈ b3Sl3EdgeRels ++ b3Sp4EdgeRels ++ b3CtCommRels, wordVal ctElt v ∈ χ.ker) ∧
    ∀ i : Fin 8,
      (wordVal ctElt (decodeWord 6 b3PhanInCtCodes[i.val]!))⁻¹ * PresentedGroup.of i ∈ χ.ker := by
  obtain ⟨ψ, hψ⟩ := exists_ctAct
  refine ⟨ψ.comp toCT, fun w c => ?_, fun v hv => ?_, fun i => ?_⟩
  · rw [MonoidHom.comp_apply, toCT_mk, wordVal_of]
    exact Act.act_mk ψ hψ _ c
  · rw [MonoidHom.mem_ker, MonoidHom.comp_apply, toCT_ct_rel hv, map_one]
  · rw [MonoidHom.mem_ker, MonoidHom.comp_apply, toCT_gen i, map_one]

end CertificateChecks.KernelPhanB3

end
