module

public import Certificates.Kernel.Co2.Words
public import CFSG.Certificates.Kernel.Fi24.TauCeti

public section

namespace CertificateChecks.KernelFi24

open CFSG.KC CFSG.KC.LceS CFSG.Certificates CFSG.Certificates.LCE CertificateChecks.KernelCo2
  TauCeti TauCeti.Sporadic

noncomputable abbrev g0 : ℕ → Fi24AutomorphismGroup := pgen (Relator.relatorSet fi24AutomorphismRelators)

theorem lceEntry_eq (w : List (ℕ × Bool)) : CFSG.KC.Fi24Top.lceEntry w = Co2B.ent w := by
  unfold CFSG.KC.Fi24Top.lceEntry Co2B.ent
  congr 2
  induction w with
  | nil => rfl
  | cons l w ih =>
    rw [List.foldr_cons, ih]
    rfl

theorem swd_pgen' {n : ℕ} (rels : Set (FreeGroup (Fin n))) (w : List (Fin n × Bool)) :
    swd (pgen rels) (w.map fun l => (l.1.val, l.2)) = PresentedGroup.mk rels (FreeGroup.mk w) := by
  induction w with
  | nil => rfl
  | cons l w ih =>
    unfold swd at ih ⊢
    rw [List.map_cons, List.map_cons, List.prod_cons, ih,
      show FreeGroup.mk (l :: w) = FreeGroup.mk [l] * FreeGroup.mk w from rfl, map_mul]
    congr 1
    obtain ⟨j, b⟩ := l
    have hj := pgen_lt rels j.isLt
    cases b
    · rw [show FreeGroup.mk [(j, false)] = (FreeGroup.of j)⁻¹ from rfl, map_inv]
      simp only [Bool.false_eq_true, ↓reduceIte, hj]
      rfl
    · rw [show FreeGroup.mk [(j, true)] = FreeGroup.of j from rfl]
      simp only [↓reduceIte, hj]
      rfl

theorem rel_lens : fi24AutomorphismRelators.map (fun r => decide (r.toWord.length < 1024)) =
    List.replicate 80 true := by
  rw [fi24AutomorphismRelators_def, fi24AutomorphismAdditionalRelators_def, coxeterRelators_def,
    coxeterRelatorsOfList_def, fi24SourceEquationRelator_def, fi24SourceLongRelator_def,
    fi24SourceEquationWord_def, fi24SourceLongWord_def]
  simp only [List.map_append, List.map_map, List.map_cons, List.map_nil, Function.comp_def,
    toWord_coxeterRelator, fi24AutomorphismCoxeterMatrix_apply, fi24AutomorphismEdges_def,
    Relator.div, Relator.toWord_mul, Relator.toWord_inv, Relator.toWord_pow, Relator.toWord_gen]
  decide +kernel

theorem top_val {h : ℕ} (hh : h < 80) :
    bval g0 (wWord (CFSG.KD.Fi24B.TOPT h)) (wLen (CFSG.KD.Fi24B.TOPT h)) = 1 := by
  have hl : fi24AutomorphismRelators.length = 80 := length_fi24AutomorphismRelators
  have e := congrArg (fun L => L[h]?) CFSG.KC.Fi24Top.top_eq
  simp only [List.getElem?_map, List.getElem?_range hh, Option.map_some] at e
  rw [List.getElem?_eq_getElem (by omega), Option.map_some, Option.some_inj] at e
  rw [← e, lceEntry_eq, bval_ent]
  · rw [swd_pgen', Relator.toWord_toFreeGroup]
    exact PresentedGroup.one_of_mem (Relator.mem_relatorSet.mpr ⟨_, List.getElem_mem _, rfl⟩)
  · intro l hl'
    obtain ⟨⟨j, b⟩, -, rfl⟩ := List.mem_map.mp hl'
    exact lt_trans j.isLt (by norm_num)
  · have := congrArg (fun L => L[h]?) rel_lens
    simp only [List.getElem?_map, List.getElem?_replicate, List.getElem?_eq_getElem (by omega : h <
      fi24AutomorphismRelators.length), Option.map_some, hh, ↓reduceIte] at this
    rw [List.length_map]
    simpa using this

end CertificateChecks.KernelFi24

end
