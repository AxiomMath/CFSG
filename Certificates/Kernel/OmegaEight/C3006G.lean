module

public import Certificates.Kernel.OmegaEight.C3006K1
public import Certificates.Kernel.OmegaEight.C3006K2
public import Certificates.Kernel.OmegaEight.C3006K3
public import CFSG.Certificates.Kernel.CycTabWSound

public section

set_option maxRecDepth 100000

namespace CertificateChecks.KernelO8.C3006

open Equiv CFSG.EvenSmallLie.OmegaEight CFSG.EvenSmallLie.OmegaEight.Cover CFSG.KC.CycTab
  CFSG.KC.CycTabW CFSG.Sporadic.Schreier CFSG.LieType.Multipliers

theorem cycPerm_val {n : ℕ} [NeZero n] (cs : List (List ℕ)) (x : Fin n) :
    ((cycPerm n cs x : Fin n) : ℕ) = cycsK n cs x.val := by
  rw [show cycPerm n cs = tab (cycsPerm n cs) from rfl, tab_eq, cycsK_spec]

theorem gen3006 : ((List.finRange 8).all fun j => (List.finRange 360).all fun x =>
    (genArrs[(j : ℕ)]!)[(x : ℕ)]! == ((cycPerm 360 (genCycles j) x : Fin 360) : ℕ)) = true := by
  have h := genArrs_cyc
  simp only [List.all_eq_true, List.mem_finRange, true_implies, beq_iff_eq] at h ⊢
  intro j x
  rw [cycPerm_val]
  have hx : x.val < (genArrs[(j : ℕ)]!).toList.length := by
    rw [h j]
    simp
  calc (genArrs[(j : ℕ)]!)[(x : ℕ)]! = (genArrs[(j : ℕ)]!).toList[x.val]'hx := by
        rw [getElem!_pos _ _ (by simpa using hx), Array.getElem_toList]
    _ = ((List.range 360).map (cycsK 360 (genCycles j)))[x.val]'(by simp) :=
        List.getElem_of_eq (h j) hx
    _ = cycsK 360 (genCycles j) x.val := by simp

theorem lettersX : LetterOKW 9 D.TX fun r : Fin 8 => cycPerm 360 (genCycles r) := by
  refine tabsW_sound tabX fun r x => ?_
  rw [cycPerm_val]
  fin_cases r <;> rfl

theorem genList_getD {k : ℕ} (hk : k < 8) :
    genList.getD k 1 = cycPerm 360 (genCycles (Fin.ofNat 8 k)) := by
  interval_cases k <;> rfl

theorem evalCodes_val (x : Fin 360) : ∀ c : List ℤ, (∀ z ∈ c, z ≠ 0 ∧ z.natAbs ≤ 8) →
    ((evalCodes genList c x : Fin 360) : ℕ) = wordW 360 9 D.TX ((c.map zL).map codeW) x.val
  | [], _ => rfl
  | z :: c, hc => by
    have hz := hc z (List.mem_cons_self ..)
    have ih := evalCodes_val x c fun z' hz' => hc z' (List.mem_cons_of_mem _ hz')
    have hr : z.natAbs - 1 < 8 := by omega
    rw [evalCodes, Perm.mul_apply, List.map_cons, List.map_cons]
    change _ = fgW 9 D.TX (codeW (zL z) * 360 + wordW 360 9 D.TX ((c.map zL).map codeW) x.val)
    rw [← ih, ← lettersX (zL z) (evalCodes genList c x)]
    by_cases h0 : 0 < z
    · have hk : z.toNat - 1 = z.natAbs - 1 := by omega
      simp only [h0, if_true, letter, zL, decide_true, cond_true]
      rw [hk, genList_getD hr]
    · have hk : (-z).toNat - 1 = z.natAbs - 1 := by omega
      simp only [h0, if_false, letter, zL, decide_false, cond_false]
      rw [hk, genList_getD hr]

theorem lettersA : LetterOKW 9 D.TA gens := by
  refine tabsW_sound tabA fun i x => ?_
  rw [gens, tab_eq, evalCodes_val x _ (by fin_cases i <;> decide +kernel)]
  fin_cases i <;> rfl

theorem word_eq (w : List (Fin 4 × Bool)) : word w = (w.map (letter gens)).prod := rfl

theorem rhoWord_eq (w : List (Fin 4 × Bool)) : rhoWord w = (w.map (letter rhoGens)).prod := rfl

theorem model3006 : ((rels.all fun r => decide (word r = 1)) && ((List.finRange 4).all fun i =>
    decide (word (commWords (pairs i)) = gens i)) && ((List.finRange 8).all fun j =>
    decide (word (genWords j) = cycPerm 360 (genCycles j))) && decide (word uWord * word uWord =
    1) && decide (word tuWord = rhoT * word uWord * rhoT⁻¹)) = true := by
  have hc := commA
  have hg := genWordsA
  simp only [List.all_eq_true, List.mem_finRange, true_implies] at hc hg
  simp only [Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq, List.mem_finRange,
    true_implies]
  refine ⟨⟨⟨⟨fun r hr => ?_, fun i => ?_⟩, fun j => ?_⟩, ?_⟩, ?_⟩
  · rw [word_eq]
    exact onesOKW_sound lettersA relsA r (List.mem_map_of_mem hr)
  · rw [word_eq]
    ext x
    rw [eqOKW_sound lettersA (hc i) x]
    have := lettersA (i, true) x
    simp only [letter, cond_true, codeW, Nat.add_zero] at this
    rw [this]
  · rw [word_eq]
    ext x
    rw [eqOKW_sound lettersA (hg j) x, cycPerm_val]
  · rw [word_eq, ← List.prod_append, ← List.map_append]
    exact onesOKW_sound lettersA uA _ (List.mem_singleton_self _)
  · ext x
    rw [word_eq, eqOKW_sound lettersA tuA x, Perm.mul_apply, Perm.mul_apply, word_eq]
    change _ = (((uWord.map (letter gens)).prod (rhoT⁻¹ x) : ℕ) + 120) % 360
    rw [wordW_val lettersA (rhoT⁻¹ x) uWord]
    rfl

theorem lettersR : LetterOKW 8 D.TR rhoGens := by
  refine tabsW_sound tabR fun i x => ?_
  rw [rhoGens, cycPerm_val]
  fin_cases i <;> rfl

theorem rho3006 : ((coverWs.all fun r => decide (rhoWord r = 1)) && decide (rhoWord uWord *
    rhoWord uWord = 1) && !decide (rhoWord tuWord * rhoWord tuWord = 1)) = true := by
  simp only [Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq, Bool.not_eq_true',
    decide_eq_false_iff_not]
  refine ⟨⟨fun r hr => ?_, ?_⟩, ?_⟩
  · rw [rhoWord_eq]
    exact onesOKW_sound lettersR covR r (List.mem_map_of_mem hr)
  · rw [rhoWord_eq, ← List.prod_append, ← List.map_append]
    exact onesOKW_sound lettersR uR _ (List.mem_singleton_self _)
  · rw [rhoWord_eq, ← List.prod_append, ← List.map_append]
    have h := tuR
    rw [Bool.not_eq_true'] at h
    exact ne_one_of_eqOKW lettersR h

end CertificateChecks.KernelO8.C3006

end
