module

public import Certificates.Kernel.M23Dc.Final
public import Certificates.Kernel.M23Dc.NfWChecks
public import CFSG.Certificates.Kernel.ConjWalkLSound

public section

namespace CFSG.KD.M23Dc

open CFSG.KC.ConjWalk CFSG.KC.ConjCount CFSG.QuasithinUnique.Ch1.SporLat
  CFSG.QuasithinUnique.K1.SporadicPerm

section Walk

variable {Γ : Type} [Group Γ] [Finite Γ] [MulAction Γ (Fin 23)] [FaithfulSMul Γ (Fin 23)]

theorem noFifteen_of_walk (els : List Γ) {T Ti : List (List ℕ)} {tw recs : List ℕ}
    (hT : T = els.map (tab 23))
    (hw : walkKL 23 [19, 20, 21, 22] (encL 64 (T.getD 1 [])) (encL 64 (Ti.getD 1 []))
      (encL 64 (T.getD 3 [])) (encL 64 (Ti.getD 3 [])) (encL 64 (tabW T 23 tw)) recs = true)
    (hinv : (Nat.blt 3 T.length && invOK 23 (T.getD 1 []) (Ti.getD 1 []) &&
      invOK 23 (T.getD 3 []) (Ti.getD 3 [])) = true)
    (hord : (tw.all (· < T.length) && tabW T 23 (tw ++ tw ++ tw ++ tw ++ tw) == List.range 23 &&
      !(tabW T 23 tw == List.range 23)) = true)
    {m : ℕ} (hH : Nat.card (Subgroup.closure {x | x ∈ els}) = 5 * m) (hm : ¬ 5 ∣ m)
    (hlen : Nat.card (Subgroup.closure {x | x ∈ els}) < 15 * (recs.length + 1)) :
    ∀ z ∈ Subgroup.closure {x | x ∈ els}, orderOf z ≠ 15 := by
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  simp only [Bool.and_eq_true, Nat.blt_eq, beq_iff_eq, List.all_eq_true, decide_eq_true_eq,
    Bool.not_eq_true', beq_eq_false_iff_ne] at hinv hord
  obtain ⟨⟨h3, hi1⟩, hi3⟩ := hinv
  obtain ⟨⟨htw, h5⟩, h1⟩ := hord
  have hEl : T.length = els.length := by rw [hT, List.length_map]
  set H := Subgroup.closure {x | x ∈ els}
  have hget : ∀ l < els.length, T.getD l [] = tab 23 (els.getD l 1) := by
    intro l hl
    rw [hT, List.getD_eq_getElem _ _ (by simpa using hl), List.getD_eq_getElem _ _ hl]
    simp
  have hmem : ∀ l < els.length, els.getD l 1 ∈ H := by
    intro l hl
    rw [List.getD_eq_getElem _ _ hl]
    exact Subgroup.subset_closure (List.getElem_mem hl)
  have hg1 := hget 1 (by omega)
  have hg3 := hget 3 (by omega)
  have hv1 : Ti.getD 1 [] = tab 23 (els.getD 1 1)⁻¹ := inv_of_invOK (by rw [← hg1]; exact hi1)
  have hv3 : Ti.getD 3 [] = tab 23 (els.getD 3 1)⁻¹ := inv_of_invOK (by rw [← hg3]; exact hi3)
  have hlt : ∀ l ∈ tw, l < els.length := fun l hl => hEl ▸ htw l hl
  set t := evalL els tw with htdef
  have htab : tabW T 23 tw = tab 23 t := tabW_eq hT tw hlt
  have ht5 : t ^ 5 = 1 := by
    apply eq_of_tab (n := 23)
    have e := tabW_eq hT (tw ++ tw ++ tw ++ tw ++ tw) (by
      intro l hl
      simp only [List.mem_append, or_self] at hl
      exact hlt l hl)
    rw [h5, evalL_append, evalL_append, evalL_append, evalL_append] at e
    rw [tab_one_eq, e]
    simp only [← htdef, pow_succ, pow_zero, one_mul]
  have ht1 : t ≠ 1 := by
    intro e
    apply h1
    rw [htab, e, tab_one_eq]
  refine walkKL_noFifteen (n := 23) (hmem 1 (by omega)) (hmem 3 (by omega)) ?_ ?_ ?_ ?_ ?_
    (by decide) hw (evalL_mem (fun x hx => Subgroup.subset_closure hx) tw)
    (orderOf_eq_prime ht5 ht1) hH hm hlen
  · rw [hg1]; exact rp_encL (by norm_num) _
  · rw [hv1]; exact rp_encL (by norm_num) _
  · rw [hg3]; exact rp_encL (by norm_num) _
  · rw [hv3]; exact rp_encL (by norm_num) _
  · rw [htab]; exact rp_encL (by norm_num) _

end Walk


theorem om_size_two : (Om 2).lbl.size = 315 := by
  simpa using congrArg (fun l => l.getD 2 0) (eq_of_beq omSizesB)

theorem om_size_five : (Om 5).lbl.size = 315 := by
  simpa using congrArg (fun l => l.getD 5 0) (eq_of_beq omSizesB)

theorem Y_card_two_five {j : ℕ} (hj : j = 2 ∨ j = 5) : Nat.card (m23CtxK.Y j) = 5 * 8064 := by
  have hj16 : j < 16 := by omega
  have hjJ : j < m23CtxK.J := by rw [m23K_J]; exact hj16
  rw [m23CtxK.Y_card hjJ]
  change (m23LatK.Om[j]!).lbl.size * 2 ^ 7 = _
  rw [Om_get hj16]
  rcases hj with rfl | rfl
  · rw [om_size_two]
    norm_num
  · rw [om_size_five]
    norm_num

theorem letters_eq {j : ℕ} (hj : j < 16) :
    (m23CtxK.sg ++ m23CtxK.gens j).map (tab 23) = (mLet j).toList.map Array.toList := by
  have hjJ : j < m23CtxK.J := by rw [m23K_J]; exact hj
  rw [← mLet_eq hj]
  change _ = (m23CtxK.D.sTabs ++ m23CtxK.D.mt[j]!).toArray.toList.map Array.toList
  rw [← m23CtxK.Y_letters hjJ]
  simp [genTabs, Function.comp_def]

theorem m23K_noFifteen {j : ℕ} (hj : j = 2 ∨ j = 5) : ∀ z ∈ m23CtxK.Y j, orderOf z ≠ 15 := by
  have hc := Y_card_two_five hj
  have hj16 : j < 16 := by omega
  have hT := letters_eq hj16
  unfold LatCtx.Y at hc ⊢
  rcases hj with rfl | rfl
  · exact noFifteen_of_walk (m23CtxK.sg ++ m23CtxK.gens 2)
      (by rw [hT]; exact eq_of_beq nf2w_tabs) nf2w nf2w_inv nf2w_ord hc (by norm_num)
      (by rw [hc, eq_of_beq nf2w_len]; norm_num)
  · exact noFifteen_of_walk (m23CtxK.sg ++ m23CtxK.gens 5)
      (by rw [hT]; exact eq_of_beq nf5w_tabs) nf5w nf5w_inv nf5w_ord hc (by norm_num)
      (by rw [hc, eq_of_beq nf5w_len]; norm_num)

end CFSG.KD.M23Dc

end
