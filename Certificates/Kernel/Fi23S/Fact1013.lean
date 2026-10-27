module

public import Certificates.Kernel.Fi23S.Tables
public import Certificates.Kernel.Fi23M.Keys
import CFSG.Certificates.Kernel.Spor.RawOrbEval
import Mathlib

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelFi23S

open CFSG.KC.Enum CFSG.KC.Fi23K CFSG.KC.Fi23R CFSG.KC.Fi23S CFSG.KD.Fi23K CFSG.KD.Fi23S
  CFSG.KS.Raw.Orb CFSG.KS.TBfs CFSG.KS.PC CFSG.KS.PEnum CFSG.Sporadic.Fi23.Native
  CFSG.Sporadic.Th.Native CFSG.Perm.Native CertificateChecks.KernelFi23R
  CertificateChecks.KernelFi23M

theorem sylChecks_eq (O : WOrbit) (chunks : Nat) : sylChecks O chunks =
    ((sylWords ()).all (fun w => w.all fun z => z.toNat < (chainLetters O).size) &&
      chainOK 31671 (sylLetters (chainLetters O)) sylBase chainQ (sylQb ())
        (chainTrees 31671 (sylLetters (chainLetters O)) sylBase) chunks &&
      orbitSizes (chainTrees 31671 (sylLetters (chainLetters O)) sylBase) == [512, 512] &&
      (conjTabs O (dTab O)).all (fun W => invOK 31671 W.1 W.2.1) &&
      parAll (treeTabs 31671 (chainTrees 31671 (sylLetters (chainLetters O)) sylBase)[0]!
          (sylLetters (chainLetters O))).size chunks fun k =>
        (treeTabs 31671 (chainTrees 31671 (sylLetters (chainLetters O)) sylBase)[1]!
          (sylLetters (chainLetters O))).all fun B =>
          CFSG.Sporadic.Fi23.Native.pairOK (conjTabs O (dTab O))
            (treeTabs 31671 (chainTrees 31671 (sylLetters (chainLetters O)) sylBase)[0]!
              (sylLetters (chainLetters O)))[k]! B) := rfl

theorem words_ok :
    (sylWords ()).all (fun w => w.all fun z => z.toNat < (chainLetters orbLit).size) = true := by
  rw [letters_TR.1, Array.all_eq_true]
  intro i hi
  rw [List.all_eq_true]
  intro z hz
  have hi' : i < 21 := hi
  rw [← getElem!_pos _ i hi] at hz
  exact decide_eq_true (sylWords_lt i hi' z hz).2

theorem sizes_ok : (orbitSizes (chainTrees 31671 SL sylBase) == [512, 512]) = true := by
  rw [syl_chain.1]
  have e : ∀ i : Fin 2, (tbfsRec 31671 (CNTS i.val) (TTS i.val 0) (TTS i.val 1) (TTS i.val 2)
      (TTS i.val 3)).pts.size = 512 := fun i => by
    unfold tbfsRec
    rw [Array.size_ofFn]
    rfl
  unfold orbitSizes
  rw [Array.toList_ofFn, List.map_ofFn]
  simp only [List.ofFn_succ, List.ofFn_zero, Function.comp_apply, e]
  rfl

theorem conjWords_ok : ∀ i < 2, ∀ z ∈ (conjWords ())[i]!, z = 1 ∨ z = -1 ∨ z = 2 ∨ z = -2 := by
  decide

theorem ws_get {i : Nat} (hi : i < 2) : (conjTabs orbLit (dTab orbLit))[i]! =
    (wordT 31671 (genTables orbLit) (conjWords ())[i]!,
      invT 31671 (wordT 31671 (genTables orbLit) (conjWords ())[i]!),
      compT 31671 (wordT 31671 (genTables orbLit) (conjWords ())[i]!)
        (compT 31671 (dTab orbLit) (invT 31671 (wordT 31671 (genTables orbLit)
          (conjWords ())[i]!)))) := by
  unfold conjTabs
  rw [getElem!_pos _ i (by rw [Array.size_map]; exact hi), Array.getElem_map,
    getElem!_pos _ i hi]
  rfl

theorem ws_size : (conjTabs orbLit (dTab orbLit)).size = 2 := by
  unfold conjTabs
  rw [Array.size_map]
  rfl


theorem inv_ok : (conjTabs orbLit (dTab orbLit)).all (fun W => invOK 31671 W.1 W.2.1) = true := by
  rw [Array.all_eq_true]
  intro i hi
  rw [ws_size] at hi
  rw [← getElem!_pos _ i (by rw [ws_size]; exact hi), ws_get hi]
  exact rw_invOK dP_sq (rw_wordT _ (conjWords_ok i hi))

theorem U13_eq : ∀ t < 2, U13.getD t [] = ((conjWords ())[t]!).reverse.map regZ ∧
    U13i.getD t [] = invW (((conjWords ())[t]!).reverse.map regZ) := by
  decide +kernel


theorem gK_lt {k j x : Nat} (hk : k < 512) (hj : j < 512) (hx : x < 31671) : gK k j x < 31671 := by
  rw [gK_eq hk hj hx]
  exact actN_lt _ hx

theorem leaf_ap2 {k j y : Nat} (hk : k < 512) (hj : j < 512) (hy : y < 31671) :
    ap t0[k]! (ap t1[j]! y) = gK k j y := by
  rw [← ap_comp hy, leaf_ap hk hj hy]

theorem leaf_mem {k j : Nat} (hk : k < 512) (hj : j < 512) : tv 0 k * tv 1 j ∈ Xc :=
  Subgroup.mul_mem _ (tv_mem (by decide) hk) (tv_mem (by decide) hj)

theorem actN_eq_val (p : Pt) {i : Nat} (hi : i < 31671) : actN p i = (p ⟨i, hi⟩).val :=
  actN_of_lt p hi

theorem one_of_fix {p : Pt} (hp : p ∈ Xc) (h : ∀ b < 6, actN p b = b) : p = 1 :=
  base_one hp fun i hi => by rw [← actN_eq_val p (by omega)]; exact h i hi

theorem isIdT_of {T : Table} (h : ∀ i < 31671, ap T i = i) : CFSG.Sporadic.Fi23.Native.isIdT T = true := by
  unfold CFSG.Sporadic.Fi23.Native.isIdT
  rw [CFSG.KS.TW.allIn_iff]
  intro i hi
  rw [h i hi, beq_self_eq_true]

theorem cw_rep {t : Nat} (ht : t < 2) : ∃ c ∈ Xc, ∀ y < 31671,
    ap (conjTabs orbLit (dTab orbLit))[t]!.2.2 y = cw t y ∧ actN c y = cw t y := by
  have hW := rw_wordT _ (conjWords_ok t ht)
  have hWi := rw_invT dP_sq hW
  have hC := rw_compT hW (rw_compT rw_dTab hWi)
  refine ⟨wp ((invW (((conjWords ())[t]!).reverse.map regZ) ++ [43]) ++
    ((conjWords ())[t]!).reverse.map regZ), wp_mem _, fun y hy => ?_⟩
  obtain ⟨e1, e2⟩ := U13_eq t ht
  have hcw : cw t y = wa G ((invW (((conjWords ())[t]!).reverse.map regZ) ++ [43]) ++
      ((conjWords ())[t]!).reverse.map regZ) y := by
    unfold cw
    rw [e1, e2, wa_append, wa_append, wa_cons, wa_nil, lf_eq, if_pos (by norm_num)]
  rw [ws_get ht]
  refine ⟨by rw [hC.ap hy, hcw], ?_⟩
  rw [actN_eq_val _ hy, ← idx_eq _ hy, ← hC.2.2 y hy, hC.ap hy, hcw]

theorem rw13_tab {k j u : Nat} (hk : k < 512) (hj : j < 512) (hu : u < 2) {y : Nat}
    (hy : y < 31671) : rw13 k j u y < 31671 ∧
      ap (compT 31671 (compT 31671 t0[k]! t1[j]!)
        (compT 31671 (compT 31671 (conjTabs orbLit (dTab orbLit))[u]!.1
          (compT 31671 t0[k]! t1[j]!)) (conjTabs orbLit (dTab orbLit))[u]!.2.1)) y =
        rw13 k j u y := by
  have hW := rw_wordT _ (conjWords_ok u hu)
  have hWi := rw_invT dP_sq hW
  obtain ⟨e1, e2⟩ := U13_eq u hu
  obtain ⟨a1, l1⟩ := hWi.tr.2 y hy
  have l2 := gK_lt hk hj l1
  obtain ⟨a3, l3⟩ := hW.tr.2 _ l2
  have l4 := gK_lt hk hj l3
  have er : rw13 k j u y = gK k j (wa G (((conjWords ())[u]!).reverse.map regZ)
      (gK k j (wa G (invW (((conjWords ())[u]!).reverse.map regZ)) y))) := by
    unfold rw13
    rw [e1, e2]
  refine ⟨by rw [er]; exact l4, ?_⟩
  rw [ws_get hu, er]
  simp only
  rw [ap_comp hy, ap_comp hy, a1, ap_comp l1, leaf_ap hk hj l1, a3, leaf_ap hk hj l3]

theorem o3_ok {k j t : Nat} (hk : k < 512) (hj : j < 512) (ht : t < 2)
    (hfix : ∀ b < 6, gK k j (cw t (gK k j (cw t (gK k j (cw t b))))) = b) :
    order3OK 31671 (compT 31671 (compT 31671 t0[k]! t1[j]!)
      (conjTabs orbLit (dTab orbLit))[t]!.2.2) = true := by
  obtain ⟨c, hc, hC⟩ := cw_rep ht
  have hlt : ∀ y < 31671, cw t y < 31671 := fun y hy => by rw [← (hC y hy).2]; exact actN_lt _ hy
  have hact : ∀ y < 31671, actN (tv 0 k * tv 1 j * c) y = gK k j (cw t y) := fun y hy => by
    rw [actN_mul, (hC y hy).2, ← gK_eq hk hj (hlt y hy)]
  have hh : ∀ y < 31671, ap (compT 31671 (compT 31671 t0[k]! t1[j]!)
      (conjTabs orbLit (dTab orbLit))[t]!.2.2) y = actN (tv 0 k * tv 1 j * c) y := fun y hy => by
    rw [ap_comp hy, (hC y hy).1, leaf_ap hk hj (hlt y hy), hact y hy]
  have e3 : ∀ i, actN ((tv 0 k * tv 1 j * c) ^ 3) i = actN (tv 0 k * tv 1 j * c)
      (actN (tv 0 k * tv 1 j * c) (actN (tv 0 k * tv 1 j * c) i)) := fun i => by
    rw [pow_succ, pow_succ, pow_one, actN_mul, actN_mul]
  have h3 : (tv 0 k * tv 1 j * c) ^ 3 = 1 := by
    refine one_of_fix (Subgroup.pow_mem _ (Subgroup.mul_mem _ (leaf_mem hk hj) hc) 3) fun b hb => ?_
    have hb' : b < 31671 := by omega
    have l1 := gK_lt hk hj (hlt b hb')
    have l2 := gK_lt hk hj (hlt _ l1)
    rw [e3, hact b hb', hact _ l1, hact _ l2]
    exact hfix b hb
  unfold order3OK
  rw [CFSG.KS.TW.allIn_iff]
  intro i hi
  rw [beq_iff_eq, hh i hi, hh _ (actN_lt _ hi), hh _ (actN_lt _ (actN_lt _ hi)), ← e3, h3, actN_one]

theorem leaf13 {k j : Nat} (hk : k < 512) (hj : j < 512) :
    CFSG.Sporadic.Fi23.Native.pairOK (conjTabs orbLit (dTab orbLit)) t0[k]! t1[j]! = true := by
  unfold CFSG.Sporadic.Fi23.Native.pairOK
  rcases lf13_cases (lf13_all hk hj) with ⟨-, b, hb, hne⟩ | ⟨-, hfix⟩ | ⟨-, t, ht, hfix⟩ |
      ⟨-, u, hu, ⟨b1, hb1, h1⟩, ⟨b2, hb2, h2⟩, ⟨b3, hb3, h3⟩⟩
  · have hi : invo2OK 31671 t0[k]! t1[j]! = false := by
      rw [Bool.eq_false_iff]
      intro h
      unfold invo2OK at h
      rw [CFSG.KS.TW.allIn_iff] at h
      have h' := h b (by omega)
      have hb' : b < 31671 := by omega
      rw [beq_iff_eq, leaf_ap2 hk hj (y := b) hb',
        leaf_ap2 hk hj (y := gK k j b) (gK_lt hk hj hb')] at h'
      exact hne h'
    rw [hi]
    rfl
  · have hg := one_of_fix (leaf_mem hk hj) fun b hb => by rw [← gK_eq hk hj (by omega)]; exact hfix b hb
    have hl : leafOK (conjTabs orbLit (dTab orbLit)) (compT 31671 t0[k]! t1[j]!) = true := by
      unfold leafOK
      rw [isIdT_of fun i hi => by rw [leaf_ap hk hj hi, gK_eq hk hj hi, hg, actN_one], Bool.true_or]
    rw [hl, Bool.or_true]
  · have ho := o3_ok hk hj ht hfix
    have hl : leafOK (conjTabs orbLit (dTab orbLit)) (compT 31671 t0[k]! t1[j]!) = true := by
      unfold leafOK
      refine Bool.or_eq_true_iff.2 (Or.inr ?_)
      rw [Array.any_eq_true]
      refine ⟨t, by rw [ws_size]; exact ht, ?_⟩
      rw [← getElem!_pos _ t (by rw [ws_size]; exact ht)]
      try simp only
      rw [ho, Bool.true_or]
    rw [hl, Bool.or_true]
  · have hR := fun {y : Nat} (hy : y < 31671) => rw13_tab hk hj hu hy
    have n1 : CFSG.Sporadic.Fi23.Native.isIdT (compT 31671 (compT 31671 t0[k]! t1[j]!)
        (compT 31671 (compT 31671 (conjTabs orbLit (dTab orbLit))[u]!.1
          (compT 31671 t0[k]! t1[j]!)) (conjTabs orbLit (dTab orbLit))[u]!.2.1)) = false := by
      rw [Bool.eq_false_iff]
      intro h
      unfold CFSG.Sporadic.Fi23.Native.isIdT at h
      rw [CFSG.KS.TW.allIn_iff] at h
      have h' := h b1 (by omega)
      rw [beq_iff_eq, (hR (by omega)).2] at h'
      exact h1 h'
    have n2 : CFSG.Sporadic.Th.Native.invoOK 31671 (compT 31671 (compT 31671 t0[k]! t1[j]!)
        (compT 31671 (compT 31671 (conjTabs orbLit (dTab orbLit))[u]!.1
          (compT 31671 t0[k]! t1[j]!)) (conjTabs orbLit (dTab orbLit))[u]!.2.1)) = false := by
      rw [Bool.eq_false_iff]
      intro h
      unfold CFSG.Sporadic.Th.Native.invoOK at h
      rw [CFSG.KS.TW.allIn_iff] at h
      have hb : b2 < 31671 := by omega
      have h' := h b2 hb
      rw [beq_iff_eq, (hR hb).2, (hR (hR hb).1).2] at h'
      exact h2 h'
    have n3 : order3OK 31671 (compT 31671 (compT 31671 t0[k]! t1[j]!)
        (compT 31671 (compT 31671 (conjTabs orbLit (dTab orbLit))[u]!.1
          (compT 31671 t0[k]! t1[j]!)) (conjTabs orbLit (dTab orbLit))[u]!.2.1)) = false := by
      rw [Bool.eq_false_iff]
      intro h
      unfold order3OK at h
      rw [CFSG.KS.TW.allIn_iff] at h
      have hb : b3 < 31671 := by omega
      have h' := h b3 hb
      rw [beq_iff_eq, (hR hb).2, (hR (hR hb).1).2, (hR (hR (hR hb).1).1).2] at h'
      exact h3 h'
    have hl : leafOK (conjTabs orbLit (dTab orbLit)) (compT 31671 t0[k]! t1[j]!) = true := by
      unfold leafOK
      refine Bool.or_eq_true_iff.2 (Or.inr ?_)
      rw [Array.any_eq_true]
      refine ⟨u, by rw [ws_size]; exact hu, ?_⟩
      rw [← getElem!_pos _ u (by rw [ws_size]; exact hu)]
      try simp only
      rw [n1, n2, n3]
      simp
    rw [hl, Bool.or_true]

theorem syl_ok (chunks : Nat) : sylChecks orbLit chunks = true := by
  rw [sylChecks_eq, Bool.and_eq_true, Bool.and_eq_true, Bool.and_eq_true, Bool.and_eq_true]
  refine ⟨⟨⟨⟨words_ok, syl_chain.2 chunks⟩, sizes_ok⟩, inv_ok⟩, ?_⟩
  apply parAll_of
  intro k hk
  rw [treeTabs_size (by decide)] at hk
  rw [Array.all_eq_true]
  intro j hj
  rw [treeTabs_size (by decide)] at hj
  rw [← getElem!_pos _ j (by rw [treeTabs_size (by decide)]; exact hj)]
  exact leaf13 hk hj

theorem classes_ok : classesCertificate 3 = true := by
  unfold classesCertificate
  rw [orbitData_eq']
  exact syl_ok 3

end CertificateChecks.KernelFi23S

end
