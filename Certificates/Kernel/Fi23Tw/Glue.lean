
module

public import Certificates.Kernel.Fi23Tw.Prof
import Certificates.Kernel.Fi23Tw.Comm
import Certificates.Kernel.Fi23Tw.Twin
import Certificates.Kernel.Fi23Tw.Tg
public import Certificates.Kernel.Fi23Tw.Facts

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelFi23Tw

open CFSG.Sporadic.Fi23 CFSG.Sporadic.Th CFSG.KC.Enum CFSG.KC.Fi23K CFSG.KD.Fi23K
  CFSG.KC.Fi23R CFSG.KC.Fi23Five CFSG.KC.Fi23Tw CFSG.KD.Fi23Tw CFSG.KD.Fi23Cls
  CertificateChecks.KernelFi23Q CertificateChecks.KernelFi23Cls
  CFSG.HardMathSupport.Dickson.I271.TabFi23 CFSG.KS.Raw.Orb
  CFSG.Sporadic.Fi23.Native CFSG.HardMathSupport.Dickson.I271.TabFi23C CFSG.Sporadic.Th.Native
  CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Fi23Five
  CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Fi23Native
  CFSG.HardMathSupport.Timmesfeld.SporadicBalance.BThreeFi23Native
open CFSG.HardMathSupport.Timmesfeld.SporadicBalance.BThreeFi23 (t3 rep_t3Tabs)

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

section Bridge

theorem twinCheck_of {T : Table} {x : CFSG.Sporadic.Fi23.J} (hT : Rep 31671 T x) {k : ℕ}
    (h1 : ∀ a : Fin 31671, x • a = a → ∃ b, Twin ePt x a b)
    (h2 : ∀ a b a' b', Twin ePt x a b → Twin ePt x a' b' → ePt a' * ePt b' = ePt a * ePt b →
      (a' = a ∧ b' = b) ∨ (a' = b ∧ b' = thirdPt a b) ∨ (a' = thirdPt a b ∧ b' = a))
    (h2b : ∀ a b, Twin ePt x a b → thirdPt a b ≠ a ∧ thirdPt a b ≠ b)
    (h3 : ∀ a b a' b', Twin ePt x a b → Twin ePt x a' b' →
      ePt a * ePt b * (ePt a' * ePt b') = ePt a' * ePt b' * (ePt a * ePt b))
    (h4 : ∀ (t : Fin chainQ.size) (c' : Fin 31671),
      (∀ a : Fin 31671, x • a = a → (ePt c' * ePt a = ePt a * ePt c' ↔
        ePt (cPt k t) * ePt a = ePt a * ePt (cPt k t))) →
      c' = cPt k t ∨ c' = x • cPt k t ∨ c' = x • x • cPt k t) :
    twinCheck orb (dTable orb) (genTables orb (-2)) T k = true := by
  have hfix := mem_fixList_iff' hT
  have hlt : ∀ {a : ℕ}, a ∈ fixList T → a < 31671 := fun h =>
    CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Fi23Five.lt_of_mem_fixList h
  have hP : ∀ {a b : ℕ}, (a, b) ∈ twinPairs orb (dTable orb) (genTables orb (-2)) (fixList T) →
      ∃ (ha : a < 31671) (hb : b < 31671), Twin ePt x ⟨a, ha⟩ ⟨b, hb⟩ := by
    intro a b hab
    obtain ⟨hFa, hFb, -⟩ := mem_twinPairs.1 hab
    exact ⟨hlt hFa, hlt hFb, (twin_iff hT ⟨a, hlt hFa⟩ ⟨b, hlt hFb⟩).2 hab⟩
  unfold twinCheck
  simp only [Bool.and_eq_true]
  refine ⟨⟨⟨?_, ?_⟩, ?_⟩, ?_⟩
  · unfold twinCheck1
    rw [List.all_eq_true]
    intro a ha
    obtain ⟨b, hb⟩ := h1 ⟨a, hlt ha⟩ ((hfix ⟨a, hlt ha⟩).1 ha)
    rw [List.any_eq_true]
    exact ⟨(a, b.val), (twin_iff hT ⟨a, hlt ha⟩ b).1 hb, beq_self_eq_true a⟩
  · unfold twinCheck2
    rw [List.all_eq_true]
    rintro ⟨a, b⟩ hab
    obtain ⟨ha, hb, htw⟩ := hP hab
    have e3 := thirdPt_val ⟨a, ha⟩ ⟨b, hb⟩
    obtain ⟨n1, n2⟩ := h2b _ _ htw
    dsimp only
    rw [Bool.and_eq_true, Bool.and_eq_true, bne_iff_ne, bne_iff_ne, List.all_eq_true]
    refine ⟨⟨fun h => n1 (Fin.ext (e3.trans h)), fun h => n2 (Fin.ext (e3.trans h))⟩, ?_⟩
    rintro ⟨a', b'⟩ hab'
    obtain ⟨ha', hb', htw'⟩ := hP hab'
    dsimp only
    cases hs : sigEq orb (dTable orb) (genTables orb (-2)) [a, b] [a', b'] with
    | false => simp only [Bool.not_false, Bool.true_or]
    | true =>
      have hE := prod_eq_of_sigEq hs
      have hE' : ePt ⟨a', ha'⟩ * ePt ⟨b', hb'⟩ = ePt ⟨a, ha⟩ * ePt ⟨b, hb⟩ := by
        simpa [ePt, List.prod_cons, mul_one] using hE.symm
      simp only [Bool.not_true, Bool.false_or, Bool.or_eq_true, beq_iff_eq, Prod.mk.injEq]
      rcases h2 _ _ _ _ htw htw' hE' with ⟨h8, h9⟩ | ⟨h8, h9⟩ | ⟨h8, h9⟩
      · exact Or.inl (Or.inl ⟨congrArg Fin.val h8, congrArg Fin.val h9⟩)
      · exact Or.inl (Or.inr ⟨congrArg Fin.val h8, (congrArg Fin.val h9).trans e3⟩)
      · exact Or.inr ⟨(congrArg Fin.val h8).trans e3, congrArg Fin.val h9⟩
  · unfold twinCheck3
    rw [List.all_eq_true]
    rintro ⟨a, b⟩ hab
    rw [List.all_eq_true]
    rintro ⟨a', b'⟩ hab'
    obtain ⟨ha, hb, htw⟩ := hP hab
    obtain ⟨ha', hb', htw'⟩ := hP hab'
    apply sigEq_of_prod_eq
    have h := h3 _ _ _ _ htw htw'
    simpa [ePt, List.prod_cons, mul_assoc] using h
  · unfold twinCheck4
    rw [List.all_eq_true]
    intro t ht
    have ht' := List.mem_range.1 ht
    have hv : (cPt k ⟨t, ht'⟩).val = rf orb (dTable orb) (genTables orb (-2)) k chainQ[t]! :=
      cPt_val k ⟨t, ht'⟩
    rw [← hv]
    unfold goodPt
    rw [Bool.and_eq_true]
    refine ⟨decide_eq_true (cPt k ⟨t, ht'⟩).2, ?_⟩
    rw [List.all_eq_true]
    intro c hc
    have hclt := List.mem_range.1 hc
    cases hs : (fixList T).all (fun a => commB orb (dTable orb) (genTables orb (-2)) c a ==
        commB orb (dTable orb) (genTables orb (-2)) (cPt k ⟨t, ht'⟩).val a) with
    | false => simp only [Bool.not_false, Bool.true_or]
    | true =>
      have hprof : ∀ a : Fin 31671, x • a = a →
          (ePt ⟨c, hclt⟩ * ePt a = ePt a * ePt ⟨c, hclt⟩ ↔
            ePt (cPt k ⟨t, ht'⟩) * ePt a = ePt a * ePt (cPt k ⟨t, ht'⟩)) := by
        intro a ha
        have h5 := (List.all_eq_true.1 hs) a.val ((hfix a).2 ha)
        rw [beq_iff_eq] at h5
        exact (commB_iff' ⟨c, hclt⟩ a).symm.trans
          ((Bool.eq_iff_iff.1 h5).trans (commB_iff' (cPt k ⟨t, ht'⟩) a))
      simp only [Bool.not_true, Bool.false_or, Bool.or_eq_true, beq_iff_eq]
      rcases h4 ⟨t, ht'⟩ ⟨c, hclt⟩ hprof with h | h | h
      · exact Or.inl (Or.inl (congrArg Fin.val h))
      · exact Or.inl (Or.inr ((congrArg Fin.val h).trans (ap_eq_smul hT _).symm))
      · refine Or.inr ?_
        rw [ap_eq_smul hT, ap_eq_smul hT]
        exact congrArg Fin.val h

end Bridge

theorem chainQ_get : ∀ t < chainQ.size, chainQ[t]! = t := by decide

theorem TG_len : CFSG.KD.Fi23Tw.TG.length = 6 := by decide

theorem chainQ_size : chainQ.size = 6 := by decide

theorem cPt4_val (t : Fin chainQ.size) : (cPt 4 t).val = tA G 4 t.val := by
  unfold cPt
  rw [← idx_of_lt _ (chainQ_lt t.2), conjPt_acts (by norm_num) _ (chainQ_lt t.2),
    chainQ_get t.val t.2]

theorem tg_head {t : ℕ} (ht : t < 6) :
    (CFSG.KD.Fi23Tw.TG.getD t []).getD 0 0 = tA G 4 t := by
  have h := allN_iff.1 (ch17340tgc_ok : tgc = true) t ht
  rw [Nat.beq_eq, nthL_eq] at h
  rw [← h]
  unfold tgHeads
  have e : (CFSG.KD.Fi23Tw.TG.map fun g => nthL g (nat_lit 0)).getD t 0 =
      (CFSG.KD.Fi23Tw.TG.map fun g => nthL g (nat_lit 0)).getD t (nthL [] 0) := rfl
  rw [e, List.getD_map, nthL_eq]

theorem x_cube (y : Fin 31671) : t3 2 • t3 2 • t3 2 • y = y := by
  have hx : orderOf (t3 2) = 3 := Certificates.certificate17338.2.2.1.1
  have h1 := pow_orderOf_eq_one (t3 2)
  rw [hx, pow_three'] at h1
  rw [← mul_smul, ← mul_smul, h1, one_smul]

theorem hK4 : ∀ (t : Fin chainQ.size) (c' : Fin 31671),
    (∀ a : Fin 31671, t3 2 • a = a → (ePt c' * ePt a = ePt a * ePt c' ↔
      ePt (cPt 4 t) * ePt a = ePt a * ePt (cPt 4 t))) →
    c' = cPt 4 t ∨ c' = t3 2 • cPt 4 t ∨ c' = t3 2 • t3 2 • cPt 4 t := by
  intro t c' hprof
  have ht6 : t.val < 6 := chainQ_size ▸ t.2
  have hgm : CFSG.KD.Fi23Tw.TG.getD t.val [] ∈ CFSG.KD.Fi23Tw.TG := by
    rw [List.getD_eq_getElem _ _ (TG_len ▸ ht6)]
    exact List.getElem_mem _
  obtain ⟨-, hg1, hg2, hg3⟩ := tgK_spec (allLL_spec (ch17340targ_ok : targ = true) _ hgm)
  have hg0 : (CFSG.KD.Fi23Tw.TG.getD t.val []).getD 0 0 = (cPt 4 t).val := by
    rw [tg_head ht6, cPt4_val]
  rw [hg0, x_acts] at hg1
  rw [← hg1, x_acts] at hg2
  obtain ⟨e, he, hc⟩ := cover c'.val c'.2
  obtain ⟨-, hlt, hfixT, hsep⟩ := repK_spec (rep_all e he)
  have hc' : c' = ⟨e.getD 0 0, hlt⟩ ∨ c' = t3 2 • ⟨e.getD 0 0, hlt⟩ ∨
      c' = t3 2 • t3 2 • ⟨e.getD 0 0, hlt⟩ := by
    rcases hc with h | h | h
    · exact Or.inl (Fin.ext h)
    · refine Or.inr (Or.inl (Fin.ext ?_))
      rw [h]
      exact x_acts ⟨e.getD 0 0, hlt⟩
    · refine Or.inr (Or.inr (Fin.ext ?_))
      rw [h]
      have e1 := x_acts ⟨e.getD 0 0, hlt⟩
      change wv G CFSG.KD.Fi23Tw.w2 (e.getD 0 0) = _ at e1
      rw [e1]
      exact x_acts _
  have hpr : ∀ a : Fin 31671, t3 2 • a = a →
      (ePt ⟨e.getD 0 0, hlt⟩ * ePt a = ePt a * ePt ⟨e.getD 0 0, hlt⟩ ↔
        ePt c' * ePt a = ePt a * ePt c') := by
    intro a ha
    rcases hc' with h | h | h
    · rw [h]
    · rw [h]
      exact (comm_x ha).symm
    · rw [h]
      exact ((comm_x ha).trans (comm_x ha)).symm
  have hr : (⟨e.getD 0 0, hlt⟩ : Fin 31671) = cPt 4 t ∨
      (⟨e.getD 0 0, hlt⟩ : Fin 31671) = t3 2 • cPt 4 t ∨
      (⟨e.getD 0 0, hlt⟩ : Fin 31671) = t3 2 • t3 2 • cPt 4 t := by
    rcases hsep _ hgm with h | h | h | ⟨a, ha, hne⟩
    · exact Or.inl (Fin.ext (h.trans hg0))
    · exact Or.inr (Or.inl (Fin.ext (h.trans hg1.symm)))
    · exact Or.inr (Or.inr (Fin.ext (h.trans hg2.symm)))
    · exfalso
      obtain ⟨halt, hwa⟩ := hfixT a ha
      have hx : t3 2 • (⟨a, halt⟩ : Fin 31671) = ⟨a, halt⟩ :=
        Fin.ext ((x_acts ⟨a, halt⟩).symm.trans hwa)
      have hbit := hg3 a ((fix_iff ⟨a, halt⟩).1 hx)
      rw [hg0] at hbit
      apply hne
      rw [hbit]
      refine Bool.eq_iff_iff.2 ((cmK_iff halt hlt).trans ?_)
      refine ((hpr ⟨a, halt⟩ hx).trans ((hprof ⟨a, halt⟩ hx).trans ?_))
      exact (cmK_iff halt (cPt 4 t).2).symm
  have h3 := x_cube (cPt 4 t)
  have h4 := x_cube (t3 2 • cPt 4 t)
  rcases hc' with h1 | h1 | h1 <;> rcases hr with h2 | h2 | h2 <;> rw [h1, h2] <;>
    simp only [h3, h4, true_or, or_true]

theorem fi23C_ok : fi23COK orb = true := by
  have hT : Rep 31671 ((t3Tabs orb (chainLetters orb))[2]!) (t3 2) := rep_t3Tabs 2
  have h : twinCheck orb (dTable orb) (genTables orb (-2)) ((t3Tabs orb (chainLetters orb))[2]!)
      4 = true := twinCheck_of hT hK1 hK2 hK2b hK3 hK4
  exact h

end CertificateChecks.KernelFi23Tw

end
