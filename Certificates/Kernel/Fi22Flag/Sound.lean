module

public import Certificates.Kernel.Fi22Flag.ChkDefs
public import Certificates.Kernel.Fi22Syl.Final
public import CFSG.Sporadic.Fi22.Classes
import Certificates.Kernel.Fi22Flag.Checks
import Certificates.Kernel.Sporadic.ON.Gen
import CFSG.Certificates.Kernel.Spor.RawOrbEval
import Mathlib

public section

set_option maxRecDepth 400000

#kon_join CertificateChecks.KernelFi22Flag.c24671All CertificateChecks.KernelFi22Flag.c24671Sl 128

namespace CertificateChecks.KernelFi22Flag

open CFSG.KC.Enum CFSG.KS CFSG.KS.PEnum CFSG.KS.TBfs CFSG.KS.PC CFSG.KS.TW CFSG.KS.Fi22L
  CFSG.KS.Fi22S CFSG.KS.Fi22Cent CFSG.Sporadic.Fi22 CFSG.Sporadic.Fi22.Native CFSG.Sporadic.Th
  CFSG.Sporadic.Th.Native CFSG.Perm CFSG.Perm.Native CertificateChecks.KernelFi22S

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

theorem allFixL_of (F : Nat → Nat) : ∀ l : List Nat, (∀ q ∈ l, F q = q) →
    List.rec (motive := fun _ => Bool) true (fun q _ ih => bAnd(Nat.beq (F q) q, ih)) l = true
  | [], _ => rfl
  | a :: l, h => by
    change bAnd(Nat.beq (F a) a, List.rec (motive := fun _ => Bool) true
      (fun q _ ih => bAnd(Nat.beq (F q) q, ih)) l) = true
    rw [Raw.Orb.bAnd_eq, Bool.and_eq_true, Nat.beq_eq]
    exact ⟨h a List.mem_cons_self, allFixL_of F l fun q hq => h q (List.mem_cons_of_mem a hq)⟩

theorem allFixL_false (F : Nat → Nat) : ∀ l : List Nat, (∃ q ∈ l, F q ≠ q) →
    List.rec (motive := fun _ => Bool) true (fun q _ ih => bAnd(Nat.beq (F q) q, ih)) l = false
  | [], ⟨_, hq, _⟩ => absurd hq List.not_mem_nil
  | a :: l, ⟨q, hq, hne⟩ => by
    change bAnd(Nat.beq (F a) a, List.rec (motive := fun _ => Bool) true
      (fun q _ ih => bAnd(Nat.beq (F q) q, ih)) l) = false
    rw [Raw.Orb.bAnd_eq]
    by_cases e : F a = a
    · have hb : Nat.beq (F a) a = true := by rw [Nat.beq_eq]; exact e
      rw [hb, Bool.true_and]
      rcases List.mem_cons.1 hq with rfl | hq'
      · exact absurd e hne
      · exact allFixL_false F l ⟨q, hq', hne⟩
    · have hb : Nat.beq (F a) a = false := Bool.eq_false_iff.2 fun h => e (Nat.eq_of_beq_eq_true h)
      rw [hb, Bool.false_and]

theorem anyMvL_of (F : Nat → Nat) : ∀ l : List Nat, (∃ q ∈ l, F q ≠ q) →
    List.rec (motive := fun _ => Bool) false (fun q _ ih => bIf(Nat.beq (F q) q, ih, true)) l = true
  | [], ⟨_, hq, _⟩ => absurd hq List.not_mem_nil
  | a :: l, ⟨q, hq, hne⟩ => by
    change bIf(Nat.beq (F a) a, List.rec (motive := fun _ => Bool) false
      (fun q _ ih => bIf(Nat.beq (F q) q, ih, true)) l, true) = true
    rw [Raw.Orb.bIf_eq]
    by_cases e : F a = a
    · rw [if_pos (by rw [Nat.beq_eq]; exact e)]
      rcases List.mem_cons.1 hq with rfl | hq'
      · exact absurd e hne
      · exact anyMvL_of F l ⟨q, hq', hne⟩
    · rw [if_neg (fun h => e (Nat.eq_of_beq_eq_true h))]

theorem anyMvL_false (F : Nat → Nat) : ∀ l : List Nat, (∀ q ∈ l, F q = q) →
    List.rec (motive := fun _ => Bool) false (fun q _ ih => bIf(Nat.beq (F q) q, ih, true)) l = false
  | [], _ => rfl
  | a :: l, h => by
    change bIf(Nat.beq (F a) a, List.rec (motive := fun _ => Bool) false
      (fun q _ ih => bIf(Nat.beq (F q) q, ih, true)) l, true) = false
    rw [Raw.Orb.bIf_eq, if_pos (by rw [Nat.beq_eq]; exact h a List.mem_cons_self)]
    exact anyMvL_false F l fun q hq => h q (List.mem_cons_of_mem a hq)

theorem allFix_of {F : Nat → Nat} (h : ∀ q ∈ QL, F q = q) : allFix F = true := allFixL_of F QL h

theorem allFix_false {F : Nat → Nat} (h : ∃ q ∈ QL, F q ≠ q) : allFix F = false :=
  allFixL_false F QL h

theorem anyMv_of {F : Nat → Nat} (h : ∃ q ∈ QL, F q ≠ q) : anyMv F = true := anyMvL_of F QL h

theorem anyMv_false {F : Nat → Nat} (h : ∀ q ∈ QL, F q = q) : anyMv F = false :=
  anyMvL_false F QL h

theorem memL_spec (c : Nat) : ∀ L : List Nat,
    List.rec (motive := fun _ => Bool) false (fun f _ ih => bIf(Nat.beq f c, true, ih)) L = true →
      c ∈ L
  | [], h => absurd h Bool.false_ne_true
  | a :: L, h => by
    change bIf(Nat.beq a c, true, List.rec (motive := fun _ => Bool) false
      (fun f _ ih => bIf(Nat.beq f c, true, ih)) L) = true at h
    rw [Raw.Orb.bIf_eq] at h
    by_cases e : a = c
    · rw [← e]
      exact List.mem_cons_self
    · rw [if_neg (fun h => e (Nat.eq_of_beq_eq_true h))] at h
      exact List.mem_cons_of_mem a (memL_spec c L h)

theorem mem_of_check {k j : Nat} (hk : k < 1024) (hj : j < 128) (hf : c24671flag k j = true) :
    128 * k + j ∈ c24671F := by
  have hs : k / 8 < 128 := by omega
  have h := c24671All (k / 8) hs
  unfold c24671Sl at h
  have h' := Raw.Orb.allN_iff.1 h (k % 8) (Nat.mod_lt _ (by norm_num))
  rw [Raw.Orb.strictB_eq] at h'
  have e : Nat.add (Nat.mul (k / 8) 8) (k % 8) = k := Nat.div_add_mod' k 8
  rw [e] at h'
  have h2 := Raw.Orb.allN_iff.1 h' j hj
  beta_reduce at h2
  rw [Raw.Orb.bIf_eq, hf] at h2
  have e2 : Nat.add (Nat.mul k 128) j = 128 * k + j := by
    change k * 128 + j = 128 * k + j
    omega
  by_cases hm : c24671mem (Nat.add (Nat.mul k 128) j) = true
  · rw [← e2]
    exact memL_spec _ c24671F hm
  · rw [if_neg hm] at h2
    exact absurd h2 (by decide)

theorem tabS_eq (i : ℕ) : tabS i = KernelFi22S.tabK i := by
  change treeTabs 3510 (chainTrees 3510 (sylLetters (chainLetters orb)) sylBase)[i]!
      (sylLetters (chainLetters orb)) =
    treeTabs 3510 (chainTrees 3510 (sylLetters (chainLetters orbL)) sylBase)[i]!
      (sylLetters (chainLetters orbL))
  rw [CertificateChecks.KernelFi22S.orb_eq]

theorem leaf_idx {k j : ℕ} (hk : k < 1024) (hj : j < 128) : ∀ y < 3510,
    idx 3510 (treeG TS[0]! (pairG sylG) k * treeG TS[1]! (pairG sylG) j) y = gK k j y := by
  obtain ⟨c0, c1⟩ := cnts
  have hk' : k < TS[0]!.pts.size := by rw [TS_size (l := 0) rfl]; exact hk
  have hj' : j < TS[1]!.pts.size := by rw [TS_size (l := 1) rfl]; exact hj
  intro y hy
  have r1 := rep_tabS (i := 1) (by rw [sylBase_size]; norm_num) hj' y hy
  have t1 := (tab_TR (i := 1) (by norm_num) (by rw [c1]; exact hj)).2 y hy
  rw [tabS_eq] at r1
  have r0 := rep_tabS (i := 0) (by rw [sylBase_size]; norm_num) hk' _ t1.2
  have t0 := (tab_TR (i := 0) (by norm_num) (by rw [c0]; exact hk)).2 _ t1.2
  rw [tabS_eq] at r0
  rw [idx_mul, ← r1, t1.1, ← r0, t0.1]
  unfold gK
  rw [Raw.Orb.strictN_eq]

theorem conj_elt {w : ℕ} (hw : w < 2) :
    ∃ c : J, ∀ y < 3510, wF w y = idx 3510 c y ∧ wI w y = idx 3510 c⁻¹ y := by
  obtain ⟨T1, T2⟩ := conj_TR hw
  have hmem : (conjTabs orbL)[w]'(by rw [conj_size]; exact hw) ∈ conjTabs orb := by
    rw [CertificateChecks.KernelFi22S.orb_eq]
    exact Array.getElem_mem _
  obtain ⟨c, hc1, hc2⟩ := rep_conjTabs hmem
  exact ⟨c, fun y hy => ⟨(T1.2 y hy).1.symm.trans (hc1 y hy), (T2.2 y hy).1.symm.trans (hc2 y hy)⟩⟩

theorem one_of_QL {g : J} (hg : ∀ q ∈ QL, idx 3510 g q = q) : g = 1 :=
  sep g fun t ht => by
    have hm : chainQ[t]! ∈ QL := by
      rw [← chain_hyp.chk.1, getElem!_pos chainQ t ht]
      exact Array.getElem_mem_toList ht
    exact hg _ hm

theorem flag_of_mem_D {k j : ℕ} (hk : k < 1024) (hj : j < 128) {x : J}
    (hx : ∀ y < 3510, idx 3510 x y = gK k j y) (hxD : x ∈ D) : c24671flag k j = true := by
  have hx2 : x * x = 1 := by rw [← pow_two, ← orderOf_of_mem_D hxD, pow_orderOf_eq_one]
  have hx1 : x ≠ 1 := by
    intro h
    have := orderOf_of_mem_D hxD
    rw [h, orderOf_one] at this
    exact absurd this (by norm_num)
  have hG : ∀ y < 3510, gK k j y = idx 3510 x y := fun y hy => (hx y hy).symm
  have hsq : ∀ q ∈ QL, KernelFi22S.sq (gK k j) q = q := fun q hq => by
    have hq' := QL_lt q hq
    unfold KernelFi22S.sq
    rw [Raw.Orb.strictN_eq, hG q hq', hG _ (idx_lt x hq'), ← idx_mul, hx2, idx_one]
  have hmv : ∃ q ∈ QL, gK k j q ≠ q := by
    by_contra hc
    refine hx1 (one_of_QL fun q hq => ?_)
    rw [← hG q (QL_lt q hq)]
    by_contra hne
    exact hc ⟨q, hq, hne⟩
  have hno : ∀ w < 2, conjK (gK k j) w = false := by
    intro w hw
    obtain ⟨c, hc⟩ := conj_elt hw
    have hr : ∀ y < 3510, rK (gK k j) w y = idx 3510 (x * (c * x * c⁻¹)) y := by
      intro y hy
      have l1 := idx_lt c⁻¹ hy
      have l2 := idx_lt x l1
      have l3 := idx_lt c l2
      unfold rK
      simp only [Raw.Orb.strictN_eq]
      rw [(hc y hy).2, hG _ l1, (hc _ l2).1, hG _ l3]
      simp only [idx_mul]
    have hrD : c * x * c⁻¹ ∈ D := (hxD : IsConj a x).trans (isConj_iff.2 ⟨c, rfl⟩)
    have hord := orderOf_mul_mem_D hxD hrD
    unfold conjK
    rw [Raw.Orb.bAnd_eq, Raw.Orb.bAnd_eq]
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hord
    rcases hord with h1 | h2 | h3
    · have e := orderOf_eq_one_iff.1 h1
      have hf : anyMv (rK (gK k j) w) = false := anyMv_false fun q hq => by
        rw [hr q (QL_lt q hq), e, idx_one]
      rw [hf, Bool.false_and]
    · have e := pow_orderOf_eq_one (x * (c * x * c⁻¹))
      rw [h2, pow_two] at e
      have hf : anyMv (KernelFi22S.sq (rK (gK k j) w)) = false := anyMv_false fun q hq => by
        have hq' := QL_lt q hq
        unfold KernelFi22S.sq
        rw [Raw.Orb.strictN_eq, hr q hq', hr _ (idx_lt _ hq'), ← idx_mul, e, idx_one]
      rw [hf, Bool.false_and, Bool.and_false]
    · have e := pow_orderOf_eq_one (x * (c * x * c⁻¹))
      rw [h3, pow_three'] at e
      have hf : anyMv (cb (rK (gK k j) w)) = false := anyMv_false fun q hq => by
        have hq' := QL_lt q hq
        unfold cb
        simp only [Raw.Orb.strictN_eq]
        rw [hr q hq', hr _ (idx_lt _ hq'), hr _ (idx_lt _ (idx_lt _ hq')), ← idx_mul, ← idx_mul,
          e, idx_one]
      rw [hf, Bool.and_false, Bool.and_false]
  have hl := leafK_of hk hj
  unfold leafK leafF at hl
  rw [Raw.Orb.bIf_eq, if_neg (by rw [anyMv_false hsq]; exact Bool.false_ne_true), Raw.Orb.bIf_eq,
    if_neg (by rw [allFix_false hmv]; exact Bool.false_ne_true), Raw.Orb.bIf_eq] at hl
  have hcube : allFix (cb fun x => strictN (gA x) (gK k j)) = true := by
    by_contra hc
    rw [if_neg hc, Raw.Orb.bIf_eq, hno 0 (by norm_num), if_neg Bool.false_ne_true,
      hno 1 (by norm_num)] at hl
    exact Bool.false_ne_true hl
  unfold c24671flag c24671flagF
  rw [Raw.Orb.bAnd_eq, Raw.Orb.bAnd_eq, allFix_of hsq, anyMv_of hmv, hcube]
  try rfl

theorem card_D_slvl_le : Nat.card {x : J // x ∈ D ∧ x ∈ slvl 0} ≤ 22 := by
  have key : ∀ x : {x : J // x ∈ D ∧ x ∈ slvl 0}, ∃ k j : ℕ, k < 1024 ∧ j < 128 ∧
      128 * k + j ∈ c24671F ∧
        (x : J) = treeG TS[0]! (pairG sylG) k * treeG TS[1]! (pairG sylG) j := by
    rintro ⟨x, hxD, hx⟩
    obtain ⟨k0, hk0, h, hh, rfl⟩ :=
      exists_tree_mul (i := 0) (by rw [sylBase_size]; norm_num) hx
    obtain ⟨k1, hk1, h', hh', rfl⟩ :=
      exists_tree_mul (i := 1) (by rw [sylBase_size]; norm_num) hh
    have hh'' : h' ∈ slvl 2 := hh'
    rw [slvl_two, Subgroup.mem_bot] at hh''
    have e : ∀ t0 t1 h' : J, h' = 1 → t0 * (t1 * h') = t0 * t1 := by
      intro t0 t1 h' h
      rw [h, mul_one]
    have hxe := e (treeG TS[0]! (pairG sylG) k0) (treeG TS[1]! (pairG sylG) k1) h' hh''
    rw [hxe] at hxD
    rw [TS_size (l := 0) rfl] at hk0
    rw [TS_size (l := 1) rfl] at hk1
    exact ⟨k0, k1, hk0, hk1, mem_of_check hk0 hk1 (flag_of_mem_D hk0 hk1 (leaf_idx hk0 hk1) hxD),
      hxe⟩
  choose k j hk hj hmem hx using key
  let f : {x : J // x ∈ D ∧ x ∈ slvl 0} → ↥c24671F.toFinset :=
    fun x => ⟨128 * k x + j x, List.mem_toFinset.2 (hmem x)⟩
  have hinj : Function.Injective f := by
    intro x y hxy
    have e : 128 * k x + j x = 128 * k y + j y := congrArg Subtype.val hxy
    have hjx := hj x
    have hjy := hj y
    have ek : k x = k y := by omega
    have ej : j x = j y := by omega
    apply Subtype.ext
    rw [hx x, hx y, ek, ej]
  have := Nat.card_le_card_of_injective f hinj
  rw [Nat.card_eq_finsetCard] at this
  exact this.trans ((List.toFinset_card_le _).trans (by decide))

open scoped Pointwise in
theorem exists_conj_into_slvl (S : Sylow 2 J) : ∃ g : J, ∀ x ∈ (S : Subgroup J), g * x * g⁻¹ ∈ slvl 0 := by
  have hT : IsPGroup 2 (slvl 0) := IsPGroup.of_card (n := 17) (by rw [card_slvl_zero]; norm_num)
  have hidx : ¬ 2 ∣ (slvl 0).index := by rw [slvl_index]; decide
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq J S (hT.toSylow hidx)
  refine ⟨g, fun x hx => ?_⟩
  have h1 : MulAut.conj g • x ∈ MulAut.conj g • (S : Subgroup J) :=
    Subgroup.smul_mem_pointwise_smul x _ _ hx
  rw [← Sylow.coe_subgroup_smul, hg, IsPGroup.toSylow_coe, MulAut.smul_def,
    MulAut.conj_apply] at h1
  exact h1

theorem card_D_sylow_le (S : Sylow 2 J) : Nat.card {x : J // x ∈ D ∧ x ∈ (S : Subgroup J)} ≤ 22 := by
  obtain ⟨g, hg⟩ := exists_conj_into_slvl S
  have hconj : ∀ x : J, x ∈ D → g * x * g⁻¹ ∈ D := fun x hx =>
    (hx : IsConj a x).trans (isConj_iff.2 ⟨g, rfl⟩)
  let f : {x : J // x ∈ D ∧ x ∈ (S : Subgroup J)} → {x : J // x ∈ D ∧ x ∈ slvl 0} :=
    fun x => ⟨g * x * g⁻¹, hconj x x.2.1, hg x x.2.2⟩
  have hinj : Function.Injective f := by
    intro x y hxy
    have h : g * (x : J) * g⁻¹ = g * (y : J) * g⁻¹ := by
      have := congrArg Subtype.val hxy
      exact this
    apply Subtype.ext
    calc (x : J) = g⁻¹ * (g * (x : J) * g⁻¹) * g := by group
      _ = g⁻¹ * (g * (y : J) * g⁻¹) * g := by rw [h]
      _ = (y : J) := by group
  exact (Nat.card_le_card_of_injective _ hinj).trans card_D_slvl_le

end CertificateChecks.KernelFi22Flag

end
