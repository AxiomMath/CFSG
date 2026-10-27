module

public import Certificates.Kernel.ThU.Checks
public import CFSG.Certificates.Kernel.ThU.Sound
public import CFSG.Certificates.Kernel.Th.Checks2.Seed_S
public import CFSG.Certificates.Kernel.Th.Checks2.Sm_C

public section

set_option maxRecDepth 100000

namespace CFSG.KD.ThU

open CFSG.KC.Th CFSG.KC.Th.BigS CFSG.KC.Th.Spec CFSG.KC.ThU CFSG.KC.Th.Spec.SylowOrbit
  CFSG.KC.Th.Spec.SylowPc CFSG.KC.Th.Spec.FwdRel
open CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.Coordinator

theorem pk_seedA : pkMat CFSG.KD.ThSeed.SA =
    CFSG.Blueprint.NativeSporadic.decode 2 248 1 thULocal3.seedA := by
  rw [pkMat_seed CFSG.KD.ThSeed.dA, ← CFSG.KD.ThSeed.LA_eq, CFSG.Sporadic.Th.seedA_eq]
  rfl

theorem pk_seedB : pkMat CFSG.KD.ThSeed.SB =
    CFSG.Blueprint.NativeSporadic.decode 2 248 1 thULocal3.seedB := by
  rw [pkMat_seed CFSG.KD.ThSeed.dB, ← CFSG.KD.ThSeed.LB_eq, CFSG.Sporadic.Th.seedB_eq]
  rfl

theorem blockAt_spec {b : ℕ} (h : blockAt b = true) :
    BlockOK RB CFSG.KD.ThS.rm PR 12 (blocks.getD b (0, 0, 0, 0)).2.2.2 BL b ∧
      blkFr BL b = (blocks.getD b (0, 0, 0, 0)).2.1 ∧
      blkTo BL b = (blocks.getD b (0, 0, 0, 0)).2.2.1 := by
  obtain ⟨h0, h1⟩ := CFSG.KC.Th.Spec.Dce.andB_iff.1 h
  obtain ⟨h1, h2⟩ := CFSG.KC.Th.Spec.Dce.andB_iff.1 h1
  have e0 : blkFr BL b = (blocks.getD b (0, 0, 0, 0)).2.1 := Nat.eq_of_beq_eq_true h0
  have e1 : blkTo BL b = (blocks.getD b (0, 0, 0, 0)).2.2.1 := Nat.eq_of_beq_eq_true h1
  exact ⟨blockOK_of e0 e1 h2, e0, e1⟩

theorem pc_bound (J : Subgroup (GL (Fin 248) (ZMod 2)))
    (hR : ∀ k < 12, RegIn (⊤ : Subgroup J) RB (regAt PR k)) :
    236196 ≤ Nat.card (pcSub J RB PR 0 12) := by
  have hb : ∀ b < 9, blockAt b = true := fun b hb =>
    List.all_eq_true.1 chk_blocks b (List.mem_range.2 hb)
  let f : ℕ → ℕ := fun b => if b < 9 then (blocks.getD b (0, 0, 0, 0)).2.1 else 12
  let P : ℕ → ℕ := fun b => (blocks.getD b (0, 0, 0, 0)).2.2.2
  have hstep : ∀ b < 9, P b ^ (f (b + 1) - f b) * Nat.card (pcSub J RB PR (f (b + 1)) 12) ≤
      Nat.card (pcSub J RB PR (f b) 12) := by
    intro b hb9
    obtain ⟨hok, efr, eto⟩ := blockAt_spec (hb b hb9)
    have hfb : f b = blkFr BL b := by simp only [f, if_pos hb9, efr]
    have hfb1 : f (b + 1) = blkTo BL b := by
      rw [eto]
      interval_cases b <;> rfl
    rw [hfb, hfb1]
    refine block_le CFSG.KD.ThS.k0 hR ?_ ?_ hok
    · rw [efr, eto]
      interval_cases b <;> decide
    · rw [eto]
      interval_cases b <;> decide
  have h := chain_le f P 9 rfl rfl hstep
  have e : (∏ b ∈ Finset.range 9, P b ^ (f (b + 1) - f b)) = 236196 := by decide
  rw [e] at h
  exact h

theorem thU_sub : ∃ g : Fin 3 → (CFSG.Blueprint.NativeSporadic.seedMonoid 2 248 1
      thULocal3.seedA thULocal3.seedB)ˣ,
    (∀ r ∈ thULocal3.rels, FreeGroup.lift g (FreeGroup.mk r) = 1) ∧
    (∀ i, g i ^ thULocal3.ords.getD i 0 = 1) ∧
    thULocal3.n ≤ Nat.card (Subgroup.closure (Set.range g)) := by
  have hk := CFSG.KD.ThS.k0
  set S := CFSG.Blueprint.NativeSporadic.seedMonoid 2 248 1 thULocal3.seedA thULocal3.seedB
    with hS
  have hAm : CFSG.Blueprint.NativeSporadic.decode 2 248 1 thULocal3.seedA ∈ S :=
    Submonoid.subset_closure (Set.mem_insert _ _)
  have hBm : CFSG.Blueprint.NativeSporadic.decode 2 248 1 thULocal3.seedB ∈ S :=
    Submonoid.subset_closure (Set.mem_insert_of_mem _ rfl)
  have hAA : CFSG.Blueprint.NativeSporadic.decode 2 248 1 thULocal3.seedA *
      CFSG.Blueprint.NativeSporadic.decode 2 248 1 thULocal3.seedA = 1 := by
    rw [← pk_seedA, ← pkMat_mulB hk, Nat.eq_of_beq_eq_true CFSG.KD.ThSeed.aa, pkMat_one hk]
  have hBBB : CFSG.Blueprint.NativeSporadic.decode 2 248 1 thULocal3.seedB *
      CFSG.Blueprint.NativeSporadic.decode 2 248 1 thULocal3.seedB *
      CFSG.Blueprint.NativeSporadic.decode 2 248 1 thULocal3.seedB = 1 := by
    rw [← pk_seedB, ← pkMat_mulB hk, ← pkMat_mulB hk, Nat.eq_of_beq_eq_true CFSG.KD.ThSeed.bbb,
      pkMat_one hk]
  obtain ⟨a, b, ha, hb⟩ := seed_units S hAm hBm hAA hBBB
  have es1 := Nat.eq_of_beq_eq_true chk_s1
  have es2 := Nat.eq_of_beq_eq_true chk_s2
  obtain ⟨hn1, hn⟩ := CFSG.KC.Th.Spec.Dce.andB_iff.1 chk_n
  obtain ⟨hn2, hn3⟩ := CFSG.KC.Th.Spec.Dce.andB_iff.1 hn
  have hn1' : 3 < n1 := Nat.blt_eq.mp hn1
  have hpos1 : 0 < runSlp RB CFSG.KD.ThS.c CFSG.KD.ThS.rm CFSG.KD.ThS.ONE slp1.c0 3 := by
    rw [es1]
    omega
  have hreg := regs_exist (unitsHom S) hk a b
    (by rw [ha, Nat.eq_of_beq_eq_true chk_A, pk_seedA])
    (by rw [hb, Nat.eq_of_beq_eq_true chk_B, pk_seedB]) hpos1
  have hgr := regsIn_spec chk_gr
  have hex : ∀ i : Fin 3, ∃ u : Sˣ, unitsHom S u = pkMat (RB (regAt GR i.val)) := fun i =>
    hreg _ (hgr i.val i.isLt).1 (by rw [es1]; exact (hgr i.val i.isLt).2)
  choose x hx using hex
  have hsq : ∀ i : Fin 3, x i ^ 2 = 1 := by
    intro i
    apply unitsHom_injective S
    have h := List.all_eq_true.1 chk_sq i.val (List.mem_range.2 i.isLt)
    rw [map_pow, map_one, hx, sq, ← pkMat_mulB hk, Nat.eq_of_beq_eq_true h, pkMat_one hk]
  refine ⟨x, fun r hr => ?_, fun i => ?_, ?_⟩
  · exact lift_eq_one_of_relOKR hk (unitsHom_injective S) x hx
      (List.all_eq_true.1 chk_rels r hr)
  · have e : thULocal3.ords.getD i.val 0 = 2 := by
      fin_cases i <;> rfl
    rw [e]
    exact hsq i
  · have hpos2 : 0 < runSlp RB CFSG.KD.ThS.c CFSG.KD.ThS.rm CFSG.KD.ThS.ONE slp2.c0 n1 := by
      rw [es2]
      exact Nat.blt_eq.mp hn2
    have hlt2 : runSlp RB CFSG.KD.ThS.c CFSG.KD.ThS.rm CFSG.KD.ThS.ONE slp2.c0 n1 < 2048 := by
      rw [es2]
      exact Nat.blt_eq.mp hn3
    have hall : allMarked PR 12 (runMarked slp2.c0 (n1 + 2048 * gmask3 GR) / 2048) = true := by
      rw [← Nat.eq_of_beq_eq_true chk_M]
      exact chk_mk
    haveI := unitsHom_finite S
    exact le_card_closure_of_chain hk (unitsHom_injective S) x hx hpos2 hlt2 hall pc_bound

end CFSG.KD.ThU

end
