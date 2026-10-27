
module

public import Certificates.Kernel.P0Orb.RepA
public import Certificates.Kernel.P0Orb.RepB
public import Certificates.Kernel.P0Orb.RepC
public import Certificates.Kernel.P0Orb.TabOK
public import Certificates.Kernel.P0Orb.TabEq
public import Certificates.Kernel.P0Vis.TabOK
public import Certificates.Kernel.P0Vis.TabEq
public import Certificates.Kernel.P0Vis.Facts
public import Certificates.Kernel.P0Vis.VisA
public import Certificates.Kernel.P0Vis.VisB
public import Certificates.Kernel.P0Vis.Gaps
public import Certificates.Kernel.P0Vis.Bd
public import CFSG.Certificates.Kernel.P0RankK.VisBound
public import CFSG.Certificates.Kernel.P0RankK.Lift
public import CFSG.Certificates.Kernel.P0RankK.QPres
public import CFSG.Certificates.Kernel.P0RankK.AssemBits
public import CFSG.Certificates.Kernel.Common.ForallChunks
import Mathlib.Tactic.NormNum
public import CFSG.Certificates.Kernel.P0RankK.VisGlue
public import CFSG.Monster.B.TwoA.Sp8.P0RankSound

public noncomputable section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

attribute [local instance low] Classical.propDecidable

namespace CFSG.KD.P0Vis

open CFSG.KC.P0Orb CFSG.KC.P0Vis CFSG.KD.P0Orb
open MonsterB.P0Rank CFSG.Monster.B.TwoA.Sp8.P0Rank
open CFSG.Monster.B.TwoA.Sp8.WordRel CFSG.Monster.B.TwoA.Sp8 CFSG.Monster.B.TwoA CFSG.Open

#kc_forall_chunks atAll812462 (fun t => atOK AT GC t = true) 10 CFSG.KD.P0Orb.at812462t 1
#kc_forall_chunks btAll812462 (fun t => btOK BT BG t = true) 10 CFSG.KD.P0Vis.bt812462t 1
#kc_forall_chunks faAll812462 (fun o => faOK FA AT RT o = true) 68 CFSG.KD.P0Vis.fa812462o 1
#kc_forall_chunks fbAll812462 (fun z => fbOK FB BT z = true) 32 CFSG.KD.P0Vis.fb812462z 1
#kc_forall_chunks fcAll812462 (fun i => factsOK i = true) 59 CFSG.KD.P0Vis.fc812462_ 1
#kc_forall_chunks r0All812462 (fun i => grpOK AT RT BC BU 0 8 CFSG.KD.P0OrbR0.rows i = true) 1
  CFSG.KD.P0OrbR0.ch812462r0_ 1
#kc_forall_chunks r1All812462 (fun i => grpOK AT RT BC BU 1 8 CFSG.KD.P0OrbR1.rows i = true) 75
  CFSG.KD.P0OrbR1.ch812462r1_ 1
#kc_forall_chunks r2All812462 (fun i => grpOK AT RT BC BU 600 8 CFSG.KD.P0OrbR2.rows i = true)
  75 CFSG.KD.P0OrbR2.ch812462r2_ 1
#kc_forall_chunks r3All812462 (fun i => grpOK AT RT BC BU 1200 8 CFSG.KD.P0OrbR3.rows i = true)
  75 CFSG.KD.P0OrbR3.ch812462r3_ 1
#kc_forall_chunks r4All812462 (fun i => grpOK AT RT BC BU 1800 8 CFSG.KD.P0OrbR4.rows i = true)
  75 CFSG.KD.P0OrbR4.ch812462r4_ 1
#kc_forall_chunks r5All812462 (fun i => grpOK AT RT BC BU 2400 8 CFSG.KD.P0OrbR5.rows i = true)
  75 CFSG.KD.P0OrbR5.ch812462r5_ 1
#kc_forall_chunks r6All812462 (fun i => grpOK AT RT BC BU 3000 8 CFSG.KD.P0OrbR6.rows i = true)
  75 CFSG.KD.P0OrbR6.ch812462r6_ 1
#kc_forall_chunks r7All812462 (fun i => grpOK AT RT BC BU 3600 8 CFSG.KD.P0OrbR7.rows i = true)
  75 CFSG.KD.P0OrbR7.ch812462r7_ 1
#kc_forall_chunks r8All812462 (fun i => grpOK AT RT BC BU 4200 8 CFSG.KD.P0OrbR8.rows i = true)
  86 CFSG.KD.P0OrbR8.ch812462r8_ 1
#kc_forall_chunks v0All812462
  (fun i => vgrpOK ⟨AT, BT, BC, FK, FC⟩ RT FA YG 0 16 CFSG.KD.P0VisR0.rows i = true) 75
  CFSG.KD.P0VisR0.ch812462v0_ 1
#kc_forall_chunks v1All812462
  (fun i => vgrpOK ⟨AT, BT, BC, FK, FC⟩ RT FA YG 1200 16 CFSG.KD.P0VisR1.rows i = true) 75
  CFSG.KD.P0VisR1.ch812462v1_ 1
#kc_forall_chunks v2All812462
  (fun i => vgrpOK ⟨AT, BT, BC, FK, FC⟩ RT FA YG 2400 16 CFSG.KD.P0VisR2.rows i = true) 75
  CFSG.KD.P0VisR2.ch812462v2_ 1
#kc_forall_chunks v3All812462
  (fun i => vgrpOK ⟨AT, BT, BC, FK, FC⟩ RT FA YG 3600 16 CFSG.KD.P0VisR3.rows i = true) 81
  CFSG.KD.P0VisR3.ch812462v3_ 1

theorem repAll812462 : ∀ r < 4887, ∃ row, repOK AT RT BC BU r row = true := by
  have hfile : ∀ (rows : List Row) (lo n : ℕ), (∀ i < n, grpOK AT RT BC BU lo 8 rows i = true) →
      rows.length ≤ 8 * n → ∀ r, lo ≤ r → r < lo + rows.length →
        ∃ row, repOK AT RT BC BU r row = true := by
    intro rows lo n hck hlen r h1 h2
    have := chunks_all (repsOK AT RT BC BU) (fun r row => repOK AT RT BC BU r row = true)
      (fun rows r₀ h t ht => repsOK_spec rows r₀ h t ht) (by norm_num) hck hlen (r - lo)
      (by omega)
    exact ⟨_, by rwa [Nat.add_sub_cancel' h1] at this⟩
  have hl := lens
  simp only [Bool.and_eq_true, Nat.beq_eq] at hl
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨l0, l1⟩, l2⟩, l3⟩, l4⟩, l5⟩, l6⟩, l7⟩, l8⟩ := hl
  intro r hr
  by_cases h0 : r < 1
  · exact hfile _ 0 1 r0All812462 (by omega) r (by omega) (by omega)
  by_cases h1 : r < 600
  · exact hfile _ 1 75 r1All812462 (by omega) r (by omega) (by omega)
  by_cases h2 : r < 1200
  · exact hfile _ 600 75 r2All812462 (by omega) r (by omega) (by omega)
  by_cases h3 : r < 1800
  · exact hfile _ 1200 75 r3All812462 (by omega) r (by omega) (by omega)
  by_cases h4 : r < 2400
  · exact hfile _ 1800 75 r4All812462 (by omega) r (by omega) (by omega)
  by_cases h5 : r < 3000
  · exact hfile _ 2400 75 r5All812462 (by omega) r (by omega) (by omega)
  by_cases h6 : r < 3600
  · exact hfile _ 3000 75 r6All812462 (by omega) r (by omega) (by omega)
  by_cases h7 : r < 4200
  · exact hfile _ 3600 75 r7All812462 (by omega) r (by omega) (by omega)
  · exact hfile _ 4200 86 r8All812462 (by omega) r (by omega) (by omega)

theorem visAll812462 : ∀ r < 4887, ∃ row, visitOK ⟨AT, BT, BC, FK, FC⟩ RT FA YG r row = true ∧
    ∀ c ∈ row.2, c.1.length ≤ 16 := by
  have hfile : ∀ (rows : List VRow) (lo n : ℕ),
      (∀ i < n, vgrpOK ⟨AT, BT, BC, FK, FC⟩ RT FA YG lo 16 rows i = true) → glenOK rows = true →
      rows.length ≤ 16 * n → ∀ r, lo ≤ r → r < lo + rows.length →
        ∃ row, visitOK ⟨AT, BT, BC, FK, FC⟩ RT FA YG r row = true ∧
          ∀ c ∈ row.2, c.1.length ≤ 16 := by
    intro rows lo n hck hgl hlen r h1 h2
    have := chunks_all (visitsOK ⟨AT, BT, BC, FK, FC⟩ RT FA YG)
      (fun r row => visitOK ⟨AT, BT, BC, FK, FC⟩ RT FA YG r row = true)
      (fun rows r₀ h t ht => visitsOK_spec rows r₀ h t ht) (by norm_num) hck hlen (r - lo)
      (by omega)
    rw [Nat.add_sub_cancel' h1] at this
    exact ⟨_, this, glenOK_spec hgl _ (List.getElem_mem _)⟩
  have hl := vlens
  simp only [Bool.and_eq_true, Nat.beq_eq] at hl
  obtain ⟨⟨⟨l0, l1⟩, l2⟩, l3⟩ := hl
  intro r hr
  by_cases h0 : r < 1200
  · exact hfile _ 0 75 v0All812462 glen812462_0 (by omega) r (by omega) (by omega)
  by_cases h1 : r < 2400
  · exact hfile _ 1200 75 v1All812462 glen812462_1 (by omega) r (by omega) (by omega)
  by_cases h2 : r < 3600
  · exact hfile _ 2400 75 v2All812462 glen812462_2 (by omega) r (by omega) (by omega)
  · exact hfile _ 3600 81 v3All812462 glen812462_3 (by omega) r (by omega) (by omega)

theorem card_le_P0_kernel :
    ∀ E : Subgroup Dfull, E ≤ PLam lam0 → IsElemAbelian 2 E → Nat.card E ≤ 2 ^ 14 := by
  intro E hE hEA
  have hGC : ∀ cs ∈ p0Data.aCols, ∀ c ∈ cs, c < 2 ^ 16 := by decide
  have hBG : ∀ cs ∈ p0Data.uConjT, ∀ c ∈ cs, c < 2 ^ 9 := by decide
  have hAT : ∀ κ < 2 ^ 10, ∀ x < 2 ^ 16, CFSG.KC.P0Orb.aAct AT κ x = actK p0Data.aCols κ x := by
    have h := aAct_eq_actK at0 atAll812462 (by rw [gc_eq]; exact hGC)
    rw [gc_eq] at h
    exact h
  have hBT : ∀ κ < 2 ^ 10, ∀ x < 2 ^ 9, CFSG.KC.P0Vis.bAct BT κ x = actK p0Data.uConjT κ x := by
    have h := bAct_eq_actK bt0 btAll812462 (by rw [bg_eq]; exact hBG)
    rw [bg_eq] at h
    exact h
  have hbc := bcOK_sound bc
  rw [beta_eq] at hbc
  have hβ : ∀ x < 2 ^ 16, ∀ y < 2 ^ 16, bet BC x y = betaN p0Data.beta x y := hbc.1
  have hq : ∀ x < 2 ^ 16, qf BU x = MonsterB.P0Rank.qN p0Data.beta x := hbc.2
  have hn := nums
  simp only [Bool.and_eq_true, Nat.beq_eq, Nat.blt_eq] at hn
  obtain ⟨⟨⟨⟨⟨⟨hNY, hNF⟩, hFK⟩, hFC⟩, -⟩, -⟩, -⟩ := hn
  have hfact : ∀ i < NF, factOK p0Data FK FC i = true := by
    intro i hi
    rw [hNF] at hi
    have hi6 : i / 6 < 59 := by omega
    have h := fcAll812462 (i / 6) hi6
    rw [factsOK, List.all_eq_true] at h
    have := h (i % 6) (List.mem_range.2 (Nat.mod_lt i (by norm_num)))
    rwa [Nat.div_add_mod] at this
  have hFCall := fc_all hfact hFK hFC fval0
  have hA0 : ∀ x < 2 ^ 16, CFSG.KC.P0Orb.aAct AT 0 x = x := fun x hx => by
    rw [hAT 0 (by norm_num) x hx, actK_zero_left]
  have hAlt : ∀ κ < 2 ^ 10, ∀ x < 2 ^ 16, CFSG.KC.P0Orb.aAct AT κ x < 2 ^ 16 := fun κ hκ x hx => by
    rw [hAT κ hκ x hx]
    exact actK_aCols_lt κ hx
  have hAc : ∀ κ < 2 ^ 10, ∀ μ < 2 ^ 10, ∀ x < 2 ^ 16,
      CFSG.KC.P0Orb.aAct AT κ (CFSG.KC.P0Orb.aAct AT μ x) = CFSG.KC.P0Orb.aAct AT (κ ^^^ μ) x := by
    intro κ hκ μ hμ x hx
    rw [hAT μ hμ x hx, hAT κ hκ _ (actK_aCols_lt μ hx), hAT _ (Nat.xor_lt_two_pow hκ hμ) x hx,
      actK_aCols_xor κ hκ μ hμ x hx]
  have hAlin : ∀ κ < 2 ^ 10, ∀ x < 2 ^ 16, ∀ y < 2 ^ 16,
      CFSG.KC.P0Orb.aAct AT κ (x ^^^ y) = CFSG.KC.P0Orb.aAct AT κ x ^^^ CFSG.KC.P0Orb.aAct AT κ y := by
    intro κ hκ x hx y hy
    rw [hAT κ hκ _ (Nat.xor_lt_two_pow hx hy), hAT κ hκ x hx, hAT κ hκ y hy, actK_xor]
  have hAq : ∀ κ < 2 ^ 10, ∀ x < 2 ^ 16, qf BU x = 0 → qf BU (CFSG.KC.P0Orb.aAct AT κ x) = 0 := by
    intro κ hκ x hx h0
    rw [hq _ (hAlt κ hκ x hx), hAT κ hκ x hx]
    exact qN_actK_eq_zero κ hx (by rw [← hq x hx]; exact h0)
  have hAβ : ∀ κ < 2 ^ 10, ∀ x < 2 ^ 16, ∀ y < 2 ^ 16,
      bet BC x y = 0 → bet BC (CFSG.KC.P0Orb.aAct AT κ x) (CFSG.KC.P0Orb.aAct AT κ y) = 0 := by
    intro κ hκ x hx y hy h0
    rw [hβ _ (hAlt κ hκ x hx) _ (hAlt κ hκ y hy), hAT κ hκ x hx, hAT κ hκ y hy]
    exact betaN_actK_eq_zero κ hx hy (by rw [← hβ x hx y hy]; exact h0)
  have hN : N = 4887 := n_eq
  have hrep : ∀ r < N, RepFacts AT RT BC BU N r := fun r hr => by
    obtain ⟨row, h⟩ := repAll812462 r (by omega)
    exact repOK_facts bc rt h
  have hslot0 : slot RT 0 = 0 := by
    have h := rt
    rw [rtOK, Bool.and_eq_true] at h
    exact Nat.eq_of_beq_eq_true h.1
  have hD16 : ∀ x ∈ layerD E, x < 2 ^ 16 := fun x hx =>
    Finset.mem_range.1 (Finset.mem_filter.1 hx).1
  have hDq : ∀ x ∈ layerD E, qf BU x = 0 := fun x hx => by
    rw [hq x (hD16 x hx)]
    exact qN_eq_zero_of_mem_layerD hEA x hx
  have hDb : ∀ x ∈ layerD E, ∀ y ∈ layerD E, bet BC x y = 0 := fun x hx y hy => by
    rw [hβ x (hD16 x hx) y (hD16 y hy)]
    exact betaN_eq_zero_of_mem_layerD hEA x hx y hy
  obtain ⟨lam, hlam, r, hr, himg⟩ := orbit_complete hrep hslot0 (by omega) hA0 hAc hAlt hAlin
    hAq hAβ _ (layerD E) rfl (xorClosed_layerD E) hD16 hDq hDb
  obtain ⟨E', hE', hE'A, hcard, hlayer⟩ := conj_layers hE hEA lam
  have hD' : layerD E' = spanF (sbasis (slot RT r)) := by
    rw [hlayer, ← himg]
    exact Finset.image_congr fun x hx => (hAT lam hlam x (hD16 x hx)).symm
  have hbsD : ∀ b ∈ sbasis (slot RT r), b ∈ layerD E' := fun b hb => by
    rw [hD']
    exact mem_spanF _ b hb
  rw [← hcard, natCard_eq_layers (show E' ≤ WordRel.P0 from hE'), hD']
  obtain ⟨row, hvis, hglen⟩ := visAll812462 r (by omega)
  exact visit_bound (C := ⟨AT, BT, BC, FK, FC⟩) hAT hBT actK_aCols_xor actK_uConjT_xor
    (fun κ x hx => actK_aCols_lt κ hx) hβ hFCall faAll812462 fbAll812462 yc yg
    (by rw [hNY]; norm_num) lamB lamS hvis hglen (hrep r hr).card (xorClosed_layerW E')
    (fun κ hκ => Finset.mem_range.1 (Finset.mem_filter.1 hκ).1)
    (fun κ hκ b hb => actK_eq_of_mem_layerW hE'A κ hκ b (hbsD b hb))
    (fun τ hτ => Finset.mem_range.1 (Finset.mem_filter.1 hτ).1)
    (actK_eq_of_mem_layerY hE'A)
    (fun ks hks => layer_liftPm bd hE'A _ ks hbsD hks)

end CFSG.KD.P0Vis
