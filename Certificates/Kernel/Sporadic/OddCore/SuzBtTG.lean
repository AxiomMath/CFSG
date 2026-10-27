
module

public import Certificates.Kernel.Sporadic.OddCore.SuzBtOG
public import Certificates.Kernel.Sporadic.OddCore.SuzBtTF
public import CFSG.Sporadic.SuzRecog.SuzL34.Bridge
import CFSG.Certificates.Kernel.Common.Harness
import CFSG.Certificates.Kernel.Spor.RawOrbEval
import Mathlib.Tactic.IntervalCases

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSpor.SuzBtTG

open CFSG.KC.Enum CFSG.KS CFSG.KS.BTup CertificateChecks.KernelSpor
open CFSG.Sporadic.SuzOddCore CFSG.Sporadic.SuzRecog CFSG.Sporadic.SuzRecog.C1Model
open CFSG.Sporadic.SuzRecog.SuzL34Cert CertificateChecks.KernelSpor.SuzC1EG
open CertificateChecks.KernelSpor.SuzBtG CertificateChecks.KernelSpor.SuzBtZG
  CertificateChecks.KernelSpor.SuzBtOG

theorem kBT : allN 4 (fun j => Nat.beq (SuzBtT0.G j)
    (decK (C1ModelData.t0Decs.getD j ([], 0)))) = true := by quickRfl

theorem hgT : ∀ j < 4, ∀ x : Fin 1782, pg 11 (mask 11) (SuzBtT0.G j) x = t0Gen j x :=
  fun j hj x => by
    rw [Nat.eq_of_beq_eq_true (allN_spec kBT j hj)]
    exact pg_decK (C1Model.t0Decs_ok hj).1 (C1Model.t0Decs_ok hj).2 x

theorem hbT : ∀ t : Fin 3, pg 11 (mask 11) SuzBtT0.B t = c1Base t := by
  intro t
  fin_cases t <;> rfl

theorem hpT : ∀ i < SuzBtT0.cnt, btPtK 1782 11 (mask 11) 3 33 (mask 33) 4 SuzBtT0.cnt SuzBtT0.B
    SuzBtT0.G SuzBtT0.K SuzBtT0.R SuzBtT0.POS i = true := fun i hi =>
  btSl_spec SuzBtTF.kT0Sl (Nat.zero_le _) (by rw [SuzBtTF.kT0Cnt] at hi; omega) hi

theorem t0_eq : genSub 1782 4 t0Gen = T0 := T0_eq.symm

theorem hfixT : ∀ h ∈ genSub 1782 4 t0Gen, (∀ t, h (c1Base t) = c1Base t) → h = 1 :=
  fun h hh hf => invE1_eq_one (T0_le_invE (t0_eq ▸ hh)) hf

theorem hST : ∀ j < 4, ∀ t : Fin 3,
    pg 11 (mask 11) (btKey 33 (mask 33) SuzBtT0.K (SuzBtT0Z.S j)) t = t0Gen j (c1Base t) :=
  fun j hj => mov_base hbT (hgT j hj) (CFSG.KS.Raw.Orb.allN_iff.1 SuzBtTF.kT0S j hj)

theorem hrT : ∀ i < SuzBtT0.cnt, btRtK 4 4 SuzBtT0.cnt SuzBtT0Z.S SuzBtT0.R SuzBtT0.POS
    SuzBtT0Z.RT i = true := fun i hi =>
  btRtSl_spec SuzBtTF.kT0Rt (Nat.zero_le _) (by rw [SuzBtTF.kT0Cnt] at hi; omega) hi

theorem hK0 : btKey 33 (mask 33) (fun _ => SuzBtT0.B) 0 = SuzBtT0.B := by decide

theorem hK0b (t : Fin 3) :
    pg 11 (mask 11) (btKey 33 (mask 33) (fun _ => SuzBtT0.B) 0) t = (1 : Equiv.Perm (Fin 1782))
      (c1Base t) := by
  rw [hK0, Equiv.Perm.one_apply, hbT t]

theorem hL1 : ∀ q < 1, ∃ l ∈ (⊥ : Subgroup (Equiv.Perm (Fin 1782))), ∀ t : Fin 3,
    pg 11 (mask 11) (btKey 33 (mask 33) (fun _ => SuzBtT0.B) q) t = l (c1Base t) := by
  intro q hq
  obtain rfl : q = 0 := by omega
  exact ⟨1, Subgroup.one_mem _, hK0b⟩

theorem hLcov : ∀ l ∈ (⊥ : Subgroup (Equiv.Perm (Fin 1782))), l ∈ genSub 1782 4 t0Gen →
    ∃ q < 1, ∀ t : Fin 3,
      pg 11 (mask 11) (btKey 33 (mask 33) (fun _ => SuzBtT0.B) q) t = l (c1Base t) :=
  fun l hl _ => by
    rw [Subgroup.mem_bot] at hl
    subst hl
    exact ⟨0, by norm_num, hK0b⟩

theorem hLcan : ∀ q < 1, btKey 33 (mask 33) (fun _ => SuzBtT0.B) q >>> (3 * 11) = 0 := by
  intro q hq
  obtain rfl : q = 0 := by omega
  rw [hK0]
  decide

theorem hext : ∀ x ∈ genSub 1782 4 t0Gen, ∀ l ∈ (⊥ : Subgroup (Equiv.Perm (Fin 1782))),
    (∀ t, x (c1Base t) = l (c1Base t)) → x = l := fun x hx l hl e => by
  rw [Subgroup.mem_bot] at hl
  subst hl
  exact hfixT x hx e

theorem kI_eq : btCntN SuzBtT0.cnt (btInvP 4 33 (mask 33) 1 SuzBtT0.K SuzBtT0.R SuzBtT0Z.RT
    (fun _ => SuzBtT0.B)) = 27 := Nat.beq_eq.mp SuzBtTF.kT0I

theorem card_inv_t0 : Nat.card {x : T0 // x * x = 1 ∧ x ≠ 1} = 27 := by
  have h := card_inv_of_btInvP hgT hpT hfixT hbT hST hrT (by norm_num) SuzBtTF.kT0Hd hL1 hLcov
    hLcan hext
  rw [kI_eq] at h
  rw [← h, ← t0_eq]
  refine Nat.card_congr (Equiv.subtypeEquivRight fun x => ?_)
  rw [Subgroup.mem_bot]
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨h1, h2, fun h3 => h2 (Subtype.ext h3)⟩
  · rintro ⟨h1, h2, -⟩
    exact ⟨h1, h2⟩

theorem fixed_t0 {x : Equiv.Perm (Fin 1782)} (hx : x ∈ T0) (h2 : x * x = 1) (h1 : x ≠ 1) :
    fixedCard x = 54 := by
  rw [← t0_eq] at hx
  obtain ⟨i, hi, he⟩ := btKey_cover hgT hbT hpT SuzBtTF.kT0Hd hx
  have hinv := (btInvP_iff_el hgT hpT hfixT hbT hST hrT (by norm_num) SuzBtTF.kT0Hd hL1 hLcov
    hLcan hext hi hx he).2 ⟨h2, h1, fun h3 => h1 (Subgroup.mem_bot.1 h3)⟩
  have hf := CFSG.KS.Raw.Orb.allN_iff.1 SuzBtTF.kT0Fx i hi
  rw [CFSG.KS.Raw.Orb.bIf_eq, if_pos hinv] at hf
  have hc := Nat.beq_eq.mp hf
  have hm : (Finset.univ.filter fun p : Fin 1782 => x p = p).map Fin.valEmbedding =
      (Finset.range 1782).filter (fun p =>
        Nat.beq (btWalk 11 (mask 11) SuzBtT0.G SuzBtT0.R i p) p = true) := by
    ext p
    simp only [Finset.mem_map, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_range,
      Fin.valEmbedding_apply]
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact ⟨y.2, Nat.beq_eq.mpr (by rw [btWalk_spec hgT hpT hfixT hbT hi hx he y, hy])⟩
    · rintro ⟨hp, hb⟩
      refine ⟨⟨p, hp⟩, Fin.ext ?_, rfl⟩
      rw [← btWalk_spec hgT hpT hfixT hbT hi hx he ⟨p, hp⟩]
      exact Nat.beq_eq.mp hb
  rw [fixedCard_eq_filter, ← Finset.card_map Fin.valEmbedding, hm, ← btCntN_eq, hc]

theorem sq_val {H : Subgroup (Equiv.Perm (Fin 1782))} {x : H} (h : x * x = 1) :
    (x : Equiv.Perm (Fin 1782)) * x = 1 := congrArg Subtype.val h

theorem ne_val {H : Subgroup (Equiv.Perm (Fin 1782))} {x : H} (h : x ≠ 1) :
    (x : Equiv.Perm (Fin 1782)) ≠ 1 := fun e => h (Subtype.ext e)

theorem sq_mk {H : Subgroup (Equiv.Perm (Fin 1782))} {y : Equiv.Perm (Fin 1782)} {hy : y ∈ H}
    (h : y * y = 1) : (⟨y, hy⟩ : H) * ⟨y, hy⟩ = 1 := Subtype.ext h

theorem ne_mk {H : Subgroup (Equiv.Perm (Fin 1782))} {y : Equiv.Perm (Fin 1782)} {hy : y ∈ H}
    (h : y ≠ 1) : (⟨y, hy⟩ : H) ≠ 1 := fun e => h (congrArg Subtype.val e)

theorem f4Prop : F4Prop := by
  unfold F4Prop
  dsimp only
  rw [tabSubgroup_v0Tabs, tabSubgroup_t0Tabs]
  have hT : ∀ x : V0, x * x = 1 → x ≠ 1 → fixedCard (x : Equiv.Perm (Fin 1782)) = 54 →
      (x : Equiv.Perm (Fin 1782)) ∈ T0 := fun x h2 h1 hf =>
    mem_T0_of_fix x.2 (sq_val h2) (ne_val h1)
      (by rw [← fixedCard_eq_card_filter, hf]; norm_num)
  refine ⟨?_, hT, card_inv_t0, fun x h2 h1 => fixed_t0 x.2 (sq_val h2) (ne_val h1)⟩
  rw [← card_inv_t0]
  exact Nat.card_congr
    { toFun := fun x => ⟨⟨(x.1 : Equiv.Perm (Fin 1782)), hT x.1 x.2.1 x.2.2.1 x.2.2.2⟩,
        sq_mk (sq_val x.2.1), ne_mk (ne_val x.2.2.1)⟩
      invFun := fun y => ⟨⟨(y.1 : Equiv.Perm (Fin 1782)), T0_le_V0 y.1.2⟩,
        sq_mk (sq_val y.2.1), ne_mk (ne_val y.2.2),
        fixed_t0 (x := (y.1 : Equiv.Perm (Fin 1782))) y.1.2 (sq_val (H := T0) y.2.1)
          (ne_val (H := T0) y.2.2)⟩
      left_inv := fun x => rfl
      right_inv := fun y => rfl }

end CertificateChecks.KernelSpor.SuzBtTG

end
