
module

public import Certificates.Kernel.Sporadic.OddCore.SuzBtFG
public import Certificates.Kernel.Sporadic.OddCore.SuzBtWF
public import Certificates.Kernel.Sporadic.OddCore.SuzC1EL
import CFSG.Certificates.Kernel.Common.Harness
import CFSG.Certificates.Kernel.Spor.RawOrbEval
import CFSG.Certificates.Kernel.Spor.BTupISound
import CFSG.Certificates.Kernel.HeFixKFix
import Mathlib.Tactic.DefEqTransformations
import Mathlib.Tactic.Group

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSpor.SuzBtWG

open CFSG.KC.Enum CFSG.KS CFSG.KS.BTup CertificateChecks.KernelSpor
open CFSG.Sporadic.SuzOddCore CFSG.Sporadic.SuzRecog CFSG.Sporadic.SuzRecog.C1Model
open CFSG.Sporadic.SuzRecog.SuzL34Cert
open CertificateChecks.KernelSpor.SuzBtG CertificateChecks.KernelSpor.SuzBtZG
  CertificateChecks.KernelSpor.SuzBtOG CertificateChecks.KernelSpor.SuzBtTG
  CertificateChecks.KernelSpor.SuzBtWF

theorem e3_iff {f g : Nat → Nat} : agB f g = true ↔ ∀ t : Fin 3, f (c1Base t) = g (c1Base t) := by
  unfold agB
  rw [CFSG.KS.Raw.Orb.allN_iff]
  constructor
  · intro h t
    have e := Nat.beq_eq.mp (h t t.2)
    rwa [hbT t] at e
  · intro h t ht
    refine Nat.beq_eq.mpr ?_
    rw [hbT ⟨t, ht⟩]
    exact h ⟨t, ht⟩

theorem ext_e3 {x y : Equiv.Perm (Fin 1782)} (hx : x ∈ invE 1) (hy : y ∈ invE 1) {f g : Nat → Nat}
    (h : agB f g = true) (hf : ∀ p : Fin 1782, f p = x p) (hg : ∀ p : Fin 1782, g p = y p) :
    x = y :=
  invE1_ext hx hy fun t => Fin.ext (by rw [← hf, ← hg]; exact e3_iff.1 h t)

theorem hpW (p : Fin 1782) : pW p = wP p := hW p

theorem pV {x : Equiv.Perm (Fin 1782)} (hx : x ∈ V0) :
    ∃ k < 512, ∀ p : Fin 1782, pg 11 (mask 11) (SuzC1EV.T k) p = x p := by
  obtain ⟨k, hk, hrep⟩ := enumerates_V0.exists_pos hx
  rw [SuzC1EV.v0_size] at hk
  refine ⟨k, hk, fun p => ?_⟩
  rw [← CFSG.KC.HeFixK.unpack_getElem! p.2, ← (SuzC1EV.pVk hk).1]
  exact hrep.2 p

theorem pTinv {g : Equiv.Perm (Fin 1782)} (hg : g ∈ T0) :
    ∃ q < 64, ∀ p : Fin 1782, pg 11 (mask 11) (SuzC1ET.T q) p = g p := by
  obtain ⟨q, hq, hrep⟩ := enumerates_T0.exists_pos hg
  rw [SuzC1EF.t0_size] at hq
  refine ⟨q, hq, fun p => ?_⟩
  rw [← CFSG.KC.HeFixK.unpack_getElem! p.2, ← (SuzC1EL.pT0k hq).1]
  exact hrep.2 p

theorem pT {q : Nat} (hq : q < 64) :
    ∃ g ∈ T0, ∀ p : Fin 1782, pg 11 (mask 11) (SuzC1ET.T q) p = g p := by
  have hq' : q < t0Enum.tabs.size := by
    rw [SuzC1EF.t0_size]
    exact hq
  have hm : t0Enum.tabs[q]! ∈ t0Enum.tabs.toList := by
    rw [getElem!_pos t0Enum.tabs q hq']
    exact Array.getElem_mem_toList hq'
  obtain ⟨g, hg, hrep⟩ := enumerates_T0.sound _ hm
  refine ⟨g, hg, fun p => ?_⟩
  rw [← CFSG.KC.HeFixK.unpack_getElem! p.2, ← (SuzC1EL.pT0k hq).1]
  exact hrep.2 p

theorem fixedCard_cnt {x : Equiv.Perm (Fin 1782)} {f : Nat → Nat}
    (hf : ∀ p : Fin 1782, f p = x p) : fixedCard x = fxN f := by
  have hm : (Finset.univ.filter fun p : Fin 1782 => x p = p).map Fin.valEmbedding =
      (Finset.range 1782).filter (fun p => Nat.beq (f p) p = true) := by
    ext p
    simp only [Finset.mem_map, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_range,
      Fin.valEmbedding_apply]
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact ⟨y.2, Nat.beq_eq.mpr (by rw [hf y, hy])⟩
    · rintro ⟨hp, hb⟩
      refine ⟨⟨p, hp⟩, Fin.ext ?_, rfl⟩
      rw [← hf ⟨p, hp⟩]
      exact Nat.beq_eq.mp hb
  unfold fxN
  rw [fixedCard_eq_filter, ← Finset.card_map Fin.valEmbedding, hm, ← btCntN_eq]

theorem bad_iff {y : Equiv.Perm (Fin 1782)} (hy : y ∈ invE 1) {f : Nat → Nat}
    (hf : ∀ p : Fin 1782, f p = y p) : bad f = true ↔
      y * y = 1 ∧ y ≠ 1 ∧ y ≠ wP ∧ fixedCard y = 42 ∧ fixedCard (y * wP) = 42 := by
  have hff : ∀ p : Fin 1782, f (f p) = (y * y) p := fun p => by
    rw [hf, hf, Equiv.Perm.mul_apply]
  have hfw : ∀ p : Fin 1782, f (pW p) = (y * wP) p := fun p => by
    rw [hpW, hf, Equiv.Perm.mul_apply]
  have hid : ∀ p : Fin 1782, (p : Nat) = (1 : Equiv.Perm (Fin 1782)) p := fun _ => rfl
  have hyy := Subgroup.mul_mem _ hy hy
  unfold bad
  rw [SuzBtFG.bAnd_iff, SuzBtFG.bAnd_iff, SuzBtFG.bAnd_iff, SuzBtFG.bAnd_iff,
    SuzBtFG.not_true_iff, SuzBtFG.not_true_iff, Nat.beq_eq, Nat.beq_eq, ← fixedCard_cnt hf,
    ← fixedCard_cnt (f := fun p => f (pW p)) hfw]
  constructor
  · rintro ⟨h2, h1, hw, h3, h4⟩
    refine ⟨ext_e3 hyy (Subgroup.one_mem _) h2 hff hid, fun e => h1 ?_, fun e => hw ?_, h3, h4⟩
    · refine e3_iff.2 fun t => ?_
      rw [hf, e, Equiv.Perm.one_apply]
    · refine e3_iff.2 fun t => ?_
      rw [hf, hpW, e]
  · rintro ⟨h2, h1, hw, h3, h4⟩
    refine ⟨e3_iff.2 fun t => ?_, fun e => h1 (ext_e3 hy (Subgroup.one_mem _) e hf hid),
      fun e => hw (ext_e3 hy w_mem e hf hpW), h3, h4⟩
    rw [hff, h2, Equiv.Perm.one_apply]

theorem conj11 {g : Equiv.Perm (Fin 1782)} (hg : g ∈ V0) {x : Equiv.Perm (Fin 1782)}
    (hx : x ∈ T0 ∨ ∃ t ∈ T0, x = wP * t) :
    g * x * g⁻¹ ∈ T0 ∨ ∃ t ∈ T0, g * x * g⁻¹ = wP * t := by
  rcases hx with hx | ⟨t, ht, rfl⟩
  · exact Or.inl (SuzBtFG.V0_conj hg hx)
  · refine Or.inr ⟨g * t * g⁻¹, SuzBtFG.V0_conj hg ht, ?_⟩
    have hc : g * wP = wP * g := (mem_V0_iff.1 hg).1
    calc g * (wP * t) * g⁻¹ = g * wP * t * g⁻¹ := by group
      _ = wP * g * t * g⁻¹ := by rw [hc]
      _ = wP * (g * t * g⁻¹) := by group

theorem sq11 {x : Equiv.Perm (Fin 1782)} (hx : x ∈ V0) :
    x * x ∈ T0 ∨ ∃ t ∈ T0, x * x = wP * t := by
  obtain ⟨k, hk, hxk⟩ := pV hx
  have hxm := (mem_V0_iff.1 hx).2
  have hxx : ∀ p : Fin 1782, pg 11 (mask 11) (SuzC1EV.T k) (pg 11 (mask 11) (SuzC1EV.T k) p) =
      (x * x) p := fun p => by
    rw [hxk, hxk, Equiv.Perm.mul_apply]
  have h := CFSG.KS.Raw.Orb.allN_iff.1 kSq k hk
  unfold inT11 at h
  obtain ⟨q, hq, hqe⟩ := exists_of_not_allN_not h
  obtain ⟨g, hg, hgq⟩ := pT hq
  rcases SuzBtFG.bOr_iff.1 hqe with hc | hc
  · left
    rw [← ext_e3 (T0_le_invE hg) (Subgroup.mul_mem _ hxm hxm) hc hgq hxx]
    exact hg
  · right
    have hf : ∀ p : Fin 1782, pW (pg 11 (mask 11) (SuzC1ET.T q) p) = (wP * g) p := fun p => by
      rw [hgq, hpW, Equiv.Perm.mul_apply]
    exact ⟨g, hg, (ext_e3 (Subgroup.mul_mem _ w_mem (T0_le_invE hg))
      (Subgroup.mul_mem _ hxm hxm) hc hf hxx).symm⟩

theorem lamDec_ok : (∀ k ∈ lam0Dec.1, k < 10) ∧ lam0Dec.2 < 128 := by decide

theorem aDec_ok : (∀ k ∈ aDec.1, k < 10) ∧ aDec.2 < 128 := by decide

theorem hL (p : Fin 1782) : pg 11 (mask 11) (SuzC1EG.decK lam0Dec) p = decPerm lam0Dec p :=
  pg_decK lamDec_ok.1 lamDec_ok.2 p

theorem hA (p : Fin 1782) : pg 11 (mask 11) (SuzC1EG.decK aDec) p = decPerm aDec p :=
  pg_decK aDec_ok.1 aDec_ok.2 p

theorem lam_mem : decPerm lam0Dec ∈ invE 1 := decPerm_mem lamDec_ok.1

theorem a_mem : decPerm aDec ∈ invE 1 := decPerm_mem aDec_ok.1

theorem rt11 {x : Equiv.Perm (Fin 1782)} (hx : x ∈ V0) (h2 : x * x = wP) :
    x * (decPerm lam0Dec)⁻¹ ∈ T0 ∨ ∃ t ∈ T0, x * (decPerm lam0Dec)⁻¹ = wP * t := by
  obtain ⟨k, hk, hxk⟩ := pV hx
  have hxm := (mem_V0_iff.1 hx).2
  have h := CFSG.KS.Raw.Orb.allN_iff.1 kRt k hk
  have hc : agB (fun p => pg 11 (mask 11) (SuzC1EV.T k) (pg 11 (mask 11) (SuzC1EV.T k) p)) pW =
      true := by
    refine e3_iff.2 fun t => ?_
    rw [hxk, hxk, hpW, ← Equiv.Perm.mul_apply, h2]
  rw [SuzBtFG.bIf_true hc] at h
  obtain ⟨q, hq, hqe⟩ := exists_of_not_allN_not h
  obtain ⟨g, hg, hgq⟩ := pT hq
  rcases SuzBtFG.bOr_iff.1 hqe with hc1 | hc1
  · left
    have hf : ∀ p : Fin 1782, pg 11 (mask 11) (SuzC1ET.T q) (pg 11 (mask 11)
        (SuzC1EG.decK lam0Dec) p) = (g * decPerm lam0Dec) p := fun p => by
      rw [hL, hgq, Equiv.Perm.mul_apply]
    have e := ext_e3 (Subgroup.mul_mem _ (T0_le_invE hg) lam_mem) hxm hc1 hf hxk
    rw [← e, mul_inv_cancel_right]
    exact hg
  · right
    have hf : ∀ p : Fin 1782, pW (pg 11 (mask 11) (SuzC1ET.T q) (pg 11 (mask 11)
        (SuzC1EG.decK lam0Dec) p)) = (wP * g * decPerm lam0Dec) p := fun p => by
      rw [hL, hgq, hpW, Equiv.Perm.mul_apply, Equiv.Perm.mul_apply]
    have e := ext_e3 (Subgroup.mul_mem _ (Subgroup.mul_mem _ w_mem (T0_le_invE hg)) lam_mem) hxm
      hc1 hf hxk
    refine ⟨g, hg, ?_⟩
    rw [← e, mul_inv_cancel_right]

theorem not_T11 {a : Equiv.Perm (Fin 1782)} (h2 : a * a = 1) (h1 : a ≠ 1) (hw : a ≠ wP)
    (hf : fixedCard a = 42) (hfw : fixedCard (a * wP) = 42) :
    ¬ (a ∈ T0 ∨ ∃ t ∈ T0, a = wP * t) := by
  rintro (hT | ⟨t, ht, rfl⟩)
  · have := fixed_t0 hT h2 h1
    omega
  · have htw : t * wP = wP * t :=
      Subgroup.mem_centralizer_singleton_iff.1 (T0_le_centralizer_w0 ht)
    have e : wP * t * wP = t := by rw [mul_assoc, htw, ← mul_assoc, w_sq, one_mul]
    rw [e] at hfw
    have ht1 : t ≠ 1 := fun h => hw (by rw [h, mul_one])
    have ht2 : t * t = 1 := by
      have h := h2
      rw [show wP * t * (wP * t) = wP * t * wP * t by group, e] at h
      exact h
    have := fixed_t0 ht ht2 ht1
    omega

theorem bad_of {a : Equiv.Perm (Fin 1782)} (ha : a ∈ V0) (h2 : a * a = 1) (h1 : a ≠ 1)
    (hw : a ≠ wP) (hf : fixedCard a = 42) (hfw : fixedCard (a * wP) = 42) :
    ¬ (a * (decPerm lam0Dec)⁻¹ ∈ T0 ∨ ∃ t ∈ T0, a * (decPerm lam0Dec)⁻¹ = wP * t) := by
  have ham := (mem_V0_iff.1 ha).2
  rintro (hT | ⟨t, ht, he⟩)
  · obtain ⟨q, hq, hgq⟩ := pTinv hT
    have h := (SuzBtFG.bAnd_iff.1 (CFSG.KS.Raw.Orb.allN_iff.1 kD q hq)).1
    have hfa : ∀ p : Fin 1782, pg 11 (mask 11) (SuzC1ET.T q) (pg 11 (mask 11)
        (SuzC1EG.decK lam0Dec) p) = a p := fun p => by
      rw [hL, hgq, Equiv.Perm.mul_apply, Equiv.Perm.inv_def, Equiv.symm_apply_apply]
    exact SuzBtFG.not_true_iff.1 h ((bad_iff ham hfa).2 ⟨h2, h1, hw, hf, hfw⟩)
  · obtain ⟨q, hq, hgq⟩ := pTinv ht
    have hae : a = wP * t * decPerm lam0Dec := by rw [← he, inv_mul_cancel_right]
    have h := (SuzBtFG.bAnd_iff.1 (CFSG.KS.Raw.Orb.allN_iff.1 kD q hq)).2
    have hfa : ∀ p : Fin 1782, pW (pg 11 (mask 11) (SuzC1ET.T q) (pg 11 (mask 11)
        (SuzC1EG.decK lam0Dec) p)) = a p := fun p => by
      rw [hL, hgq, hpW, hae, Equiv.Perm.mul_apply, Equiv.Perm.mul_apply]
    exact SuzBtFG.not_true_iff.1 h ((bad_iff ham hfa).2 ⟨h2, h1, hw, hf, hfw⟩)

theorem a_facts : decPerm aDec ∈ V0 ∧ decPerm aDec * decPerm aDec = 1 ∧ decPerm aDec ≠ 1 ∧
    decPerm aDec ≠ wP ∧ fixedCard (decPerm aDec) = 42 ∧ fixedCard (decPerm aDec * wP) = 42 := by
  have h := kA
  rw [SuzBtFG.bAnd_iff, SuzBtFG.bAnd_iff] at h
  obtain ⟨hc, -, hb⟩ := h
  have hf1 : ∀ p : Fin 1782, pg 11 (mask 11) (SuzC1EG.decK aDec) (pW p) =
      (decPerm aDec * wP) p := fun p => by
    rw [hpW, hA, Equiv.Perm.mul_apply]
  have hf2 : ∀ p : Fin 1782, pW (pg 11 (mask 11) (SuzC1EG.decK aDec) p) =
      (wP * decPerm aDec) p := fun p => by
    rw [hA, hpW, Equiv.Perm.mul_apply]
  exact ⟨mem_V0_iff.2 ⟨ext_e3 (Subgroup.mul_mem _ a_mem w_mem) (Subgroup.mul_mem _ w_mem a_mem)
    hc hf1 hf2, a_mem⟩, (bad_iff a_mem hA).1 hb⟩

theorem lam_facts : decPerm lam0Dec ∈ V0 ∧ decPerm lam0Dec * decPerm lam0Dec = wP := by
  have h := kL
  rw [SuzBtFG.bAnd_iff] at h
  obtain ⟨hc, hs⟩ := h
  have hf1 : ∀ p : Fin 1782, pg 11 (mask 11) (SuzC1EG.decK lam0Dec) (pW p) =
      (decPerm lam0Dec * wP) p := fun p => by
    rw [hpW, hL, Equiv.Perm.mul_apply]
  have hf2 : ∀ p : Fin 1782, pW (pg 11 (mask 11) (SuzC1EG.decK lam0Dec) p) =
      (wP * decPerm lam0Dec) p := fun p => by
    rw [hL, hpW, Equiv.Perm.mul_apply]
  have hf3 : ∀ p : Fin 1782, pg 11 (mask 11) (SuzC1EG.decK lam0Dec)
      (pg 11 (mask 11) (SuzC1EG.decK lam0Dec) p) = (decPerm lam0Dec * decPerm lam0Dec) p :=
    fun p => by rw [hL, hL, Equiv.Perm.mul_apply]
  exact ⟨mem_V0_iff.2 ⟨ext_e3 (Subgroup.mul_mem _ lam_mem w_mem)
    (Subgroup.mul_mem _ w_mem lam_mem) hc hf1 hf2, lam_mem⟩,
    ext_e3 (Subgroup.mul_mem _ lam_mem lam_mem) w_mem hs hf3 hpW⟩

theorem f8Prop : F8Prop := by
  unfold F8Prop
  dsimp only
  rw [tabSubgroup_t0Tabs, tabSubgroup_v0Tabs]
  obtain ⟨a1, a2, a3, a4, a5, a6⟩ := a_facts
  exact ⟨fun g hg x hx => conj11 hg hx, fun x hx => sq11 hx, fun x hx h2 => rt11 hx h2,
    fun a ha h2 h1 hw hf hfw => ⟨not_T11 h2 h1 hw hf hfw, bad_of ha h2 h1 hw hf hfw⟩,
    a1, a2, a3, a4, a5, a6, lam_facts.1, lam_facts.2⟩

end CertificateChecks.KernelSpor.SuzBtWG

end
