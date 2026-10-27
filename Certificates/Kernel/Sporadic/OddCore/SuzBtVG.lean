
module

public import Certificates.Kernel.Sporadic.OddCore.SuzBtFG
public import Certificates.Kernel.Sporadic.OddCore.SuzBtVF
import CFSG.Certificates.Kernel.Common.Harness
import CFSG.Certificates.Kernel.Spor.RawOrbEval
import CFSG.Certificates.Kernel.Spor.BTupISound
import CFSG.Certificates.Kernel.Spor.BTupNSound
import CFSG.Certificates.Kernel.Spor.BTupOSound
import CFSG.Certificates.Kernel.HeFixKFix
import Mathlib.Tactic.Group
import Mathlib.Tactic.IntervalCases

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSpor.SuzBtVG

open CFSG.KC.Enum CFSG.KS CFSG.KS.BTup CertificateChecks.KernelSpor
open CFSG.Sporadic.SuzOddCore CFSG.Sporadic.SuzRecog CFSG.Sporadic.SuzRecog.C1Model
open CFSG.Sporadic.SuzRecog.SuzL34Cert CertificateChecks.KernelSpor.SuzC1EG
open CertificateChecks.KernelSpor.SuzBtG CertificateChecks.KernelSpor.SuzBtZG
  CertificateChecks.KernelSpor.SuzBtOG CertificateChecks.KernelSpor.SuzBtTG
  CertificateChecks.KernelSpor.SuzBtFG CertificateChecks.KernelSpor.SuzBtVF

theorem kBV0 : allN 7 (fun j => Nat.beq (SuzBtV0.G j) (SuzC1EV.G j)) = true := by quickRfl

theorem kNt : allN 8 (fun d => strictB (decK (ntl1Decs.getD d ([], 0))) (fun N =>
    bAnd(allN 3 (fun t => Nat.beq (pg 11 (mask 11) N (pg 11 (mask 11) (SuzTwG 6)
      (pg 11 (mask 11) SuzBtL1.B t))) (pg 11 (mask 11) (SuzTwG 6) (pg 11 (mask 11) N
        (pg 11 (mask 11) SuzBtL1.B t)))),
    allN 4 (fun j => btNrK 11 (mask 11) 3 4 SuzBtL1.G SuzBtL1.B N (SuzBtL1.G j))))) = true := by
  quickRfl

noncomputable abbrev VV : Subgroup (Equiv.Perm (Fin 1782)) := genSub 1782 7 v0Gen

theorem VV_eq : VV = V0 := V0_eq_closure_v0Gen.symm

theorem VV_le : VV ≤ invE 1 := fun _ h => (mem_V0_iff.1 (VV_eq ▸ h)).2

theorem hgV : ∀ j < 7, ∀ x : Fin 1782, pg 11 (mask 11) (SuzBtV0.G j) x = v0Gen j x :=
  fun j hj x => by
    rw [Nat.eq_of_beq_eq_true (allN_spec kBV0 j hj), ← CFSG.KC.HeFixK.unpack_getElem! x.2,
      ← (pV0 hj).1, show v0Tabs[j]! = v0Tab j from ofFn_get _ hj]
    exact (tabRep_v0Tab j).2 x

theorem hbV : ∀ t : Fin 3, pg 11 (mask 11) SuzBtV0.B t = c1Base t := by
  intro t
  fin_cases t <;> rfl

theorem hpV : ∀ i < SuzBtV0.cnt, btPtK 1782 11 (mask 11) 3 33 (mask 33) 7 SuzBtV0.cnt SuzBtV0.B
    SuzBtV0.G SuzBtV0.K SuzBtV0.R SuzBtV0.POS i = true := fun i hi =>
  btSl_spec SuzBtVF.kV0Sl (Nat.zero_le _) (by rw [SuzBtVF.kV0Cnt] at hi; omega) hi

theorem hfixV : ∀ h ∈ VV, (∀ t, h (c1Base t) = c1Base t) → h = 1 :=
  fun h hh hf => invE1_eq_one (VV_le hh) hf

theorem hfixL : ∀ h ∈ genSub 1782 4 lgp, (∀ t, h (c1Base t) = c1Base t) → h = 1 :=
  fun h hh hf => invE1_eq_one (l1_le hh) hf

theorem cntV_lt {i : Nat} (hi : i < 512) : i < SuzBtV0.cnt := by
  rw [SuzBtVF.kV0Cnt]
  exact hi

theorem stV_ex {i : Nat} (hi : i < 512) : ∃ h ∈ VV, ∀ t : Fin 3,
    pg 11 (mask 11) (btKey 33 (mask 33) SuzBtV0.K i) t = h (c1Base t) :=
  btKey_mem hgV hbV hpV (cntV_lt hi)

noncomputable def elV (i : Nat) : Equiv.Perm (Fin 1782) :=
  if h : i < 512 then Classical.choose (stV_ex h) else 1

theorem elV_mem {i : Nat} (hi : i < 512) : elV i ∈ VV := by
  unfold elV
  rw [dif_pos hi]
  exact (Classical.choose_spec (stV_ex hi)).1

theorem elV_key {i : Nat} (hi : i < 512) (t : Fin 3) :
    pg 11 (mask 11) (btKey 33 (mask 33) SuzBtV0.K i) t = elV i (c1Base t) := by
  unfold elV
  rw [dif_pos hi]
  exact (Classical.choose_spec (stV_ex hi)).2 t

theorem elV_of {i : Nat} (hi : i < 512) {x : Equiv.Perm (Fin 1782)} (hx : x ∈ VV)
    (he : ∀ t : Fin 3, pg 11 (mask 11) (btKey 33 (mask 33) SuzBtV0.K i) t = x (c1Base t)) :
    elV i = x :=
  ext_of_base hfixV (elV_mem hi) hx fun t => Fin.ext (by rw [← elV_key hi t, he t])

theorem elV_cover {x : Equiv.Perm (Fin 1782)} (hx : x ∈ VV) : ∃ i < 512, elV i = x := by
  obtain ⟨i, hi, he⟩ := btKey_cover hgV hbV hpV SuzBtVF.kV0Hd hx
  rw [SuzBtVF.kV0Cnt] at hi
  exact ⟨i, hi, elV_of hi hx he⟩

theorem elV_inj {i j : Nat} (hi : i < 512) (hj : j < 512) (h : elV i = elV j) : i = j :=
  btKey_inj (by norm_num) hpV (cntV_lt hi) (cntV_lt hj) fun t => by
    rw [elV_key hi t, elV_key hj t, h]

theorem wV_eq {i : Nat} (hi : i < 512) (p : Fin 1782) : wV i p = elV i p :=
  btWalk_spec hgV hpV hfixV hbV (cntV_lt hi) (elV_mem hi) (elV_key hi) p

theorem kyV_eq {i : Nat} (hi : i < 512) (t : Fin 3) : kyV i t = elV i (c1Base t) :=
  elV_key hi t

theorem card_statesV (P : Equiv.Perm (Fin 1782) → Prop) (f : Nat → Bool)
    (hP : ∀ x, P x → x ∈ VV) (hf : ∀ i < 512, f i = true ↔ P (elV i)) :
    Nat.card {x // P x} = btCntN 512 f := by
  rw [btCntN_eq]
  set T := (Finset.range 512).filter (fun i => f i = true)
  have hT : T.card = Nat.card {i : Nat // i ∈ T} := by
    rw [Nat.card_eq_fintype_card, Fintype.card_coe]
  rw [hT]
  have hmemT : ∀ i ∈ T, i < 512 ∧ f i = true := fun i hi => by
    rw [Finset.mem_filter, Finset.mem_range] at hi
    exact hi
  let φ : {i : Nat // i ∈ T} → {x // P x} := fun i =>
    ⟨elV i.1, (hf i.1 (hmemT i.1 i.2).1).1 (hmemT i.1 i.2).2⟩
  have hbij : Function.Bijective φ := by
    refine ⟨fun i j e => Subtype.ext (elV_inj (hmemT i.1 i.2).1 (hmemT j.1 j.2).1
      (congrArg Subtype.val e)), fun x => ?_⟩
    obtain ⟨i, hi, he⟩ := elV_cover (hP x.1 x.2)
    have hiT : i ∈ T := by
      rw [Finset.mem_filter, Finset.mem_range]
      exact ⟨hi, (hf i hi).2 (he ▸ x.2)⟩
    exact ⟨⟨i, hiT⟩, Subtype.ext he⟩
  exact (Nat.card_congr (Equiv.ofBijective φ hbij)).symm

theorem pgL {j : Nat} (hj : j < 4) (t : Fin 3) :
    pg 11 (mask 11) (SuzBtL1.G j) (pg 11 (mask 11) SuzBtV0.B t) = lgp j (c1Base t) := by
  rw [hbV t, hgL j hj]

theorem czV_iff {i : Nat} (hi : i < 512) :
    czV SuzBtL1.G i = true ↔
      elV i ∈ Subgroup.centralizer (genSub 1782 4 lgp : Set (Equiv.Perm (Fin 1782))) := by
  rw [mem_cent_iff]
  unfold czV
  rw [CFSG.KS.Raw.Orb.allN_iff]
  refine forall₂_congr fun j hj => ?_
  rw [CFSG.KS.Raw.Orb.allN_iff]
  have hm1 := Subgroup.mul_mem _ (l1_le (gp_mem hj)) (VV_le (elV_mem hi))
  have hm2 := Subgroup.mul_mem _ (VV_le (elV_mem hi)) (l1_le (gp_mem hj))
  constructor
  · intro h
    refine invE1_ext hm1 hm2 fun t => Fin.ext ?_
    have e := Nat.beq_eq.mp (h t t.2)
    rw [pgL hj t, wV_eq hi, kyV_eq hi t, hgL j hj] at e
    rw [Equiv.Perm.mul_apply, Equiv.Perm.mul_apply]
    exact e.symm
  · intro h t ht
    refine Nat.beq_eq.mpr ?_
    have e := congrArg (fun g => (g (c1Base ⟨t, ht⟩) : Nat)) h
    simp only [Equiv.Perm.mul_apply] at e
    rw [pgL hj ⟨t, ht⟩, wV_eq hi, kyV_eq hi ⟨t, ht⟩, hgL j hj]
    exact e.symm

theorem conj_l1_iff {x : Equiv.Perm (Fin 1782)} :
    (∀ y ∈ genSub 1782 4 lgp, x * y * x⁻¹ ∈ genSub 1782 4 lgp) ↔
      ∀ j < 4, x * lgp j * x⁻¹ ∈ genSub 1782 4 lgp := by
  refine ⟨fun h j hj => h _ (gp_mem hj), fun h y hy => ?_⟩
  induction hy using Subgroup.closure_induction with
  | mem z hz =>
    obtain ⟨j, hj, rfl⟩ := hz
    exact h j hj
  | one => simpa using Subgroup.one_mem _
  | mul a c _ _ ha hc =>
    have e : x * (a * c) * x⁻¹ = (x * a * x⁻¹) * (x * c * x⁻¹) := by group
    rw [e]
    exact Subgroup.mul_mem _ ha hc
  | inv a _ ha =>
    have e : x * a⁻¹ * x⁻¹ = (x * a * x⁻¹)⁻¹ := by group
    rw [e]
    exact Subgroup.inv_mem _ ha

theorem nrV_iff {i : Nat} (hi : i < 512) :
    nrV SuzBtL1.G i = true ↔
      ∀ y ∈ genSub 1782 4 lgp, elV i * y * (elV i)⁻¹ ∈ genSub 1782 4 lgp := by
  rw [conj_l1_iff]
  unfold nrV
  rw [CFSG.KS.Raw.Orb.allN_iff]
  refine forall₂_congr fun j hj => ?_
  rw [not_allN_not_iff]
  have hx := VV_le (elV_mem hi)
  constructor
  · rintro ⟨p, hp, h⟩
    have hp' : p < SuzBtL1.cnt := by
      rw [SuzBtZF.kL1Cnt]
      exact hp
    obtain ⟨l, hl, hle⟩ := btKey_mem hgL hbL hpL hp'
    have e : elV i * lgp j = l * elV i := by
      refine invE1_ext (Subgroup.mul_mem _ hx (l1_le (gp_mem hj)))
        (Subgroup.mul_mem _ (l1_le hl) hx) fun t => Fin.ext ?_
      have e := Nat.beq_eq.mp (CFSG.KS.Raw.Orb.allN_iff.1 h t t.2)
      rw [pgL hj t, wV_eq hi, kyV_eq hi t,
        btWalk_spec hgL hpL hfixL hbL hp' hl hle] at e
      rw [Equiv.Perm.mul_apply, Equiv.Perm.mul_apply]
      exact e
    rw [e, mul_inv_cancel_right]
    exact hl
  · intro hc
    obtain ⟨p, hp, hpe⟩ := btKey_cover hgL hbL hpL SuzBtZF.kL1Hd hc
    refine ⟨p, by rw [SuzBtZF.kL1Cnt] at hp; exact hp, CFSG.KS.Raw.Orb.allN_iff.2 fun t ht =>
      Nat.beq_eq.mpr ?_⟩
    rw [pgL hj ⟨t, ht⟩, wV_eq hi, kyV_eq hi ⟨t, ht⟩,
      btWalk_spec hgL hpL hfixL hbL hp hc hpe]
    have e : elV i * lgp j * (elV i)⁻¹ * elV i = elV i * lgp j := by group
    rw [← Equiv.Perm.mul_apply (elV i * lgp j * (elV i)⁻¹) (elV i), e, Equiv.Perm.mul_apply]

theorem card_cent_v0 : Nat.card ↥(Subgroup.centralizer
    (genSub 1782 4 lgp : Set (Equiv.Perm (Fin 1782))) ⊓ VV) = 64 := by
  have h := card_statesV (fun x => x ∈ Subgroup.centralizer
    (genSub 1782 4 lgp : Set (Equiv.Perm (Fin 1782))) ⊓ VV) (czV SuzBtL1.G)
    (fun _ h => (Subgroup.mem_inf.1 h).2) fun i hi => by
      rw [czV_iff hi, Subgroup.mem_inf]
      exact ⟨fun h => ⟨h, elV_mem hi⟩, fun h => h.1⟩
  rw [Nat.beq_eq.mp SuzBtVF.kCz] at h
  exact h

theorem card_norm_v0 : Nat.card {x : VV // ∀ y ∈ genSub 1782 4 lgp,
    (x : Equiv.Perm (Fin 1782)) * y * (x : Equiv.Perm (Fin 1782))⁻¹ ∈ genSub 1782 4 lgp} = 256 := by
  have h := card_statesV (fun x => x ∈ VV ∧ ∀ y ∈ genSub 1782 4 lgp,
    x * y * x⁻¹ ∈ genSub 1782 4 lgp) (nrV SuzBtL1.G) (fun _ h => h.1) fun i hi => by
      rw [nrV_iff hi]
      exact ⟨fun h => ⟨elV_mem hi, h⟩, fun h => h.2⟩
  rw [Nat.beq_eq.mp SuzBtVF.kNr] at h
  rw [← h]
  exact Nat.card_congr (Equiv.subtypeSubtypeEquivSubtypeInter (· ∈ VV)
    (fun x => ∀ y ∈ genSub 1782 4 lgp, x * y * x⁻¹ ∈ genSub 1782 4 lgp))

theorem ntl1Decs_ok {d : Nat} (hd : d < 8) : (∀ k ∈ (ntl1Decs.getD d ([], 0)).1, k < 10) ∧
    (ntl1Decs.getD d ([], 0)).2 < 128 := by
  interval_cases d <;> decide

theorem nt_facts {d : Nat} (hd : d < 8) : decPerm (ntl1Decs.getD d ([], 0)) ∈ V0 ∧
    ∀ y ∈ genSub 1782 4 lgp, decPerm (ntl1Decs.getD d ([], 0)) * y *
      (decPerm (ntl1Decs.getD d ([], 0)))⁻¹ ∈ genSub 1782 4 lgp := by
  set ν := decPerm (ntl1Decs.getD d ([], 0))
  have hν : ∀ x : Fin 1782, pg 11 (mask 11) (decK (ntl1Decs.getD d ([], 0))) x = ν x :=
    pg_decK (ntl1Decs_ok hd).1 (ntl1Decs_ok hd).2
  have hνm : ν ∈ invE 1 := decPerm_mem (ntl1Decs_ok hd).1
  have h := CFSG.KS.Raw.Orb.allN_iff.1 kNt d hd
  rw [CFSG.KS.Raw.Orb.strictB_eq, SuzBtFG.bAnd_iff] at h
  obtain ⟨hw, hn⟩ := h
  refine ⟨mem_V0_iff.2 ⟨invE1_ext (Subgroup.mul_mem _ hνm w_mem)
    (Subgroup.mul_mem _ w_mem hνm) fun t => Fin.ext ?_, hνm⟩, conj_l1_iff.2 fun j hj => ?_⟩
  · have e := Nat.beq_eq.mp (CFSG.KS.Raw.Orb.allN_iff.1 hw t t.2)
    rw [hbL t, hW, hν, hν, hW] at e
    rw [Equiv.Perm.mul_apply, Equiv.Perm.mul_apply]
    exact e
  · obtain ⟨l, hl, hle⟩ := btNr_spec hgL hν (hgL j hj) hbL (CFSG.KS.Raw.Orb.allN_iff.1 hn j hj)
    have e : ν * lgp j = l * ν :=
      invE1_ext (Subgroup.mul_mem _ hνm (l1_le (gp_mem hj))) (Subgroup.mul_mem _ (l1_le hl) hνm)
        fun t => by
          rw [Equiv.Perm.mul_apply, Equiv.Perm.mul_apply]
          exact hle t
    rw [e, mul_inv_cancel_right]
    exact hl

theorem f6Prop : F6Prop := by
  unfold F6Prop
  dsimp only
  rw [tabSubgroup_v0Tabs, ← l1_eq, ← VV_eq]
  refine ⟨card_cent_v0, card_norm_v0, fun d hd => ?_⟩
  obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem hd
  have hk8 : k < 8 := hk
  have h := nt_facts hk8
  rw [List.getD_eq_getElem _ _ hk] at h
  rw [VV_eq]
  exact h

end CertificateChecks.KernelSpor.SuzBtVG

end
