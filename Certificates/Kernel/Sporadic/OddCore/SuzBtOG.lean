
module

public import Certificates.Kernel.Sporadic.OddCore.SuzBtNG
public import Certificates.Kernel.Sporadic.OddCore.SuzBtIG
public import Certificates.Kernel.Sporadic.OddCore.SuzBtOF
public import Certificates.Kernel.Sporadic.OddCore.SuzTwCF
public import CFSG.Certificates.Kernel.Spor.BTupOSound
public import CFSG.Sporadic.SuzRecog.C1ModelBase
import CFSG.Certificates.Kernel.Common.Harness
import CFSG.Certificates.Kernel.Spor.RawOrbEval
import CFSG.Certificates.Kernel.HeFixKFix
import Mathlib.Tactic.Group

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSpor.SuzBtOG

open CFSG.KC.Enum CFSG.KS CFSG.KS.BTup CertificateChecks.KernelSpor
open CFSG.Sporadic.SuzOddCore CFSG.Sporadic.SuzRecog CFSG.Sporadic.SuzRecog.C1Model
open CFSG.Sporadic.SuzRecog.SuzL34Cert CertificateChecks.KernelSpor.SuzC1EG
open CertificateChecks.KernelSpor.SuzBtG CertificateChecks.KernelSpor.SuzBtZG
  CertificateChecks.KernelSpor.SuzBtNG

theorem kBN : allN 2 (fun j => Nat.beq (SuzBtM1O.C j) (decK (nl1Decs.getD j ([], 0)))) = true := by
  quickRfl

theorem exists_of_not_allN_not {n : Nat} {f : Nat → Bool}
    (h : Bool.not (allN n (fun q => Bool.not (f q))) = true) : ∃ q < n, f q = true := by
  by_contra hc
  have hall : allN n (fun q => Bool.not (f q)) = true := CFSG.KS.Raw.Orb.allN_iff.2 fun q hq => by
    cases e : f q
    · rfl
    · exact absurd ⟨q, hq, e⟩ hc
  rw [hall] at h
  exact Bool.false_ne_true h

theorem le_norm_of_gens {n k m : Nat} {cg mg : Nat → Equiv.Perm (Fin n)}
    (h : ∀ j < k, ∀ l < m, (cg j)⁻¹ * mg l * cg j ∈ genSub n m mg) :
    genSub n k cg ≤ Subgroup.normalizer (genSub n m mg : Set (Equiv.Perm (Fin n))) := by
  refine Subgroup.closure_le _ |>.2 ?_
  rintro _ ⟨j, hj, rfl⟩
  refine (Subgroup.inv_mem_iff _).1 (mem_set_normalizer_of_finite (Set.toFinite _) fun x hx => ?_)
  rw [SetLike.mem_coe] at hx ⊢
  rw [inv_inv]
  induction hx using Subgroup.closure_induction with
  | mem y hy =>
    obtain ⟨l, hl, rfl⟩ := hy
    exact h j hj l hl
  | one => simpa using Subgroup.one_mem _
  | mul a b _ _ ha hb =>
    have e : (cg j)⁻¹ * (a * b) * cg j = ((cg j)⁻¹ * a * cg j) * ((cg j)⁻¹ * b * cg j) := by
      group
    rw [e]
    exact Subgroup.mul_mem _ ha hb
  | inv a _ ha =>
    have e : (cg j)⁻¹ * a⁻¹ * cg j = ((cg j)⁻¹ * a * cg j)⁻¹ := by group
    rw [e]
    exact Subgroup.inv_mem _ ha

theorem fixedCard_conj (g x : Equiv.Perm (Fin 1782)) : fixedCard (g * x * g⁻¹) = fixedCard x := by
  unfold fixedCard
  refine Nat.card_congr ⟨fun z => ⟨g⁻¹ z.1, ?_⟩, fun y => ⟨g y.1, ?_⟩, fun z => ?_, fun y => ?_⟩
  · have h : g (x (g⁻¹ z.1)) = z.1 := z.2
    change x (g⁻¹ z.1) = g⁻¹ z.1
    exact Equiv.Perm.eq_inv_iff_eq.2 h
  · have h : x y.1 = y.1 := y.2
    change g (x (g⁻¹ (g y.1))) = g y.1
    rw [Equiv.Perm.inv_def, Equiv.symm_apply_apply, h]
  · exact Subtype.ext (by simp)
  · exact Subtype.ext (by simp)

@[expose] noncomputable def wP : Equiv.Perm (Fin 1782) := permC 1782 w0T

theorem hW : ∀ x : Fin 1782, pg 11 (mask 11) (SuzTwG 6) x = wP x := fun x => by
  rw [← CFSG.KC.HeFixK.unpack_getElem! x.2, ← SuzTwCF.pW0.1]
  exact tabRep_w0.2 x

theorem w_mem : wP ∈ invE 1 := w0_mem_invE

theorem w_sq : wP * wP = 1 := w0_mul_self

theorem hCN : ∀ j < 2, ∀ x : Fin 1782, pg 11 (mask 11) (SuzBtM1O.C j) x = ngp j x :=
  fun j hj x => by
    rw [Nat.eq_of_beq_eq_true (allN_spec kBN j hj)]
    exact hgN hj x

theorem nl1_conj_m1 {j l : Nat} (hj : j < 2) (hl : l < 8) :
    (ngp j)⁻¹ * mgp l * ngp j ∈ genSub 1782 8 mgp := by
  obtain ⟨x, hx, he⟩ := btCj_spec hgM hbM hpM (hCN j hj) (hgM l hl) hbM
    (CFSG.KS.Raw.Orb.allN_iff.1 (CFSG.KS.Raw.Orb.allN_iff.1 SuzBtOF.kCjN j hj) l hl)
  have hc := nl1_le (gp_mem hj)
  have e : ngp j * x = mgp l * ngp j :=
    invE1_ext (Subgroup.mul_mem _ hc (m1_le hx)) (Subgroup.mul_mem _ (m1_le (gp_mem hl)) hc)
      fun t => he t
  rw [mul_assoc, ← e, inv_mul_cancel_left]
  exact hx

theorem nl1_le_norm_m1 :
    genSub 1782 2 ngp ≤ Subgroup.normalizer (genSub 1782 8 mgp : Set (Equiv.Perm (Fin 1782))) :=
  le_norm_of_gens fun _ hj _ hl => nl1_conj_m1 hj hl

theorem w_mem_m1 : wP ∈ genSub 1782 8 mgp := by
  obtain ⟨q, hq, hm⟩ := exists_of_not_allN_not SuzBtOF.kWM
  exact mem_of_btKey m1_le hgM hbM hpM hq w_mem (mov_base hbM hW hm)

theorem w_not_l1 : wP ∉ genSub 1782 4 lgp := by
  intro h
  obtain ⟨p, hp, he⟩ := btKey_cover hgL hbL hpL SuzBtZF.kL1Hd h
  have h1 := CFSG.KS.Raw.Orb.allN_iff.1 SuzBtOF.kWL p hp
  have h2 : btMov 11 (mask 11) 3 (SuzTwG 6) SuzBtL1.B (btKey 33 (mask 33) SuzBtL1.K p) = true :=
    CFSG.KS.Raw.Orb.allN_iff.2 fun t ht => Nat.beq_eq.mpr (by
      rw [he ⟨t, ht⟩, hbL ⟨t, ht⟩, hW])
  rw [h2] at h1
  exact Bool.false_ne_true h1

theorem fixed_w : fixedCard wP = 42 := by
  have hc : btCntN 1782 (fun x => Nat.beq (pg 11 (mask 11) (SuzTwG 6) x) x) = 42 :=
    Nat.beq_eq.mp SuzBtOF.kFx
  have hm : (Finset.univ.filter fun x : Fin 1782 => wP x = x).map Fin.valEmbedding =
      (Finset.range 1782).filter (fun i => Nat.beq (pg 11 (mask 11) (SuzTwG 6) i) i = true) := by
    ext i
    simp only [Finset.mem_map, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_range,
      Fin.valEmbedding_apply]
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact ⟨x.2, Nat.beq_eq.mpr (by rw [hW x, hx])⟩
    · rintro ⟨hi, hb⟩
      refine ⟨⟨i, hi⟩, Fin.ext ?_, rfl⟩
      rw [← hW ⟨i, hi⟩]
      exact Nat.beq_eq.mp hb
  rw [fixedCard_eq_filter, ← Finset.card_map Fin.valEmbedding, hm, ← btCntN_eq, hc]

theorem conj_facts {g : Equiv.Perm (Fin 1782)} (hg : g ∈ genSub 1782 2 ngp) :
    g * wP * g⁻¹ ∈ genSub 1782 8 mgp ∧ g * wP * g⁻¹ * (g * wP * g⁻¹) = 1 ∧
      g * wP * g⁻¹ ≠ 1 ∧ g * wP * g⁻¹ ∉ genSub 1782 4 lgp := by
  have hnL : g ∈ Subgroup.normalizer (genSub 1782 4 lgp : Set (Equiv.Perm (Fin 1782))) := by
    rw [l1_eq]
    exact nl1_le_norm (nl1_eq ▸ hg)
  have hiffL := (Subgroup.mem_normalizer_iff.1 hnL) wP
  refine ⟨((Subgroup.mem_normalizer_iff.1 (nl1_le_norm_m1 hg)) wP).1 w_mem_m1, ?_, ?_,
    fun h => w_not_l1 (hiffL.2 h)⟩
  · have e : g * wP * g⁻¹ * (g * wP * g⁻¹) = g * (wP * wP) * g⁻¹ := by group
    rw [e, w_sq, mul_one, mul_inv_cancel]
  · intro h
    refine w_not_l1 (hiffL.2 ?_)
    rw [h]
    exact Subgroup.one_mem _

theorem hX : ∀ y ∈ genSub 1782 8 mgp, ∀ g ∈ genSub 1782 2 ngp,
    (∀ t, y (c1Base t) = (g * wP * g⁻¹) (c1Base t)) → y = g * wP * g⁻¹ :=
  fun y hy g hg e => invE1_ext (m1_le hy)
    (Subgroup.mul_mem _ (Subgroup.mul_mem _ (nl1_le hg) w_mem) (Subgroup.inv_mem _ (nl1_le hg))) e

theorem card_orb_ge : 288 ≤ Nat.card {x : Equiv.Perm (Fin 1782) |
    ∃ g ∈ genSub 1782 2 ngp, x = g * wP * g⁻¹} := by
  have h := btOc_card hgM hpM hfixM hbM hCN hW SuzBtOF.kPre
    (fun i hi => btOcSl_spec SuzBtOF.kOc (Nat.zero_le _) (by rw [SuzBtF.kCnt] at hi; omega) hi)
    hX (by norm_num)
  rwa [Nat.beq_eq.mp SuzBtOF.kOn] at h

theorem card_orb_le : Nat.card {x : Equiv.Perm (Fin 1782) |
    ∃ g ∈ genSub 1782 2 ngp, x = g * wP * g⁻¹} ≤ 288 := by
  rw [← SuzBtIG.card_inv_m1, ← (show genSub 1782 8 mgp = decSubgroup m1Decs from
    genSub_dec m1Decs), ← l1_eq]
  let φ : {x : Equiv.Perm (Fin 1782) | ∃ g ∈ genSub 1782 2 ngp, x = g * wP * g⁻¹} →
      {x : genSub 1782 8 mgp // x * x = 1 ∧ x ≠ 1 ∧
        ((x : genSub 1782 8 mgp) : Equiv.Perm (Fin 1782)) ∉ genSub 1782 4 lgp} := fun x =>
    ⟨⟨x.1, by
        obtain ⟨g, hg, e⟩ := x.2
        rw [e]
        exact (conj_facts hg).1⟩, by
      obtain ⟨g, hg, e⟩ := x.2
      refine ⟨Subtype.ext ?_, fun h => (conj_facts hg).2.2.1 ?_, ?_⟩
      · change x.1 * x.1 = 1
        rw [e]
        exact (conj_facts hg).2.1
      · rw [← e]
        exact congrArg Subtype.val h
      · change x.1 ∉ genSub 1782 4 lgp
        rw [e]
        exact (conj_facts hg).2.2.2⟩
  exact Nat.card_le_card_of_injective φ fun a b h =>
    Subtype.ext (congrArg (fun y => (y.1 : Equiv.Perm (Fin 1782))) h)

theorem f3Prop : F3Prop := by
  unfold F3Prop
  dsimp only
  rw [← nl1_eq, ← l1_eq]
  refine ⟨le_antisymm card_orb_le card_orb_ge, ?_, ?_, ?_, ?_⟩
  · rintro x ⟨g, hg, rfl⟩
    rw [← (show genSub 1782 8 mgp = decSubgroup m1Decs from genSub_dec m1Decs)]
    exact (conj_facts hg).1
  · rintro x ⟨g, hg, rfl⟩
    exact (conj_facts hg).2.2.2
  · rintro x ⟨g, hg, rfl⟩
    rw [fixedCard_conj]
    exact fixed_w
  · rw [l1_eq]
    exact SuzBtIG.card_inv_m1

end CertificateChecks.KernelSpor.SuzBtOG

end
