module

public import Certificates.Kernel.SporSch.PairJ3.C81Base
import CFSG.Certificates.Kernel.Common.Harness
import Mathlib.Tactic

public section

set_option maxRecDepth 400000
set_option maxHeartbeats 100000

namespace CertificateChecks.KernelSporSch.PJ3C81

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.SporSch CFSG.Certificates CFSG.Certificates.Native
open CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.Sporadic.Schreier
open CFSG.Sporadic.Schreier.PairNative CertificateChecks.KernelSporSch
open CertificateChecks.KernelSporSch.PJ3Count CFSG.Sporadic.SmallOddCore Subgroup

noncomputable def eS (i : Nat) : Equiv.Perm (Fin 6156) := E (C81D.SN i) * U ^ (C81D.SB i)

noncomputable abbrev G (j : Nat) : Equiv.Perm (Fin 6156) := Tb (j + 1)

noncomputable abbrev Ssub : Subgroup (Equiv.Perm (Fin 6156)) :=
  closure (tp 6156 '' {x | x ∈ j3SylowGenTbls.toArray})

theorem blt_iff {a b : Nat} (h : Nat.blt a b = true) : a < b := by simpa [Nat.blt_eq] using h

theorem sRow {i : Nat} (hi : i < 256) : sAt i = true := by
  have h0 : allBlk (Nat.mul (Nat.add (Nat.mul (i / 128) 2) (i / 64 % 2)) 64) sAt 64 = true :=
    sB_all (i / 128) (by omega : i / 128 < 2) (i / 64 % 2) (by omega : i / 64 % 2 < 2)
  have h := allBlk_spec h0 (i % 64) (by omega)
  have e : Nat.add (Nat.mul (Nat.add (Nat.mul (i / 128) 2) (i / 64 % 2)) 64) (i % 64) = i := by
    change (i / 128 * 2 + i / 64 % 2) * 64 + i % 64 = i
    omega
  rwa [e] at h

theorem sParts {i : Nat} (hi : i < 256) : nfValidK 4 PJ3.LR (C81D.SN i) = true ∧ C81D.SB i < 2 ∧
    (i = 0 → C81D.SB 0 = 0 ∧ eqOnL bs (nfp (C81D.SN 0)) (fun x => x) = true) ∧
    (i ≠ 0 → C81D.SP i < i ∧ C81D.SG i < 8 ∧ eqProd i (C81D.SG i) (C81D.SP i) = true) ∧
    (∀ j < 8, C81D.SM (Nat.add (Nat.mul i 8) j) < 256 ∧
      eqProd (C81D.SM (Nat.add (Nat.mul i 8) j)) j i = true) ∧
    C81D.SO i < 256 ∧ (i < 255 → sKey (C81D.SO i) < sKey (C81D.SO (Nat.add i 1))) ∧
    (C81D.SB i = 1 → invW i = true) := by
  have h := sRow hi
  unfold sAt at h
  obtain ⟨h1, h⟩ := (bAnd_iff _ _).1 h
  obtain ⟨h2, h⟩ := (bAnd_iff _ _).1 h
  obtain ⟨h3, h⟩ := (bAnd_iff _ _).1 h
  obtain ⟨h4, h⟩ := (bAnd_iff _ _).1 h
  obtain ⟨h5, h⟩ := (bAnd_iff _ _).1 h
  obtain ⟨h6, h7⟩ := (bAnd_iff _ _).1 h
  refine ⟨h1, blt_iff h2, fun h0 => ?_, fun h0 => ?_, fun j hj => ?_, blt_iff h5, fun hl => ?_,
    fun hb => ?_⟩
  · subst h0
    simp only [Nat.beq_refl, bAnd_iff] at h3
    exact ⟨Nat.eq_of_beq_eq_true h3.1, h3.2⟩
  · have e : Nat.beq i 0 = false := by
      cases i with
      | zero => exact absurd rfl h0
      | succ k => rfl
    simp only [e, bAnd_iff] at h3
    exact ⟨blt_iff h3.1, blt_iff h3.2.1, h3.2.2⟩
  · obtain ⟨a, b⟩ := (bAnd_iff _ _).1 (allN_spec h4 j hj)
    exact ⟨blt_iff a, b⟩
  · rw [blt_true hl] at h6
    exact blt_iff h6
  · rw [hb] at h7
    exact h7

theorem gB_lt {j : Nat} (hj : j < 8) : gB j < 2 := by
  interval_cases j <;> decide

theorem bMap_syl {j : Nat} (hj : j < 8) : ∀ y, bMap (12 + j) y = gP j (uP (gB j) y) := by
  intro y
  interval_cases j <;> rfl

theorem G_rep {j : Nat} (hj : j < 8) : RepF 6156 (gP j) (G j) := (rep_T (k := j + 1) (by omega)).1

section J3


theorem eP_rep {i : Nat} (hi : i < 256) : RepF 6156 (eP i) (eS i) :=
  (nfp_rep (sParts hi).1).comp (uP_rep (sParts hi).2.1)

theorem GU_mem {j : Nat} (hj : j < 8) : G j * U ^ gB j ∈ P3 :=
  mem_of_bnd (g := 12 + j) (by omega) ((G_rep hj).comp (uP_rep (gB_lt hj))) (bMap_syl hj)

theorem key_mem {c b : Nat} (hc : c < 2) (hb : b < 2) {p : Equiv.Perm (Fin 6156)} (hp : p ∈ P3) :
    U ^ c * p * U ^ b * U ^ xorB c b ∈ P3 := by
  rcases (by omega : c = 0 ∨ c = 1) with rfl | rfl <;>
    rcases (by omega : b = 0 ∨ b = 1) with rfl | rfl
  · simpa [xorB] using hp
  · have e : xorB 0 1 = 1 := rfl
    rw [e, pow_zero, one_mul, mul_assoc, pow_one, U2, mul_one]
    exact hp
  · have e : xorB 1 0 = 1 := rfl
    rw [e, pow_zero, mul_one, pow_one]
    exact conjU_mem hp
  · have e : xorB 1 1 = 0 := rfl
    rw [e, pow_zero, mul_one, pow_one]
    exact conjU_mem hp

theorem eqProd_sound {m j i : Nat} (hm : m < 256) (hi : i < 256) (hj : j < 8)
    (h : eqProd m j i = true) : eS m = G j * eS i := by
  obtain ⟨hbit, heq⟩ := (bAnd_iff _ _).1 h
  have hbm := (sParts hm).2.1
  have hbi := (sParts hi).2.1
  have hc := gB_lt hj
  have hb' : C81D.SB m = xorB (gB j) (C81D.SB i) := Nat.eq_of_beq_eq_true hbit
  have hEi : E (C81D.SN i) ∈ P3 := E_mem (sParts hi).1
  have hX : G j * eS i * U ^ C81D.SB m ∈ P3 := by
    have e : G j * eS i * U ^ C81D.SB m = (G j * U ^ gB j) *
        (U ^ gB j * E (C81D.SN i) * U ^ C81D.SB i * U ^ xorB (gB j) (C81D.SB i)) := by
      rw [hb', eS]
      have h2 := Upow2 hc
      calc G j * (E (C81D.SN i) * U ^ C81D.SB i) * U ^ xorB (gB j) (C81D.SB i)
          = G j * (U ^ gB j * U ^ gB j) * E (C81D.SN i) * U ^ C81D.SB i *
              U ^ xorB (gB j) (C81D.SB i) := by rw [h2]; group
        _ = _ := by group
    rw [e]
    exact P3.mul_mem (GU_mem hj) (key_mem hc hbi hEi)
  have hrep : RepF 6156 (fun b => gP j (eP i (uP (C81D.SB m) b))) (G j * eS i * U ^ C81D.SB m) :=
    ((G_rep hj).comp (eP_rep hi)).comp (uP_rep hbm)
  have hE := eq_of_eqOnL hH (nfp_rep (sParts hm).1) hrep (E_mem (sParts hm).1) hX heq
  rw [eS, hE, mul_assoc, Upow2 hbm, mul_one]

theorem eS_zero : eS 0 = 1 := by
  obtain ⟨hb, he⟩ := (sParts (i := 0) (by norm_num)).2.2.1 rfl
  have h1 := eq_of_eqOnL hH (nfp_rep (sParts (i := 0) (by norm_num)).1) RepF.one
    (E_mem (sParts (i := 0) (by norm_num)).1) P3.one_mem he
  rw [eS, h1, hb, pow_zero, mul_one]

theorem G_mem {j : Nat} (hj : j < 8) : G j ∈ Ssub := by
  refine subset_closure ⟨j3CentTbl (j + 1), ?_, rfl⟩
  change j3CentTbl (j + 1) ∈ j3SylowGenTbls.toArray
  rw [List.mem_toArray, j3SylowGenTbls, List.mem_map]
  exact ⟨j, List.mem_range.2 hj, rfl⟩

theorem eS_mem : ∀ i < 256, eS i ∈ Ssub := by
  intro i
  induction i using Nat.strong_induction_on with
  | _ i ih =>
    intro hi
    rcases Nat.eq_zero_or_pos i with rfl | h0
    · rw [eS_zero]
      exact Ssub.one_mem
    · obtain ⟨hp, hg, he⟩ := (sParts hi).2.2.2.1 (by omega)
      rw [eqProd_sound hi (by omega) hg he]
      exact Ssub.mul_mem (G_mem hg) (ih _ hp (by omega))

theorem gen_eq {g : Equiv.Perm (Fin 6156)} (hg : g ∈ tp 6156 '' {x | x ∈ j3SylowGenTbls.toArray}) :
    ∃ j < 8, g = G j := by
  obtain ⟨x, hx, rfl⟩ := hg
  change x ∈ j3SylowGenTbls.toArray at hx
  rw [List.mem_toArray, j3SylowGenTbls, List.mem_map] at hx
  obtain ⟨j, hj, rfl⟩ := hx
  exact ⟨j, List.mem_range.1 hj, rfl⟩

theorem mem_eS : ∀ x ∈ Ssub, ∃ i < 256, x = eS i := by
  refine PJ3C81.closure_subset_of_mul_left (T := {x | ∃ i < 256, x = eS i}) ⟨0, by norm_num,
    eS_zero.symm⟩ ?_
  rintro g hg y ⟨i, hi, rfl⟩
  obtain ⟨j, hj, rfl⟩ := gen_eq hg
  obtain ⟨hm, he⟩ := (sParts hi).2.2.2.2.1 j hj
  exact ⟨_, hm, (eqProd_sound hm hi hj he).symm⟩

theorem eS_P {i : Nat} (hi : i < 256) : eS i ∈ P3 ↔ C81D.SB i = 0 := by
  have hE := E_mem (sParts hi).1
  constructor
  · intro h
    rcases (by have := (sParts hi).2.1; omega : C81D.SB i = 0 ∨ C81D.SB i = 1) with h0 | h1
    · exact h0
    · exfalso
      rw [eS, h1, pow_one] at h
      exact U_not (by simpa using P3.mul_mem (P3.inv_mem hE) h)
  · intro h0
    rw [eS, h0, pow_zero, mul_one]
    exact hE

theorem sKey_eq {i i' : Nat} (hi : i < 256) (hi' : i' < 256) (h : eS i = eS i') :
    sKey i = sKey i' := by
  have hb : C81D.SB i = C81D.SB i' := by
    have h1 := (sParts hi).2.1
    have h2 := (sParts hi').2.1
    have e1 := eS_P hi
    have e2 := eS_P hi'
    rw [h] at e1
    have h3 : C81D.SB i = 0 ↔ C81D.SB i' = 0 := e1.symm.trans e2
    by_cases h4 : C81D.SB i = 0
    · rw [h4, h3.1 h4]
    · have h5 : C81D.SB i' ≠ 0 := fun h5 => h4 (h3.2 h5)
      omega
  have hE : E (C81D.SN i) = E (C81D.SN i') := by
    have e1 : E (C81D.SN i) = eS i * U ^ C81D.SB i := by rw [eS, mul_assoc, Upow2 (sParts hi).2.1, mul_one]
    have e2 : E (C81D.SN i') = eS i' * U ^ C81D.SB i' := by
      rw [eS, mul_assoc, Upow2 (sParts hi').2.1, mul_one]
    rw [e1, e2, h, hb]
  have hk : keyL 6156 (nfp (C81D.SN i)) bs = keyL 6156 (nfp (C81D.SN i')) bs :=
    keyL_congr 6156 fun b hb' => (nfp_rep (sParts hi).1 b (hbs b hb')).trans
      ((congrArg (fun g : Equiv.Perm (Fin 6156) => (g ⟨b, hbs b hb'⟩ : ℕ)) hE).trans
        (nfp_rep (sParts hi').1 b (hbs b hb')).symm)
  unfold sKey
  rw [hb, hk]

theorem SO_mono : ∀ k l, k < l → l < 256 → sKey (C81D.SO k) < sKey (C81D.SO l) := by
  intro k l hkl hl
  induction l with
  | zero => omega
  | succ l ih =>
    have hs := (sParts (i := l) (by omega)).2.2.2.2.2.2.1 (by omega)
    rcases Nat.lt_succ_iff_lt_or_eq.1 hkl with h | h
    · exact lt_trans (ih h (by omega)) hs
    · subst h
      exact hs

theorem card_S : Nat.card Ssub = 256 := by
  apply le_antisymm
  · let f : Fin 256 → Ssub := fun i => ⟨eS i, eS_mem i i.2⟩
    have hf : Function.Surjective f := by
      rintro ⟨x, hx⟩
      obtain ⟨i, hi, rfl⟩ := mem_eS x hx
      exact ⟨⟨i, hi⟩, rfl⟩
    have := Nat.card_le_card_of_surjective f hf
    simpa using this
  · let f : Fin 256 → Ssub := fun k => ⟨eS (C81D.SO k), eS_mem _ (sParts k.2).2.2.2.2.2.1⟩
    have hf : Function.Injective f := by
      intro a b hab
      have h := sKey_eq (sParts a.2).2.2.2.2.2.1 (sParts b.2).2.2.2.2.2.1
        (congrArg Subtype.val hab)
      by_contra hne
      rcases Nat.lt_or_gt_of_ne (Fin.val_ne_of_ne hne) with hlt | hlt
      · exact absurd h (SO_mono _ _ hlt b.2).ne
      · exact absurd h (SO_mono _ _ hlt a.2).ne'
    have := Nat.card_le_card_of_injective f hf
    simpa using this

theorem eS_R {i : Nat} (hi : i < 256) : eS i ∈ j3P ⊔ zpowers U := by
  refine mul_mem (mem_sup_left ?_) (mem_sup_right (pow_mem (mem_zpowers U) _))
  rw [P_eq3]
  exact E_mem (sParts hi).1

theorem S_le : Ssub ≤ j3P ⊔ zpowers U := by
  intro x hx
  obtain ⟨i, hi, rfl⟩ := mem_eS x hx
  exact eS_R hi

theorem T21U : Tb 21 * U ∈ P3 :=
  mem_of_bnd (g := 6) (by norm_num) ((rep_T (k := 21) (by norm_num)).1.comp rep0) fun _ => rfl

theorem outer_conj {s : Equiv.Perm (Fin 6156)} (hs : s ∈ Ssub) (hsP : s ∉ P3) (hs2 : s * s = 1) :
    ∃ c ∈ P3, s = c * Tb 21 * c⁻¹ := by
  obtain ⟨i, hi, rfl⟩ := mem_eS s hs
  have hb : C81D.SB i = 1 := by
    have := (sParts hi).2.1
    have h0 := (eS_P hi).not.1 hsP
    omega
  have hw := (sParts hi).2.2.2.2.2.2.2 hb
  unfold invW at hw
  by_cases h1 : C81D.SW i = 1
  · rw [h1] at hw
    have hsq : eqOnL bs (fun x => eP i (eP i x)) (fun x => x) = true :=
      eqOnL_of_eq hbs ((eP_rep hi).comp (eP_rep hi)) (hs2 ▸ RepF.one)
    rw [hsq] at hw
    have hf : false = true := hw
    exact absurd hf Bool.false_ne_true
  · have e1 : Nat.beq (C81D.SW i) 1 = false := by
      cases h : Nat.beq (C81D.SW i) 1
      · rfl
      · exact absurd (Nat.eq_of_beq_eq_true h) h1
    rw [e1] at hw
    have hw' : bAnd(Nat.beq (C81D.SW i) 2, bAnd(nfValidK 4 PJ3.LR (C81D.SX i),
        eqOnL bs (fun x => eP i (nfp (C81D.SX i) (cP 0 x)))
          (fun x => nfp (C81D.SX i) (cP 21 (cP 0 x))))) = true := hw
    obtain ⟨-, hw⟩ := (bAnd_iff _ _).1 hw'
    obtain ⟨hv, heq⟩ := (bAnd_iff _ _).1 hw
    have hc := E_mem hv
    have hL : eS i * E (C81D.SX i) * U ∈ P3 := by
      rw [eS, hb, pow_one, mul_assoc, mul_assoc]
      exact P3.mul_mem (E_mem (sParts hi).1) (by rw [← mul_assoc]; exact conjU_mem hc)
    have hR : E (C81D.SX i) * Tb 21 * U ∈ P3 := by
      rw [mul_assoc]
      exact P3.mul_mem hc T21U
    have h := eq_of_eqOnL hH (((eP_rep hi).comp (nfp_rep hv)).comp rep0)
      (((nfp_rep hv).comp (rep_T (k := 21) (by norm_num)).1).comp rep0) hL hR heq
    refine ⟨E (C81D.SX i), hc, ?_⟩
    have h' : eS i * E (C81D.SX i) = E (C81D.SX i) * Tb 21 := mul_right_cancel h
    rw [← h', mul_inv_cancel_right]

end J3

end CertificateChecks.KernelSporSch.PJ3C81

end
