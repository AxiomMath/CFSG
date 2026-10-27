module

public import Certificates.Kernel.SporSch.PairJ3.C66Forest
public import Certificates.Kernel.SporSch.PairJ3.C66Roots
public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87F3At
public import Certificates.Data.Odd87F3J3
public import CFSG.Sporadic.Schreier.J4SSylowBase

public section

set_option maxRecDepth 400000
set_option maxHeartbeats 400000

namespace CertificateChecks.KernelSporSch.PJ3C66

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.SporSch CFSG.Certificates CFSG.Certificates.Native
open CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.Sporadic.Schreier
open CFSG.Sporadic.Schreier.PairNative CertificateChecks.KernelSporSch
open CertificateChecks.KernelSporSch.PJ3Count CertificateChecks.KernelSporSch.PJ3C81
open CFSG.Sporadic.SmallOddCore Subgroup CFSG.GH74.GLS.Stage2.Signalizer.Odd87

noncomputable abbrev wE (B : Nat) (L : List Nat) : Equiv.Perm (Fin 6156) :=
  (L.map fun l => Tb (B + l)).prod

theorem wP_rep {r B : Nat} (hB : gBase r = B) :
    ∀ {L : List Nat}, (∀ l ∈ L, B + l < 31) →
      RepF 6156 (wP r L) (wE B L) ∧ RepF 6156 (wI r L) (wE B L)⁻¹
  | [], _ => ⟨RepF.one.congr (by simp only [wE, List.map_nil, List.prod_nil]),
      RepF.one.congr (by simp only [wE, List.map_nil, List.prod_nil, inv_one])⟩
  | l :: L, hL => by
    have ih := wP_rep hB (L := L) fun l' hl' => hL l' (List.mem_cons_of_mem _ hl')
    have hk := hL l List.mem_cons_self
    have e1 : ∀ y, hP r l y = cP (B + l) y := fun y => by
      unfold hP
      rw [hB]
      rfl
    have e2 : ∀ y, hI r l y = cI (B + l) y := fun y => by
      unfold hI
      rw [hB]
      rfl
    have e3 : wE B (l :: L) = Tb (B + l) * wE B L := by
      simp only [wE, List.map_cons, List.prod_cons]
    constructor
    · intro y hy
      change hP r l (wP r L y) = _
      rw [e1, e3]
      exact ((rep_T hk).1.comp ih.1) y hy
    · intro y hy
      change wI r L (hI r l y) = _
      rw [e2, e3, mul_inv_rev]
      exact (ih.2.comp (rep_T hk).2) y hy

theorem oddAll_mem {r : Nat} : ∀ {L : List (List Nat × Nat)},
    List.rec (motive := fun _ => Bool) true (fun e _ ih => bAnd(oddEl r e, ih)) L = true →
      ∀ e ∈ L, oddEl r e = true
  | [], _ => fun _ he => absurd he List.not_mem_nil
  | e :: L, h => by
    obtain ⟨h1, h2⟩ := (bAnd_iff _ _).1 h
    intro e' he'
    rcases List.mem_cons.1 he' with rfl | he'
    · exact h1
    · exact oddAll_mem h2 e' he'

theorem rootsF : allN 27 rootI = true ∧ allN 22 rootO = true ∧ oddAllB 0 = true ∧
    oddAllB 1 = true := by
  have h := roots
  unfold rootsB at h
  simpa only [bAnd_iff] using h

section J3


theorem odd_facts {r B : Nat} (hB : gBase r = B) {u : Equiv.Perm (Fin 6156)} {K : Subgroup _}
    (hK : K ≤ j3P ⊓ centralizer ({u} : Set (Equiv.Perm (Fin 6156))))
    (hgen : ∀ e ∈ oddL r, ∀ l ∈ e.1, B + l < 31 ∧ Tb (B + l) ∈ K) (hall : oddAllB r = true) :
    ∀ i < (oddL r).length, ∃ c : Equiv.Perm (Fin 6156), c ∈ j3P ∧ u * c = c * u ∧
      Odd (orderOf c) ∧ RepF 6156 (wP r ((oddL r).getD i ([], 1)).1) c ∧
      RepF 6156 (wI r ((oddL r).getD i ([], 1)).1) c⁻¹ := by
  intro i hi
  have hmem : (oddL r).getD i ([], 1) ∈ oddL r := by
    rw [List.getD_eq_getElem _ _ hi]
    exact List.getElem_mem hi
  set e := (oddL r).getD i ([], 1)
  have hg := hgen e hmem
  have hR := wP_rep hB fun l hl => (hg l hl).1
  have hcK : wE B e.1 ∈ K := Subgroup.list_prod_mem K fun x hx => by
    obtain ⟨l, hl, rfl⟩ := List.mem_map.1 hx
    exact (hg l hl).2
  obtain ⟨hcP, hcC⟩ := Subgroup.mem_inf.1 (hK hcK)
  have hodd := oddAll_mem hall e hmem
  unfold oddEl at hodd
  obtain ⟨h1, h2⟩ := (bAnd_iff _ _).1 hodd
  have hpow : wE B e.1 ^ e.2 = 1 :=
    (fixL_iff hH hbs (hR.1.powF e.2) (P3.pow_mem (P_eq3 ▸ hcP) _)).1 h2
  refine ⟨wE B e.1, hcP, (mem_centralizer_singleton_iff.1 hcC).symm, ?_, hR.1, hR.2⟩
  exact Odd.of_dvd_nat (Nat.odd_iff.2 (Nat.eq_of_beq_eq_true h1)) (orderOf_dvd_of_pow_eq_one hpow)

theorem prQ_prime {q : Nat} (hq : q < 4) : (prQ q).Prime := by
  interval_cases q <;> norm_num [prQ]

theorem pnQ_pow {q : Nat} (hq : q < 4) :
    ∃ N, pnQ q = prQ q ^ N ∧ ¬ prQ q ^ (N + 1) ∣ Nat.card j3P := by
  rw [card_j3P]
  interval_cases q
  · exact ⟨5, rfl, by norm_num [prQ]⟩
  · exact ⟨1, rfl, by norm_num [prQ]⟩
  · exact ⟨1, rfl, by norm_num [prQ]⟩
  · exact ⟨1, rfl, by norm_num [prQ]⟩

theorem not_pGroup_of_pow {M : Type*} [Group M] {G N : Subgroup M} {p k : ℕ} [Fact p.Prime]
    (hk : ¬ p ^ (k + 1) ∣ Nat.card G) (hN : IsPGroup p ↥N) {z : M} (hzN : z ∈ N) (hzG : z ∈ G)
    (hz : z ^ (p ^ k) ≠ 1) : False := by
  obtain ⟨j, hj⟩ := (IsPGroup.iff_orderOf.mp hN) ⟨z, hzN⟩
  have hj' : orderOf z = p ^ j := by rwa [Subgroup.orderOf_mk] at hj
  have hdvd : orderOf z ∣ Nat.card G := by
    have := orderOf_dvd_natCard (⟨z, hzG⟩ : ↥G)
    rwa [Subgroup.orderOf_mk] at this
  rw [hj'] at hdvd
  have hjk : j ≤ k := by
    by_contra hlt
    exact hk ((pow_dvd_pow p (by omega : k + 1 ≤ j)).trans hdvd)
  apply hz
  rw [← orderOf_dvd_iff_pow_eq_one, hj']
  exact pow_dvd_pow p hjk

theorem bFalse {a b : Nat} (h : bIf(Nat.beq a b, false, true) = true) : a ≠ b := fun e => by
  rw [e, Nat.beq_refl] at h
  exact Bool.noConfusion h

theorem wit_sound {r q t m a : Nat} {X : Nat → Nat} {u x : Equiv.Perm (Fin 6156)} (hq : q < 4)
    (hX : RepF 6156 X x) (hx : x ∈ P3)
    (hodd : ∀ i < (oddL r).length, ∃ c : Equiv.Perm (Fin 6156), c ∈ j3P ∧ u * c = c * u ∧
      Odd (orderOf c) ∧ RepF 6156 (wP r ((oddL r).getD i ([], 1)).1) c ∧
      RepF 6156 (wI r ((oddL r).getD i ([], 1)).1) c⁻¹)
    (h : witT r q t m a X = true) : F3SAt j3P u x (prQ q) := by
  intro hxG hxo _ hpg
  unfold witT at h
  by_cases ht0 : t = 0
  · subst ht0
    rw [Nat.beq_refl] at h
    obtain ⟨h1, h2⟩ := (bAnd_iff _ _).1 h
    have hm : x ^ m = 1 := (fixL_iff hH hbs (hX.powF m) (P3.pow_mem hx m)).1 h2
    have hdvd : prQ q ∣ m := hxo ▸ orderOf_dvd_of_pow_eq_one hm
    exact bFalse h1 (Nat.mod_eq_zero_of_dvd hdvd)
  have e0 : Nat.beq t 0 = false := by
    cases h' : Nat.beq t 0
    · rfl
    · exact absurd (Nat.eq_of_beq_eq_true h') ht0
  rw [e0] at h
  obtain ⟨ha, h⟩ := (bAnd_iff _ _).1 h
  have ha' := ltB ha
  by_cases ht1 : t = 1
  · subst ht1
    rw [Nat.beq_refl] at h
    have hpow : x ^ prQ q = 1 := hxo ▸ pow_orderOf_eq_one x
    refine bFalse h ?_
    rw [(hX.powF _) a ha', hpow]
    rfl
  have e1 : Nat.beq t 1 = false := by
    cases h' : Nat.beq t 1
    · rfl
    · exact absurd (Nat.eq_of_beq_eq_true h') ht1
  rw [e1] at h
  obtain ⟨-, h⟩ := (bAnd_iff _ _).1 h
  obtain ⟨hm, h3⟩ := (bAnd_iff _ _).1 h
  obtain ⟨c, hcG, hcu, hco, hcP, hcI⟩ := hodd m (ltB hm)
  have hy : RepF 6156 (yW r m X) (x * (c * x * c⁻¹)) :=
    (hX.comp (hcP.comp (hX.comp hcI))).congr (by group)
  have : Fact (prQ q).Prime := ⟨prQ_prime hq⟩
  obtain ⟨N, hN, hk⟩ := pnQ_pow hq
  have hcS : c ∈ closure {y : Equiv.Perm (Fin 6156) | y ∈ j3P ∧ u * y = y * u ∧
      Odd (orderOf y)} := subset_closure ⟨hcG, hcu, hco⟩
  refine not_pGroup_of_pow hk hpg (z := x * (c * x * c⁻¹))
    (mul_mem (subset_closure ⟨1, one_mem _, by group⟩) (subset_closure ⟨c, hcS, rfl⟩))
    (j3P.mul_mem hxG (j3P.mul_mem (j3P.mul_mem hcG hxG) (j3P.inv_mem hcG))) fun h1 => ?_
  refine bFalse h3 ?_
  rw [(hy.powF _) a ha', hN, h1]
  rfl

theorem witOK_eq {r q W : Nat} {X : Nat → Nat} (h : witOK r q W X = true) :
    witT r q (Nat.shiftRight W 28) (Nat.land (Nat.shiftRight W 16) 4095) (Nat.land W 65535) X =
      true := h

theorem t9inv : (Tb 9)⁻¹ = Tb 9 := by
  have h := pow_orderOf_eq_one (Tb 9)
  rw [t9_ord, sq] at h
  exact inv_eq_of_mul_eq_one_right h

theorem hodd0 : ∀ i < (oddL 0).length, ∃ c : Equiv.Perm (Fin 6156), c ∈ j3P ∧
    Tb 9 * c = c * Tb 9 ∧ Odd (orderOf c) ∧ RepF 6156 (wP 0 ((oddL 0).getD i ([], 1)).1) c ∧
    RepF 6156 (wI 0 ((oddL 0).getD i ([], 1)).1) c⁻¹ :=
  odd_facts (r := 0) (B := 10) rfl K1_le (fun e he l hl => by
    have hl5 : l < 5 := by
      simp only [oddL, oddI, Nat.beq_refl, List.mem_cons, List.not_mem_nil, or_false] at he
      rcases he with rfl | rfl | rfl <;> simp at hl <;> omega
    exact ⟨by omega, g1_K hl5⟩) rootsF.2.2.1

theorem root_atI {k : Nat} (hk : k < 27) {q : Nat} (hq : q < 4) :
    F3SAt j3P (Tb 9) (Tb 9 * xE (C66D.RI k)) (prQ q) := by
  have h := allN_spec rootsF.1 k hk
  unfold rootI at h
  obtain ⟨h1, h2⟩ := (bAnd_iff _ _).1 h
  have hR := ltB h1
  exact wit_sound hq (r9.comp (sI_rep hR)) (P3.mul_mem t9_mem (xE_mem hR)) hodd0
    (witOK_eq (allN_spec h2 q hq))

theorem f3S_inner {q : Nat} (hq : q < 4) : F3S j3P (Tb 9) (prQ q) := by
  refine F3S_of_at fun x => ?_
  intro hx hxo hxu hpg
  have hxP := ofJ hx
  have h2 : Tb 9 * Tb 9 = 1 := by
    have h := pow_orderOf_eq_one (Tb 9)
    rwa [t9_ord, sq] at h
  have hsP : Tb 9 * x ∈ P3 := P3.mul_mem t9_mem hxP
  have hs2 : (Tb 9 * x) * (Tb 9 * x) = 1 := by
    have h1 : Tb 9 * x * Tb 9 = x⁻¹ := by rwa [t9inv] at hxu
    calc (Tb 9 * x) * (Tb 9 * x) = (Tb 9 * x * Tb 9) * x := by group
      _ = 1 := by rw [h1]; group
  have hs1 : Tb 9 * x ≠ 1 := by
    intro h1
    have hx9 : x = Tb 9 := by
      rw [← t9inv]
      exact eq_inv_of_mul_eq_one_right h1
    have : orderOf x = 2 := by rw [hx9, t9_ord]
    rw [hxo] at this
    have h3 : prQ q ≠ 2 := by interval_cases q <;> simp [prQ]
    exact h3 this
  have hso : orderOf (mk (Tb 9 * x) hsP) = 2 := by
    rw [Subgroup.orderOf_mk]
    exact orderOf_eq_prime (by rw [sq]; exact hs2) hs1
  obtain ⟨j, hj, hjs⟩ := rec_cover hso
  obtain ⟨k, hk, c, hc, he⟩ := forestI _ j rfl hj
  obtain ⟨hcP, hcC⟩ := Subgroup.mem_inf.1 (K1_le hc)
  have hcu : Tb 9 * c = c * Tb 9 := (mem_centralizer_singleton_iff.1 hcC).symm
  have hxe : x = c * (Tb 9 * xE (C66D.RI k)) * c⁻¹ := by
    have e1 : x = Tb 9 * (Tb 9 * x) := by rw [← mul_assoc, h2, one_mul]
    have e2 : (Tb 9 * x) = c * xE (C66D.RI k) * c⁻¹ := by
      rw [← he]
      exact hjs.symm
    rw [e1, e2]
    calc Tb 9 * (c * xE (C66D.RI k) * c⁻¹) = (Tb 9 * c) * xE (C66D.RI k) * c⁻¹ := by group
      _ = (c * Tb 9) * xE (C66D.RI k) * c⁻¹ := by rw [hcu]
      _ = c * (Tb 9 * xE (C66D.RI k)) * c⁻¹ := by group
  subst hxe
  exact (root_atI hk hq).conj hcP hcu hx hxo hxu hpg

theorem hodd1 : ∀ i < (oddL 1).length, ∃ c : Equiv.Perm (Fin 6156), c ∈ j3P ∧
    Tb 21 * c = c * Tb 21 ∧ Odd (orderOf c) ∧ RepF 6156 (wP 1 ((oddL 1).getD i ([], 1)).1) c ∧
    RepF 6156 (wI 1 ((oddL 1).getD i ([], 1)).1) c⁻¹ :=
  odd_facts (r := 1) (B := 22) rfl K2_le (fun e he l hl => by
    have hl3 : l < 3 := by
      have e1 : oddL 1 = oddO := rfl
      simp only [e1, oddO, List.mem_cons, List.not_mem_nil, or_false] at he
      rcases he with rfl | rfl <;> simp at hl <;> omega
    exact ⟨by omega, g2_K hl3⟩) rootsF.2.2.2

theorem sOE_mem {j : Nat} (hj : j < 20520) : Tb 21 * sOE j ∈ P3 := by
  have hE := E_mem (clRow hj).1
  have e : Tb 21 * sOE j = (Tb 21 * E (C81D.CL j) * Tb 21) * (E (C81D.CL j))⁻¹ := by
    change Tb 21 * (E (C81D.CL j) * Tb 21 * (E (C81D.CL j))⁻¹) = _
    group
  rw [e]
  exact P3.mul_mem (tpt_mem hE) (P3.inv_mem hE)

theorem root_atO {k : Nat} (hk : k < 22) {q : Nat} (hq : q < 4) :
    F3SAt j3P (Tb 21) (Tb 21 * sOE (C66D.RO k)) (prQ q) := by
  have h := allN_spec rootsF.2.1 k hk
  unfold rootO at h
  obtain ⟨h1, h2⟩ := (bAnd_iff _ _).1 h
  have hR := ltB h1
  exact wit_sound hq (r21.comp (sO_rep hR)) (sOE_mem hR) hodd1 (witOK_eq (allN_spec h2 q hq))

theorem f3S_outer {q : Nat} (hq : q < 4) : F3S j3P (Tb 21) (prQ q) := by
  refine F3S_of_at fun x => ?_
  intro hx hxo hxu hpg
  have hxP := ofJ hx
  have hs2 : (Tb 21 * x) * (Tb 21 * x) = 1 := by
    have h1 : Tb 21 * x * Tb 21 = x⁻¹ := by rwa [T21inv] at hxu
    calc (Tb 21 * x) * (Tb 21 * x) = (Tb 21 * x * Tb 21) * x := by group
      _ = 1 := by rw [h1]; group
  have hsP : Tb 21 * x ∉ P3 := fun h => T21_not (by
    have := P3.mul_mem h (P3.inv_mem hxP)
    rwa [mul_inv_cancel_right] at this)
  have hs1 : Tb 21 * x ≠ 1 := fun h => hsP (h ▸ P3.one_mem)
  have hso : orderOf (Tb 21 * x) = 2 := orderOf_eq_prime (by rw [sq]; exact hs2) hs1
  have hsR : Tb 21 * x ∈ j3P ⊔ zpowers U := by
    refine (R_mem _).2 (Or.inr (toJ ?_))
    have e : Tb 21 * x * U = (Tb 21 * U) * (U * x * U) := by
      calc Tb 21 * x * U = Tb 21 * (U * U) * x * U := by rw [U2, mul_one]
        _ = _ := by group
    rw [e]
    exact P3.mul_mem T21U (conjU_mem hxP)
  obtain ⟨r, hr, g, hg, hrg⟩ := cover _ hsR hso
  simp only [j3Rows, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · exact absurd (by rw [hrg]; exact P3.mul_mem (P3.mul_mem (ofJ hg) t9_mem) (P3.inv_mem (ofJ hg)))
      hsP
  obtain ⟨j, hj, hjs⟩ := cl_cover (s := Tb 21 * x) ⟨g, hg, hrg⟩
  obtain ⟨k, hk, c, hc, he⟩ := forestO _ j rfl hj
  obtain ⟨hcP, hcC⟩ := Subgroup.mem_inf.1 (K2_le hc)
  have hcu : Tb 21 * c = c * Tb 21 := (mem_centralizer_singleton_iff.1 hcC).symm
  have hxe : x = c * (Tb 21 * sOE (C66D.RO k)) * c⁻¹ := by
    have e1 : x = Tb 21 * (Tb 21 * x) := (TT x).symm
    have e2 : (Tb 21 * x) = c * sOE (C66D.RO k) * c⁻¹ := by
      rw [← he]
      exact hjs.symm
    rw [e1, e2]
    calc Tb 21 * (c * sOE (C66D.RO k) * c⁻¹) = (Tb 21 * c) * sOE (C66D.RO k) * c⁻¹ := by group
      _ = (c * Tb 21) * sOE (C66D.RO k) * c⁻¹ := by rw [hcu]
      _ = c * (Tb 21 * sOE (C66D.RO k)) * c⁻¹ := by group
  subst hxe
  exact (root_atO hk hq).conj hcP hcu hx hxo hxu hpg

theorem f3S_rows {u : Equiv.Perm (Fin 6156)} (h : ∀ q < 4, F3S j3P u (prQ q)) :
    ∀ p ∈ [3, 5, 17, 19], F3S j3P u p := by
  intro p hp
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl
  · exact h 0 (by norm_num)
  · exact h 1 (by norm_num)
  · exact h 2 (by norm_num)
  · exact h 3 (by norm_num)

theorem facts :
    (∀ p ∈ [3, 5, 17, 19], F3S j3P (tp 6156 (Certificates.Odd87F3.J3.rowAt 0).rep) p) ∧
    (∀ p ∈ [3, 5, 17, 19], F3S j3P (tp 6156 (Certificates.Odd87F3.J3.rowAt 1).rep) p) :=
  ⟨f3S_rows fun _ hq => f3S_inner hq, f3S_rows fun _ hq => f3S_outer hq⟩

end J3

end CertificateChecks.KernelSporSch.PJ3C66

end
