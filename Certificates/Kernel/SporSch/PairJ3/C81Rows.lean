module

public import Certificates.Kernel.SporSch.PairJ3.C81Syl
public import Certificates.Kernel.SporSch.PairJ3.C81Cls0
public import Certificates.Kernel.SporSch.PairJ3.C81Cls1
import CFSG.Certificates.Kernel.Common.Harness
import Mathlib.Tactic

public section

set_option maxRecDepth 400000
set_option maxHeartbeats 100000

#kss_b2all CertificateChecks.KernelSporSch.PJ3C81 CertificateChecks.KernelSporSch.PJ3C81.clB 6 6

namespace CertificateChecks.KernelSporSch.PJ3C81

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.SporSch CFSG.Certificates CFSG.Certificates.Native
open CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.Sporadic.Schreier
open CFSG.Sporadic.Schreier.PairNative CertificateChecks.KernelSporSch
open CertificateChecks.KernelSporSch.PJ3Count CFSG.Sporadic.SmallOddCore Subgroup

theorem Tb_def (k : Nat) : Tb k = tp 6156 (j3CentTbl k) := rfl

theorem U_def : tp 6156 j3OuterTbl = U := by
  unfold U Tb j3OuterTbl
  rfl

theorem two_dvd_orderOf {G : Type*} [Group G] {y : G} {m : ℕ} (h1 : y ^ (2 * m) = 1)
    (h2 : y ^ m ≠ 1) : 2 ∣ orderOf y := by
  by_contra h
  have hc : Nat.Coprime (orderOf y) 2 :=
    Nat.coprime_comm.1 ((Nat.Prime.coprime_iff_not_dvd Nat.prime_two).2 h)
  exact h2 (orderOf_dvd_iff_pow_eq_one.1 (hc.dvd_of_dvd_mul_left (orderOf_dvd_of_pow_eq_one h1)))

theorem prime_dvd3 {q p1 p2 p3 e1 e2 e3 : ℕ} (hq : q.Prime) (h1 : p1.Prime) (h2 : p2.Prime)
    (h3 : p3.Prime) (h : q ∣ p1 ^ e1 * p2 ^ e2 * p3 ^ e3) : q = p1 ∨ q = p2 ∨ q = p3 := by
  rcases (Nat.Prime.dvd_mul hq).1 h with h | h
  · rcases (Nat.Prime.dvd_mul hq).1 h with h | h
    · exact Or.inl ((Nat.prime_dvd_prime_iff_eq hq h1).1 (hq.dvd_of_dvd_pow h))
    · exact Or.inr (Or.inl ((Nat.prime_dvd_prime_iff_eq hq h2).1 (hq.dvd_of_dvd_pow h)))
  · exact Or.inr (Or.inr ((Nat.prime_dvd_prime_iff_eq hq h3).1 (hq.dvd_of_dvd_pow h)))

theorem listRec_exists {x : Nat} : ∀ L : List Nat, List.rec (motive := fun _ => Bool) false
    (fun F _ ih => bIf(Nat.beq (nfp F x) x, ih, true)) L = true → ∃ F ∈ L, nfp F x ≠ x
  | [], h => absurd (h : false = true) Bool.false_ne_true
  | F :: L, h => by
    by_cases hF : nfp F x = x
    · have e : Nat.beq (nfp F x) x = true := by
        rw [hF]
        exact Nat.beq_refl x
      have h' : Bool.rec (motive := fun _ => Bool) true (List.rec (motive := fun _ => Bool) false
          (fun F _ ih => bIf(Nat.beq (nfp F x) x, ih, true)) L) (Nat.beq (nfp F x) x) = true := h
      rw [e] at h'
      obtain ⟨G, hG, hne⟩ := listRec_exists L h'
      exact ⟨G, List.mem_cons_of_mem _ hG, hne⟩
    · exact ⟨F, List.mem_cons_self, hF⟩

theorem listRec_all : ∀ L : List Nat, List.rec (motive := fun _ => Bool) true
    (fun F _ ih => bAnd(nfValidK 4 PJ3.LR F, bAnd(Nat.beq (nfp F 0) 0, ih))) L = true →
    ∀ F ∈ L, nfValidK 4 PJ3.LR F = true ∧ nfp F 0 = 0
  | [], _ => fun _ hF => absurd hF (List.not_mem_nil)
  | G :: L, h => by
    obtain ⟨h1, h⟩ := (bAnd_iff _ _).1 h
    obtain ⟨h2, h3⟩ := (bAnd_iff _ _).1 h
    intro F hF
    rcases List.mem_cons.1 hF with rfl | hF
    · exact ⟨h1, Nat.eq_of_beq_eq_true h2⟩
    · exact listRec_all L h3 F hF

theorem oRow1 {k : Nat} (hk : k < 960) : C81D.O1P k < 6156 ∧ C81D.O1Q (C81D.O1P k) = k ∧
    (k = 0 → C81D.O1P 0 = 1) ∧ (k ≠ 0 → C81D.O1R k < k ∧ C81D.O1G k < 5 ∧
      C81D.O1P k = cP (Nat.add 10 (C81D.O1G k)) (C81D.O1P (C81D.O1R k))) := by
  have h := allN_spec o1_all k hk
  unfold o1At at h
  obtain ⟨h1, h⟩ := (bAnd_iff _ _).1 h
  obtain ⟨h2, h⟩ := (bAnd_iff _ _).1 h
  refine ⟨blt_iff h1, Nat.eq_of_beq_eq_true h2, fun h0 => ?_, fun h0 => ?_⟩
  · subst h0
    simp only [Nat.beq_refl] at h
    exact Nat.eq_of_beq_eq_true h
  · have e : Nat.beq k 0 = false := by
      cases k with
      | zero => exact absurd rfl h0
      | succ k => rfl
    simp only [e, bAnd_iff] at h
    exact ⟨blt_iff h.1, blt_iff h.2.1, Nat.eq_of_beq_eq_true h.2.2⟩

theorem oRow2 {k : Nat} (hk : k < 1224) : C81D.O2P k < 6156 ∧ C81D.O2Q (C81D.O2P k) = k ∧
    (k = 0 → C81D.O2P 0 = 1) ∧ (k ≠ 0 → C81D.O2R k < k ∧ C81D.O2G k < 3 ∧
      C81D.O2P k = cP (Nat.add 22 (C81D.O2G k)) (C81D.O2P (C81D.O2R k))) := by
  have h := allN_spec o2_all k hk
  unfold o2At at h
  obtain ⟨h1, h⟩ := (bAnd_iff _ _).1 h
  obtain ⟨h2, h⟩ := (bAnd_iff _ _).1 h
  refine ⟨blt_iff h1, Nat.eq_of_beq_eq_true h2, fun h0 => ?_, fun h0 => ?_⟩
  · subst h0
    simp only [Nat.beq_refl] at h
    exact Nat.eq_of_beq_eq_true h
  · have e : Nat.beq k 0 = false := by
      cases k with
      | zero => exact absurd rfl h0
      | succ k => rfl
    simp only [e, bAnd_iff] at h
    exact ⟨blt_iff h.1, blt_iff h.2.1, Nat.eq_of_beq_eq_true h.2.2⟩

theorem clRow {i : Nat} (hi : i < 20520) : nfValidK 4 PJ3.LR (C81D.CL i) = true ∧
    clKey (C81D.CL i) = C81D.CK i ∧ (i + 1 < 20520 → C81D.CK i < C81D.CK (i + 1)) := by
  have h0 : allBlk (Nat.mul (Nat.add (Nat.mul (i / 3420) 6) (i / 570 % 6)) 570) clAt 570 = true :=
    clB_all (i / 3420) (by omega : i / 3420 < 6) (i / 570 % 6) (by omega : i / 570 % 6 < 6)
  have h := allBlk_spec h0 (i % 570) (by omega)
  have e : Nat.add (Nat.mul (Nat.add (Nat.mul (i / 3420) 6) (i / 570 % 6)) 570) (i % 570) = i := by
    change (i / 3420 * 6 + i / 570 % 6) * 570 + i % 570 = i
    omega
  rw [e] at h
  unfold clAt at h
  obtain ⟨h1, h⟩ := (bAnd_iff _ _).1 h
  obtain ⟨h2, h3⟩ := (bAnd_iff _ _).1 h
  refine ⟨h1, Nat.eq_of_beq_eq_true h2, fun hl => ?_⟩
  have e2 : Nat.blt (Nat.add i 1) 20520 = true := blt_true hl
  rw [e2] at h3
  exact blt_iff h3

theorem CK_mono : ∀ k l, k < l → l < 20520 → C81D.CK k < C81D.CK l := by
  intro k l hkl hl
  induction l with
  | zero => omega
  | succ l ih =>
    have hs := (clRow (i := l) (by omega)).2.2 (by omega)
    rcases Nat.lt_succ_iff_lt_or_eq.1 hkl with h | h
    · exact lt_trans (ih h (by omega)) hs
    · subst h
      exact hs

@[expose] noncomputable def yF (z h e x : Nat) : Nat :=
  powF (nfp z) e (nfp h (powF (nfp z) e (nfi h x)))

theorem oddParts {z h q m row : Nat} (hq : Nat.beq q 9 = false) (H : oddOK z h q m row = true) :
    nfValidK 4 PJ3.LR z = true ∧ nfValidK 4 PJ3.LR h = true ∧ ordPL bs (nfp z) q = true ∧
    commR row (nfp z) = true ∧ commR row (nfp h) = true ∧
    eqOnL bs (powF (yF z h 1) (Nat.mul 2 m)) (fun x => x) = true ∧
    bIf(eqOnL bs (powF (yF z h 1) m) (fun x => x), false, true) = true := by
  unfold oddOK at H
  simp only [hq, bAnd_iff] at H
  exact H

theorem oddParts9 {z h m row : Nat} (H : oddOK z h 9 m row = true) :
    nfValidK 4 PJ3.LR z = true ∧ nfValidK 4 PJ3.LR h = true ∧ ord9L bs (nfp z) = true ∧
    commR row (nfp z) = true ∧ commR row (nfp h) = true ∧
    eqOnL bs (powF (yF z h 3) (Nat.mul 2 m)) (fun x => x) = true ∧
    bIf(eqOnL bs (powF (yF z h 3) m) (fun x => x), false, true) = true := by
  unfold oddOK at H
  simp only [Nat.beq_refl, bAnd_iff] at H
  exact H

theorem oddFacts : oddOK 562954323755875 562949970266780 3 3 0 = true ∧
    oddOK 281475052077923 281474999390686 5 3 0 = true ∧
    oddOK 281474976714532 4295361140 17 1 1 = true ∧
    oddOK 562954289616702 45351538 9 1 1 = true := by
  have h := smF.2.2.2.2.2.2.2.2.2.2
  simp only [oddB, oddW, bAnd_iff, and_true] at h
  exact h

section J3


theorem r9 : RepF 6156 (cP 9) (Tb 9) := (rep_T (k := 9) (by norm_num)).1
theorem r21 : RepF 6156 (cP 21) (Tb 21) := (rep_T (k := 21) (by norm_num)).1

theorem t9_mem : Tb 9 ∈ P3 := mem_of_bnd (g := 0) (by norm_num) r9 fun _ => rfl

theorem t9_ord : orderOf (Tb 9) = 2 := (ordPL_iff hH hbs r9 t9_mem Nat.prime_two).1 smF.2.2.2.1

theorem comm0 {f : Nat → Nat} {x : Equiv.Perm (Fin 6156)} (hf : RepF 6156 f x) (hx : x ∈ P3)
    (h : commR 0 f = true) : x * Tb 9 = Tb 9 * x := by
  have h' : eqOnL bs (fun y => f (cP 9 y)) (fun y => cP 9 (f y)) = true := h
  exact eq_of_eqOnL hH (hf.comp r9) (r9.comp hf) (P3.mul_mem hx t9_mem) (P3.mul_mem t9_mem hx) h'

theorem comm1 {f : Nat → Nat} {x : Equiv.Perm (Fin 6156)} (hf : RepF 6156 f x) (hx : x ∈ P3)
    (h : commR 1 f = true) : x * Tb 21 = Tb 21 * x := by
  have h' : eqOnL bs (fun y => f (cP 21 (cP 0 y))) (fun y => cP 21 (f (cP 0 y))) = true := h
  have hm2 : Tb 21 * (x * U) ∈ P3 := by
    have e : Tb 21 * (x * U) = (Tb 21 * U) * (U * x * U) := by
      calc Tb 21 * (x * U) = Tb 21 * (U * U) * x * U := by rw [U2]; group
        _ = _ := by group
    rw [e]
    exact P3.mul_mem T21U (conjU_mem hx)
  have := eq_of_eqOnL hH (hf.comp (r21.comp rep0)) (r21.comp (hf.comp rep0))
    (P3.mul_mem hx T21U) hm2 h'
  have e2 : x * Tb 21 * U = Tb 21 * x * U := by simpa only [mul_assoc] using this
  exact mul_right_cancel e2

theorem mem_cent {t x : Equiv.Perm (Fin 6156)} (hx : x ∈ P3) (h : x * t = t * x) :
    x ∈ j3P ⊓ centralizer ({t} : Set (Equiv.Perm (Fin 6156))) :=
  mem_inf.2 ⟨P_eq3 ▸ hx, mem_centralizer_singleton_iff.2 h⟩

theorem orbit_lb {K : Subgroup (Equiv.Perm (Fin 6156))} {m ng : Nat} {Pt Pa Gn Q : Nat → Nat}
    {gm : Nat → Nat → Nat} {gp : Nat → Equiv.Perm (Fin 6156)}
    (hgen : ∀ j < ng, gp j ∈ K ∧ RepF 6156 (gm j) (gp j))
    (hrow : ∀ k < m, Pt k < 6156 ∧ Q (Pt k) = k ∧ (k = 0 → Pt 0 = 1) ∧
      (k ≠ 0 → Pa k < k ∧ Gn k < ng ∧ Pt k = gm (Gn k) (Pt (Pa k))))
    {w : Equiv.Perm (Fin 6156)} (hw : w ∈ K) (hw1 : w ⟨1, by norm_num⟩ = ⟨1, by norm_num⟩)
    (hwne : w ≠ 1) : m * 2 ≤ Nat.card K := by
  have hreach : ∀ k < m, ∃ g ∈ K, (g ⟨1, by norm_num⟩ : Nat) = Pt k := by
    intro k
    induction k using Nat.strong_induction_on with
    | _ k ih =>
      intro hk
      obtain ⟨-, -, h0, hs⟩ := hrow k hk
      rcases Nat.eq_zero_or_pos k with rfl | hpos
      · exact ⟨1, K.one_mem, (h0 rfl).symm⟩
      · obtain ⟨hp, hg, he⟩ := hs (by omega)
        obtain ⟨g, hgK, hgv⟩ := ih _ hp (by omega)
        refine ⟨gp (Gn k) * g, K.mul_mem (hgen _ hg).1 hgK, ?_⟩
        have e1 : ((gp (Gn k) * g) ⟨1, by norm_num⟩ : ℕ) = gm (Gn k) (g ⟨1, by norm_num⟩) :=
          ((hgen _ hg).2 _ (g ⟨1, by norm_num⟩).2).symm
        rw [e1, hgv, he]
  let f : Fin m → Fin 6156 := fun k => ⟨Pt k, (hrow k k.2).1⟩
  have hf : Function.Injective f := fun a b hab => by
    have h1 : Pt a = Pt b := congrArg Fin.val hab
    have h2 := (hrow a a.2).2.1
    have h3 := (hrow b b.2).2.1
    rw [h1] at h2
    exact Fin.ext (h2.symm.trans h3)
  exact mul_le_card_of_orbit K ⟨1, by norm_num⟩ f hf (fun k => by
    obtain ⟨g, hg, hv⟩ := hreach k k.2
    exact ⟨g, hg, Fin.ext hv⟩) hw hw1 hwne

abbrev L1 : List CFSG.Sporadic.Th.Native.Table :=
  [j3CentTbl 10, j3CentTbl 11, j3CentTbl 12, j3CentTbl 13, j3CentTbl 14]

noncomputable abbrev K1 : Subgroup (Equiv.Perm (Fin 6156)) := closure (tp 6156 '' {x | x ∈ L1.toArray})

theorem L1_mem {j : Nat} (hj : j < 5) : j3CentTbl (Nat.add 10 j) ∈ L1.toArray := by
  rw [List.mem_toArray]
  interval_cases j
  · exact List.mem_cons_self
  · exact List.mem_cons_of_mem _ List.mem_cons_self
  · exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self)
  · exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self))
  · exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
      (List.mem_cons_of_mem _ List.mem_cons_self)))

theorem g1_rep {j : Nat} (hj : j < 5) : RepF 6156 (cP (Nat.add 10 j)) (Tb (Nat.add 10 j)) :=
  (rep_T (k := Nat.add 10 j) (by change 10 + j < 31; omega)).1

theorem g1_K {j : Nat} (hj : j < 5) : Tb (Nat.add 10 j) ∈ K1 :=
  subset_closure ⟨_, L1_mem hj, (Tb_def _).symm⟩

theorem g1_P {j : Nat} (hj : j < 5) : Tb (Nat.add 10 j) ∈ P3 :=
  mem_of_bnd (g := j + 1) (by omega) (g1_rep hj) fun y => by interval_cases j <;> rfl

theorem g1_comm {j : Nat} (hj : j < 5) : Tb (Nat.add 10 j) * Tb 9 = Tb 9 * Tb (Nat.add 10 j) :=
  comm0 (g1_rep hj) (g1_P hj) (allN_spec smF.2.2.2.2.1 j hj)

theorem K1_le : K1 ≤ j3P ⊓ centralizer ({Tb 9} : Set (Equiv.Perm (Fin 6156))) := by
  rw [closure_le]
  rintro _ ⟨x, hx, rfl⟩
  change x ∈ L1.toArray at hx
  rw [List.mem_toArray] at hx
  simp only [L1, List.mem_cons, List.not_mem_nil, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl
  · exact mem_cent (g1_P (j := 0) (by norm_num)) (g1_comm (j := 0) (by norm_num))
  · exact mem_cent (g1_P (j := 1) (by norm_num)) (g1_comm (j := 1) (by norm_num))
  · exact mem_cent (g1_P (j := 2) (by norm_num)) (g1_comm (j := 2) (by norm_num))
  · exact mem_cent (g1_P (j := 3) (by norm_num)) (g1_comm (j := 3) (by norm_num))
  · exact mem_cent (g1_P (j := 4) (by norm_num)) (g1_comm (j := 4) (by norm_num))

noncomputable abbrev W1 : Equiv.Perm (Fin 6156) :=
  (Tb 14)⁻¹ * ((Tb 11)⁻¹ * (Tb 12 * (Tb 11 * Tb 12)))

theorem W1_rep : RepF 6156 w1 W1 :=
  (rep_T (k := 14) (by norm_num)).2.comp ((rep_T (k := 11) (by norm_num)).2.comp
    ((rep_T (k := 12) (by norm_num)).1.comp ((rep_T (k := 11) (by norm_num)).1.comp
      (rep_T (k := 12) (by norm_num)).1)))

theorem card_K1 : 1920 ≤ Nat.card K1 := by
  have hW : W1 ∈ K1 := K1.mul_mem (K1.inv_mem (g1_K (j := 4) (by norm_num)))
    (K1.mul_mem (K1.inv_mem (g1_K (j := 1) (by norm_num))) (K1.mul_mem (g1_K (j := 2) (by norm_num))
      (K1.mul_mem (g1_K (j := 1) (by norm_num)) (g1_K (j := 2) (by norm_num)))))
  have hw1 : W1 ⟨1, by norm_num⟩ = ⟨1, by norm_num⟩ :=
    Fin.ext ((W1_rep 1 (by norm_num)).symm.trans (Nat.eq_of_beq_eq_true smF.2.2.2.2.2.2.1))
  have hwne : W1 ≠ 1 := fun h => bNot smF.2.2.2.2.2.2.2.1
    ((W1_rep 3 (by norm_num)).trans (congrArg (fun g : Equiv.Perm (Fin 6156) =>
      (g ⟨3, by norm_num⟩ : ℕ)) h))
  have := orbit_lb (K := K1) (m := 960) (ng := 5) (Pt := C81D.O1P) (Pa := C81D.O1R) (Gn := C81D.O1G)
    (Q := C81D.O1Q) (gm := fun j x => cP (Nat.add 10 j) x) (gp := fun j => Tb (Nat.add 10 j))
    (fun j hj => ⟨g1_K hj, g1_rep hj⟩) (fun k hk => oRow1 hk) hW hw1 hwne
  omega

theorem card_C9 : Nat.card ↥(j3P ⊓ centralizer ({Tb 9} : Set (Equiv.Perm (Fin 6156)))) = 1920 := by
  obtain ⟨c, hc⟩ := isConj_iff.1 (invol_conj (x := ⟨Tb 9, t9_mem⟩)
    (by rw [Subgroup.orderOf_mk]; exact t9_ord))
  have hc' : (c : Equiv.Perm (Fin 6156)) * tE * (c : Equiv.Perm (Fin 6156))⁻¹ = Tb 9 :=
    congrArg Subtype.val hc
  have hcP : (c : Equiv.Perm (Fin 6156)) ∈ j3P := by
    rw [P_eq3]
    exact c.2
  rw [← hc', inf_centralizer_conj j3P hcP tE,
    Subgroup.card_map_of_injective (MulAut.conj (c : Equiv.Perm (Fin 6156))).injective, P_eq3,
    ← cent_t]
  exact Nat.card_congr
    { toFun := fun x => ⟨⟨x.1, (mem_inf.1 x.2).1⟩, (mem_centralizer_singleton_iff.1 (mem_inf.1 x.2).2)⟩
      invFun := fun g => ⟨g.1.1, mem_inf.2 ⟨g.1.2, mem_centralizer_singleton_iff.2 g.2⟩⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }

theorem row_of {t : Equiv.Perm (Fin 6156)} {K : Subgroup (Equiv.Perm (Fin 6156))} {N cls : Nat}
    (hKle : K ≤ j3P ⊓ centralizer ({t} : Set (Equiv.Perm (Fin 6156)))) (hK : N ≤ Nat.card K)
    (hC : Nat.card ↥(j3P ⊓ centralizer ({t} : Set (Equiv.Perm (Fin 6156)))) ≤ N)
    (hcls : cls * N = 50232960) (hN : 0 < N) :
    K = j3P ⊓ centralizer ({t} : Set (Equiv.Perm (Fin 6156))) ∧
      Nat.card ↥(j3P ⊓ centralizer ({t} : Set (Equiv.Perm (Fin 6156)))) = N ∧
      (conjClass j3P t).ncard = cls := by
  have hle := Subgroup.card_le_of_le hKle
  have hCN : Nat.card ↥(j3P ⊓ centralizer ({t} : Set (Equiv.Perm (Fin 6156)))) = N := by omega
  refine ⟨Subgroup.eq_of_le_of_card_ge hKle (by omega), hCN, ?_⟩
  have h := ncard_conjClass_mul_card j3P t
  rw [hCN, card_j3P, ← hcls] at h
  exact Nat.eq_of_mul_eq_mul_right hN h

theorem y_rep {z h e : Nat} (hz : nfValidK 4 PJ3.LR z = true) (hh : nfValidK 4 PJ3.LR h = true) :
    RepF 6156 (yF z h e) (E z ^ e * (E h * E z ^ e * (E h)⁻¹)) :=
  (((nfp_rep hz).powF e).comp ((nfp_rep hh).comp (((nfp_rep hz).powF e).comp
    (nfi_rep hh)))).congr (by group)

theorem y_mem {z h e : Nat} (hz : nfValidK 4 PJ3.LR z = true) (hh : nfValidK 4 PJ3.LR h = true) :
    E z ^ e * (E h * E z ^ e * (E h)⁻¹) ∈ P3 :=
  P3.mul_mem (P3.pow_mem (E_mem hz) e) (P3.mul_mem (P3.mul_mem (E_mem hh) (P3.pow_mem (E_mem hz) e))
    (P3.inv_mem (E_mem hh)))

theorem even_y {z h e m : Nat} (hz : nfValidK 4 PJ3.LR z = true) (hh : nfValidK 4 PJ3.LR h = true)
    (h1 : eqOnL bs (powF (yF z h e) (Nat.mul 2 m)) (fun x => x) = true)
    (h2 : bIf(eqOnL bs (powF (yF z h e) m) (fun x => x), false, true) = true) :
    2 ∣ orderOf (E z ^ e * (E h * E z ^ e * (E h)⁻¹)) := by
  have hy := y_rep (e := e) hz hh
  have hm := y_mem (e := e) hz hh
  refine two_dvd_orderOf (m := m) ?_ ?_
  · exact (fixL_iff hH hbs (hy.powF (2 * m)) (P3.pow_mem hm _)).1 h1
  · intro he
    exact (bNot_iff _).1 h2 ((fixL_iff hH hbs (hy.powF m) (P3.pow_mem hm _)).2 he)

theorem oddCore1 : CFSG.oddCore ↥(j3P ⊓ centralizer ({Tb 9} : Set (Equiv.Perm (Fin 6156)))) = ⊥ := by
  obtain ⟨o1, o2, -, -⟩ := oddFacts
  obtain ⟨a1, b1, c1, d1, e1, f1, g1⟩ := oddParts (q := 3) rfl o1
  obtain ⟨a2, b2, c2, d2, e2, f2, g2⟩ := oddParts (q := 5) rfl o2
  refine oddCore_eq_bot_of_cyclic _ [(E 562954323755875, E 562949970266780, 3, 1),
    (E 281475052077923, E 281474999390686, 5, 1)] ?_ ?_
  · intro q hq hdvd hq2
    rw [card_C9] at hdvd
    rcases prime_dvd3 (p1 := 2) (p2 := 3) (p3 := 5) (e1 := 7) (e2 := 1) (e3 := 1) hq
      Nat.prime_two Nat.prime_three (by norm_num) (by norm_num; exact hdvd) with h | h | h
    · exact absurd h hq2
    · exact ⟨_, List.mem_cons_self, h.symm⟩
    · exact ⟨_, List.mem_cons_of_mem _ List.mem_cons_self, h.symm⟩
  · intro e he
    simp only [List.mem_cons, List.not_mem_nil, or_false] at he
    rcases he with rfl | rfl
    · refine ⟨mem_cent (E_mem a1) (comm0 (nfp_rep a1) (E_mem a1) d1),
        mem_cent (E_mem b1) (comm0 (nfp_rep b1) (E_mem b1) e1), Nat.prime_three, by norm_num,
        ?_, ?_, even_y (e := 1) a1 b1 f1 g1⟩
      · rw [pow_one]
        exact (ordPL_iff hH hbs (nfp_rep a1) (E_mem a1) Nat.prime_three).1 c1
      · rw [card_C9]
        exact PJ3Group.factorization_eq Nat.prime_three (m := 640) (by norm_num) (by norm_num)
    · refine ⟨mem_cent (E_mem a2) (comm0 (nfp_rep a2) (E_mem a2) d2),
        mem_cent (E_mem b2) (comm0 (nfp_rep b2) (E_mem b2) e2), by norm_num, by norm_num,
        ?_, ?_, even_y (e := 1) a2 b2 f2 g2⟩
      · rw [pow_one]
        exact (ordPL_iff hH hbs (nfp_rep a2) (E_mem a2) (by norm_num)).1 c2
      · rw [card_C9]
        exact PJ3Group.factorization_eq (by norm_num) (m := 384) (by norm_num) (by norm_num)

theorem row1 : Tb 9 ∈ j3P ⊔ zpowers U ∧ orderOf (Tb 9) = 2 ∧ (false = true ↔ Tb 9 ∉ j3P) ∧
    K1 = j3P ⊓ centralizer ({Tb 9} : Set (Equiv.Perm (Fin 6156))) ∧
    Nat.card ↥(j3P ⊓ centralizer ({Tb 9} : Set (Equiv.Perm (Fin 6156)))) = 1920 ∧
    (conjClass j3P (Tb 9)).ncard = 26163 ∧
    CFSG.oddCore ↥(j3P ⊓ centralizer ({Tb 9} : Set (Equiv.Perm (Fin 6156)))) = ⊥ := by
  obtain ⟨hK, hc, hn⟩ := row_of (cls := 26163) K1_le card_K1 card_C9.le (by norm_num) (by norm_num)
  have hP : Tb 9 ∈ j3P := P_eq3 ▸ t9_mem
  exact ⟨mem_sup_left hP, t9_ord, ⟨fun h => absurd h Bool.false_ne_true, fun h => absurd hP h⟩,
    hK, hc, hn, oddCore1⟩

abbrev L2 : List CFSG.Sporadic.Th.Native.Table := [j3CentTbl 22, j3CentTbl 23, j3CentTbl 24]

noncomputable abbrev K2 : Subgroup (Equiv.Perm (Fin 6156)) := closure (tp 6156 '' {x | x ∈ L2.toArray})

theorem L2_mem {j : Nat} (hj : j < 3) : j3CentTbl (Nat.add 22 j) ∈ L2.toArray := by
  rw [List.mem_toArray]
  interval_cases j
  · exact List.mem_cons_self
  · exact List.mem_cons_of_mem _ List.mem_cons_self
  · exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self)

theorem g2_rep {j : Nat} (hj : j < 3) : RepF 6156 (cP (Nat.add 22 j)) (Tb (Nat.add 22 j)) :=
  (rep_T (k := Nat.add 22 j) (by change 22 + j < 31; omega)).1

theorem g2_K {j : Nat} (hj : j < 3) : Tb (Nat.add 22 j) ∈ K2 :=
  subset_closure ⟨_, L2_mem hj, (Tb_def _).symm⟩

theorem g2_P {j : Nat} (hj : j < 3) : Tb (Nat.add 22 j) ∈ P3 :=
  mem_of_bnd (g := j + 7) (by omega) (g2_rep hj) fun y => by interval_cases j <;> rfl

theorem g2_comm {j : Nat} (hj : j < 3) :
    Tb (Nat.add 22 j) * Tb 21 = Tb 21 * Tb (Nat.add 22 j) :=
  comm1 (g2_rep hj) (g2_P hj) (allN_spec smF.2.2.2.2.2.1 j hj)

theorem K2_le : K2 ≤ j3P ⊓ centralizer ({Tb 21} : Set (Equiv.Perm (Fin 6156))) := by
  rw [closure_le]
  rintro _ ⟨x, hx, rfl⟩
  change x ∈ L2.toArray at hx
  rw [List.mem_toArray] at hx
  simp only [L2, List.mem_cons, List.not_mem_nil, or_false] at hx
  rcases hx with rfl | rfl | rfl
  · exact mem_cent (g2_P (j := 0) (by norm_num)) (g2_comm (j := 0) (by norm_num))
  · exact mem_cent (g2_P (j := 1) (by norm_num)) (g2_comm (j := 1) (by norm_num))
  · exact mem_cent (g2_P (j := 2) (by norm_num)) (g2_comm (j := 2) (by norm_num))

noncomputable abbrev W2 : Equiv.Perm (Fin 6156) :=
  (Tb 23)⁻¹ * ((Tb 24)⁻¹ * ((Tb 22)⁻¹ * ((Tb 24)⁻¹ * (Tb 23 * (Tb 24 * (Tb 22 * (Tb 24 * Tb 23)))))))

theorem W2_rep : RepF 6156 w2 W2 :=
  (rep_T (k := 23) (by norm_num)).2.comp ((rep_T (k := 24) (by norm_num)).2.comp
    ((rep_T (k := 22) (by norm_num)).2.comp ((rep_T (k := 24) (by norm_num)).2.comp
      ((rep_T (k := 23) (by norm_num)).1.comp ((rep_T (k := 24) (by norm_num)).1.comp
        ((rep_T (k := 22) (by norm_num)).1.comp ((rep_T (k := 24) (by norm_num)).1.comp
          (rep_T (k := 23) (by norm_num)).1)))))))

theorem card_K2 : 2448 ≤ Nat.card K2 := by
  have k22 := g2_K (j := 0) (by norm_num)
  have k23 := g2_K (j := 1) (by norm_num)
  have k24 := g2_K (j := 2) (by norm_num)
  have hW : W2 ∈ K2 := K2.mul_mem (K2.inv_mem k23) (K2.mul_mem (K2.inv_mem k24)
    (K2.mul_mem (K2.inv_mem k22) (K2.mul_mem (K2.inv_mem k24) (K2.mul_mem k23 (K2.mul_mem k24
      (K2.mul_mem k22 (K2.mul_mem k24 k23)))))))
  have hw1 : W2 ⟨1, by norm_num⟩ = ⟨1, by norm_num⟩ :=
    Fin.ext ((W2_rep 1 (by norm_num)).symm.trans (Nat.eq_of_beq_eq_true smF.2.2.2.2.2.2.2.2.1))
  have hwne : W2 ≠ 1 := fun h => bNot smF.2.2.2.2.2.2.2.2.2.1
    ((W2_rep 0 (by norm_num)).trans (congrArg (fun g : Equiv.Perm (Fin 6156) =>
      (g ⟨0, by norm_num⟩ : ℕ)) h))
  have := orbit_lb (K := K2) (m := 1224) (ng := 3) (Pt := C81D.O2P) (Pa := C81D.O2R)
    (Gn := C81D.O2G) (Q := C81D.O2Q) (gm := fun j x => cP (Nat.add 22 j) x)
    (gp := fun j => Tb (Nat.add 22 j)) (fun j hj => ⟨g2_K hj, g2_rep hj⟩) (fun k hk => oRow2 hk)
    hW hw1 hwne
  omega

theorem conjE_rep {F : Nat} (hF : nfValidK 4 PJ3.LR F = true) :
    RepF 6156 (fun b => nfp F (cP 21 (nfi F b))) (E F * Tb 21 * (E F)⁻¹) :=
  ((nfp_rep hF).comp (r21.comp (nfi_rep hF))).congr (by group)

theorem cls_ge : 20520 ≤ (conjClass j3P (Tb 21)).ncard := by
  let f : Fin 20520 → Equiv.Perm (Fin 6156) := fun i =>
    E (C81D.CL i) * Tb 21 * (E (C81D.CL i))⁻¹
  have hf : Function.Injective f := by
    intro a b hab
    have hk : clKey (C81D.CL a) = clKey (C81D.CL b) := keyL_congr 6156 fun x hx =>
      ((conjE_rep (clRow a.2).1) x (hbs x hx)).trans
        ((congrArg (fun g : Equiv.Perm (Fin 6156) => (g ⟨x, hbs x hx⟩ : ℕ)) hab).trans
          ((conjE_rep (clRow b.2).1) x (hbs x hx)).symm)
    rw [(clRow a.2).2.1, (clRow b.2).2.1] at hk
    by_contra hne
    rcases Nat.lt_or_gt_of_ne (Fin.val_ne_of_ne hne) with h | h
    · exact (CK_mono _ _ h b.2).ne hk
    · exact (CK_mono _ _ h a.2).ne' hk
  have hsub : Set.range f ⊆ conjClass j3P (Tb 21) := by
    rintro _ ⟨i, rfl⟩
    exact ⟨E (C81D.CL i), P_eq3 ▸ E_mem (clRow i.2).1, rfl⟩
  have := Set.ncard_le_ncard hsub (Set.toFinite _)
  rwa [Set.ncard_range_of_injective hf, Nat.card_eq_fintype_card, Fintype.card_fin] at this

theorem card_C21_le : Nat.card ↥(j3P ⊓ centralizer ({Tb 21} : Set (Equiv.Perm (Fin 6156)))) ≤
    2448 := by
  have h := ncard_conjClass_mul_card j3P (Tb 21)
  rw [card_j3P] at h
  have := cls_ge
  nlinarith

theorem card_C21 : Nat.card ↥(j3P ⊓ centralizer ({Tb 21} : Set (Equiv.Perm (Fin 6156)))) = 2448 :=
  le_antisymm card_C21_le (card_K2.trans (Subgroup.card_le_of_le K2_le))

theorem oddCore2 :
    CFSG.oddCore ↥(j3P ⊓ centralizer ({Tb 21} : Set (Equiv.Perm (Fin 6156)))) = ⊥ := by
  obtain ⟨-, -, o3, o4⟩ := oddFacts
  obtain ⟨a1, b1, c1, d1, e1, f1, g1⟩ := oddParts (q := 17) rfl o3
  obtain ⟨a2, b2, c2, d2, e2, f2, g2⟩ := oddParts9 o4
  refine oddCore_eq_bot_of_cyclic _ [(E 281474976714532, E 4295361140, 17, 1),
    (E 562954289616702, E 45351538, 3, 2)] ?_ ?_
  · intro q hq hdvd hq2
    rw [card_C21] at hdvd
    rcases prime_dvd3 (p1 := 2) (p2 := 3) (p3 := 17) (e1 := 4) (e2 := 2) (e3 := 1) hq
      Nat.prime_two Nat.prime_three (by norm_num) (by norm_num; exact hdvd) with h | h | h
    · exact absurd h hq2
    · exact ⟨_, List.mem_cons_of_mem _ List.mem_cons_self, h.symm⟩
    · exact ⟨_, List.mem_cons_self, h.symm⟩
  · intro e he
    simp only [List.mem_cons, List.not_mem_nil, or_false] at he
    rcases he with rfl | rfl
    · refine ⟨mem_cent (E_mem a1) (comm1 (nfp_rep a1) (E_mem a1) d1),
        mem_cent (E_mem b1) (comm1 (nfp_rep b1) (E_mem b1) e1), by norm_num, by norm_num,
        ?_, ?_, even_y (e := 1) a1 b1 f1 g1⟩
      · rw [pow_one]
        exact (ordPL_iff hH hbs (nfp_rep a1) (E_mem a1) (by norm_num)).1 c1
      · rw [card_C21]
        exact PJ3Group.factorization_eq (by norm_num) (m := 144) (by norm_num) (by norm_num)
    · refine ⟨mem_cent (E_mem a2) (comm1 (nfp_rep a2) (E_mem a2) d2),
        mem_cent (E_mem b2) (comm1 (nfp_rep b2) (E_mem b2) e2), Nat.prime_three, by norm_num,
        ?_, ?_, even_y (e := 3) a2 b2 f2 g2⟩
      · exact (ord9L_iff hH hbs (nfp_rep a2) (E_mem a2)).1 c2
      · rw [card_C21]
        exact PJ3Group.factorization_eq Nat.prime_three (m := 272) (by norm_num) (by norm_num)

theorem row2 : Tb 21 ∈ j3P ⊔ zpowers U ∧ orderOf (Tb 21) = 2 ∧ (true = true ↔ Tb 21 ∉ j3P) ∧
    K2 = j3P ⊓ centralizer ({Tb 21} : Set (Equiv.Perm (Fin 6156))) ∧
    Nat.card ↥(j3P ⊓ centralizer ({Tb 21} : Set (Equiv.Perm (Fin 6156)))) = 2448 ∧
    (conjClass j3P (Tb 21)).ncard = 20520 ∧
    CFSG.oddCore ↥(j3P ⊓ centralizer ({Tb 21} : Set (Equiv.Perm (Fin 6156)))) = ⊥ := by
  obtain ⟨hK, hc, hn⟩ := row_of (cls := 20520) K2_le card_K2 card_C21.le (by norm_num) (by norm_num)
  have hnP : Tb 21 ∉ j3P := fun h => T21_not (P_eq3 ▸ h)
  exact ⟨(R_mem _).2 (Or.inr (P_eq3 ▸ T21U)), orderOf_eq_prime (by rw [sq, T21_2]) T21_ne,
    ⟨fun _ => hnP, fun _ => rfl⟩, hK, hc, hn, oddCore2⟩

end J3

end CertificateChecks.KernelSporSch.PJ3C81

end
