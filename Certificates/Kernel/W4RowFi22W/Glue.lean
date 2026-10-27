module

public import Certificates.Kernel.W4RowFi22W.Chk
public import CFSG.Certificates.Kernel.W4RowFi22W.Sound
public import Certificates.Kernel.Sporadic.Fi22.Base6
public import Certificates.Kernel.Sporadic.Fi22.C3155
public import Certificates.Kernel.Sporadic.Fi22.E2067
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoSporadicFi22
public import CFSG.LocalAnalysis.EvenSporadicStandard.HypOne.Fi22
public import CFSG.HardMathSupport.Meierfrankenfeld.FFToolkit.HeisLift

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelW4F22

open CFSG.KC.Enum CFSG.KC.Census CFSG.KC.Census.Base CFSG.KC.W4F22 CertificateChecks.KernelSpor
open CFSG.Monster.B.Co2 CFSG.Monster.B.Fischer CFSG.Sporadic.FischerOddCore
open CFSG.HardMathSupport.Meierfrankenfeld.FFToolkit CFSG.Certificates
open CFSG.ComponentClassification.RankTwoSporadic.Fi22 CFSG.EvenSporadicStandard.HypOne.Fi22

@[expose] noncomputable def ℓ0 (k : ℕ) : Equiv.Perm (Fin 3510) :=
  if k < 2 then fi22GenPerm k else fi22ExtRep (k - 2)

@[expose] noncomputable def ℓF (k : ℕ) : Equiv.Perm (Fin 3510) :=
  if k < 8 then ℓ0 k else (ℓ0 (k - 8))⁻¹

@[expose] noncomputable def vE (i : ℕ) : Equiv.Perm (Fin 3510) := ev ℓF CFSG.KD.W4F22.E i

theorem gen_mem {k : ℕ} (hk : k < 2) : fi22GenPerm k ∈ fi22P := by
  have hmem : fi22Chain.original.get ⟨k, hk⟩ ∈ fi22P :=
    Subgroup.subset_closure (schreier_vector_get_mem_toList fi22Chain.original ⟨k, hk⟩)
  rwa [fi22Chain_original_get] at hmem

theorem strictB_eq' (y : ℕ) (k : ℕ → Bool) : strictB y k = k y := by cases y <;> rfl

theorem band_left {a b : Bool} (h : Bool.rec (motive := fun _ => Bool) false b a = true) :
    a = true := by
  cases a
  · exact absurd h Bool.false_ne_true
  · rfl

theorem band_right {a b : Bool} (h : Bool.rec (motive := fun _ => Bool) false b a = true) :
    b = true := by
  cases a
  · exact absurd h Bool.false_ne_true
  · exact h

theorem inv_table {A B : ℕ} {g : Equiv.Perm (Fin 3510)}
    (hA : ∀ p (hp : p < 3510), at' 12 A p = (g ⟨p, hp⟩ : ℕ))
    (hc : allN 3510 (fun p => strictB (at' 12 A p) fun q =>
      Bool.rec (motive := fun _ => Bool) false (Nat.beq (at' 12 B q) p) (Nat.blt q 3510)) = true)
    (p : ℕ) (hp : p < 3510) : at' 12 B p = (g⁻¹ ⟨p, hp⟩ : ℕ) := by
  set q : Fin 3510 := g⁻¹ ⟨p, hp⟩ with hq
  have h := CFSG.KS.Raw.Orb.allN_iff.1 hc q.val q.isLt
  beta_reduce at h
  rw [strictB_eq'] at h
  have h' : Bool.rec (motive := fun _ => Bool) false (Nat.beq (at' 12 B (at' 12 A q.val)) q.val)
      (Nat.blt (at' 12 A q.val) 3510) = true := h
  have e : at' 12 A q.val = p := by
    rw [hA q.val q.isLt, Fin.eta, hq]
    simp
  rw [e] at h'
  exact Nat.eq_of_beq_eq_true (band_right h')

section Certs


theorem t_inv {k : ℕ} (hk : k < 6) : (fi22ExtRep k)⁻¹ = fi22ExtRep k := by
  have h := pow_orderOf_eq_one (fi22ExtRep k)
  rw [CTUC_Fi22_all_extension_involutions_covered.2.2.1 k hk, sq] at h
  exact inv_eq_of_mul_eq_one_right h

theorem t_mem_R {k : ℕ} (hk : k < 6) : fi22ExtRep k ∈ fi22R := by
  rcases Nat.lt_or_ge k 3 with h3 | h3
  · exact fi22P_le_R (CTUC_Fi22_all_extension_involutions_covered.1 k h3)
  · exact fi22ExtRep_mem_R h3 hk

theorem conj_mem_P {t c : Equiv.Perm (Fin 3510)} (ht : t ∈ fi22R) (hc : c ∈ fi22P) :
    t * c * t⁻¹ ∈ fi22P := by
  have h := fi22P_normal.conj_mem ⟨c, fi22P_le_R hc⟩ (Subgroup.mem_subgroupOf.2 hc) ⟨t, ht⟩
  exact Subgroup.mem_subgroupOf.1 h

theorem dih_mem {k : ℕ} (hk : k < 6) {c : Equiv.Perm (Fin 3510)} (hc : c ∈ fi22P) :
    fi22ExtRep k * c * fi22ExtRep k * c⁻¹ ∈ fi22P := by
  have h := conj_mem_P (t_mem_R hk) hc
  rw [t_inv hk] at h
  exact fi22P.mul_mem h (fi22P.inv_mem hc)

theorem at_gen {k : ℕ} (hk : k < 2) (p : ℕ) (hp : p < 3510) :
    at' (nat_lit 12) (Fi22CGT.F k) p = (fi22GenPerm k ⟨p, hp⟩ : ℕ) := by
  have h := F3155.unpack_get12 (P := Fi22CGT.F k) hp
  rw [← Fi22G.gen_eq hk] at h
  exact h.symm.trans (rep_fi22Gen hk ⟨p, hp⟩)

theorem at_t {k : ℕ} (hk : k < 6) (p : ℕ) (hp : p < 3510) :
    at' (nat_lit 12) (Fi22ExtT.L (21 + k)) p = (fi22ExtRep k ⟨p, hp⟩ : ℕ) := by
  have h := F3155.unpack_get12 (P := Fi22ExtT.L (21 + k)) hp
  rw [← Fi22E2067.ext_eq (by omega)] at h
  exact h.symm.trans (rep_fi22ExtRep hk ⟨p, hp⟩)

theorem LF_a {k : ℕ} (hk : k < 2) : LF k = Fi22CGT.F k := by
  have h : Nat.blt k (nat_lit 2) = true := Nat.blt_eq.mpr hk
  unfold LF
  rw [h]

theorem LF_t {k : ℕ} (h1 : 2 ≤ k) (h2 : k < 8) : LF k = Fi22ExtT.L (21 + (k - 2)) := by
  have ha : Nat.blt k (nat_lit 2) = false := by
    cases e : Nat.blt k (nat_lit 2)
    · rfl
    · have e' : k < _ := Nat.blt_eq.mp e
      simp only [] at e'
      exact absurd e' (by simp only [Nat.not_lt]; omega)
  have hb : Nat.blt k (nat_lit 8) = true := Nat.blt_eq.mpr h2
  have e : Nat.add (nat_lit 19) k = 21 + (k - 2) := by
    change 19 + k = 21 + (k - 2)
    omega
  unfold LF
  rw [ha, hb]
  exact congrArg Fi22ExtT.L e

theorem LF_ai {k : ℕ} (h1 : 8 ≤ k) (h2 : k < 10) :
    LF k = List.getD CFSG.KD.W4F22.AI (k - 8) 0 := by
  have ha : Nat.blt k (nat_lit 2) = false := by
    cases e : Nat.blt k (nat_lit 2)
    · rfl
    · have e' : k < _ := Nat.blt_eq.mp e
      simp only [] at e'
      exact absurd e' (by simp only [Nat.not_lt]; omega)
  have hb : Nat.blt k (nat_lit 8) = false := by
    cases e : Nat.blt k (nat_lit 8)
    · rfl
    · have e' : k < _ := Nat.blt_eq.mp e
      simp only [] at e'
      exact absurd e' (by simp only [Nat.not_lt]; omega)
  have hc : Nat.blt k (nat_lit 10) = true := Nat.blt_eq.mpr h2
  unfold LF
  rw [ha, hb, hc]
  rfl

theorem LF_t' {k : ℕ} (h1 : 10 ≤ k) : LF k = Fi22ExtT.L (21 + (k - 10)) := by
  have ha : Nat.blt k (nat_lit 2) = false := by
    cases e : Nat.blt k (nat_lit 2)
    · rfl
    · have e' : k < _ := Nat.blt_eq.mp e
      simp only [] at e'
      exact absurd e' (by simp only [Nat.not_lt]; omega)
  have hb : Nat.blt k (nat_lit 8) = false := by
    cases e : Nat.blt k (nat_lit 8)
    · rfl
    · have e' : k < _ := Nat.blt_eq.mp e
      simp only [] at e'
      exact absurd e' (by simp only [Nat.not_lt]; omega)
  have hc : Nat.blt k (nat_lit 10) = false := by
    cases e : Nat.blt k (nat_lit 10)
    · rfl
    · have e' : k < _ := Nat.blt_eq.mp e
      simp only [] at e'
      exact absurd e' (by simp only [Nat.not_lt]; omega)
  have e : Nat.add (nat_lit 11) k = 21 + (k - 10) := by
    change 11 + k = 21 + (k - 10)
    omega
  unfold LF
  rw [ha, hb, hc]
  exact congrArg Fi22ExtT.L e

theorem at_ai0 (p : ℕ) (hp : p < 3510) :
    at' 12 (List.getD CFSG.KD.W4F22.AI 0 0) p = ((fi22GenPerm 0)⁻¹ ⟨p, hp⟩ : ℕ) :=
  inv_table (A := Fi22CGT.F 0) (at_gen (by norm_num)) w4f22i0 p hp

theorem at_ai1 (p : ℕ) (hp : p < 3510) :
    at' 12 (List.getD CFSG.KD.W4F22.AI 1 0) p = ((fi22GenPerm 1)⁻¹ ⟨p, hp⟩ : ℕ) :=
  inv_table (A := Fi22CGT.F 1) (at_gen (by norm_num)) w4f22i1 p hp

theorem letters : Letters 3510 12 8 LF ℓF := by
  refine ⟨fun k hk p hp => ?_, fun k hk => ?_⟩
  · rcases Nat.lt_or_ge k 2 with h2 | h2
    · have e : ℓF k = fi22GenPerm k := by
        simp only [ℓF, ℓ0, if_pos (show k < 8 by omega), if_pos h2]
      rw [LF_a h2, e]
      exact at_gen h2 p hp
    rcases Nat.lt_or_ge k 8 with h8 | h8
    · have e : ℓF k = fi22ExtRep (k - 2) := by
        simp only [ℓF, ℓ0, if_pos h8, if_neg (show ¬ k < 2 by omega)]
      rw [LF_t h2 h8, e]
      exact at_t (by omega) p hp
    rcases Nat.lt_or_ge k 10 with h10 | h10
    · have e : ℓF k = (fi22GenPerm (k - 8))⁻¹ := by
        simp only [ℓF, ℓ0, if_neg (show ¬ k < 8 by omega), if_pos (show k - 8 < 2 by omega)]
      rw [LF_ai h8 h10, e]
      rcases Nat.lt_or_ge k 9 with h9 | h9
      · have ek : k - 8 = 0 := by omega
        rw [ek]
        exact at_ai0 p hp
      · have ek : k - 8 = 1 := by omega
        rw [ek]
        exact at_ai1 p hp
    · have e : ℓF k = fi22ExtRep (k - 10) := by
        have e1 : k - 8 - 2 = k - 10 := by omega
        simp only [ℓF, ℓ0, if_neg (show ¬ k < 8 by omega), if_neg (show ¬ k - 8 < 2 by omega), e1]
        exact t_inv (by omega)
      rw [LF_t' h10, e]
      exact at_t (by omega) p hp
  · have e : 8 + k - 8 = k := by omega
    simp only [ℓF, if_neg (show ¬ 8 + k < 8 by omega), if_pos hk, e]

end Certs

theorem wordOK : ∀ x ∈ CFSG.KD.W4F22.E, WordOK 8 x := fun x hx k hk => by
  have h := lettersB_sound w4f22_let x hx k hk
  change k < 2 * 8
  omega

theorem getD_of_all {l : List (List ℕ)} {P : List ℕ → Prop} (h : ∀ x ∈ l, P x) (h0 : P [])
    (i : ℕ) : P (l.getD i []) := by
  rcases Nat.lt_or_ge i l.length with hi | hi
  · rw [List.getD_eq_getElem _ _ hi]
    exact h _ (List.getElem_mem hi)
  · rw [List.getD_eq_default _ _ hi]
    exact h0

theorem getD_drop6 {i : ℕ} (hi : 6 ≤ i) :
    CFSG.KD.W4F22.E.getD i [] = (CFSG.KD.W4F22.E.drop 6).getD (i - 6) [] := by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_drop]
  congr 2
  omega

theorem actPerm_mem :
    ∀ x : List ℕ, (∀ k ∈ x, k < 16 ∧ k % 8 < 2) → actPerm ℓF x ∈ fi22P
  | [], _ => fi22P.one_mem
  | k :: l, hx => by
    obtain ⟨h16, h8⟩ := hx k List.mem_cons_self
    refine fi22P.mul_mem (actPerm_mem l fun j hj => hx j (List.mem_cons_of_mem _ hj)) ?_
    rcases Nat.lt_or_ge k 8 with h | h
    · have hk2 : k < 2 := by omega
      simp only [ℓF, ℓ0, if_pos h, if_pos hk2]
      exact gen_mem hk2
    · have hk2 : k - 8 < 2 := by omega
      simp only [ℓF, ℓ0, if_neg (show ¬ k < 8 by omega), if_pos hk2]
      exact fi22P.inv_mem (gen_mem hk2)

theorem vE_mem {i : ℕ} (hi : 6 ≤ i) : vE i ∈ fi22P := by
  rw [vE, ev, getD_drop6 hi]
  refine getD_of_all (P := fun x => actPerm ℓF x ∈ fi22P) (fun x hx => actPerm_mem x ?_)
    fi22P.one_mem _
  intro k hk
  have h1 := wordOK x (List.mem_of_mem_drop hx) k hk
  have h2 := Nat.blt_eq.mp (List.all_eq_true.1 (List.all_eq_true.1 w4f22_aonly x hx) k hk)
  exact ⟨by simpa [WordOK] using h1, h2⟩

theorem vE_T
    {k : ℕ} (hk : k < 6) :
    vE k = fi22ExtRep k := by
  have e : ∀ (j : ℕ) (x : List ℕ), CFSG.KD.W4F22.E.getD j [] = x → vE j = actPerm ℓF x :=
    fun j x h => by rw [vE, ev, h]
  interval_cases k
  · rw [e 0 [2] rfl]
    simp [actPerm, ℓF, ℓ0]
  · rw [e 1 [3] rfl]
    simp [actPerm, ℓF, ℓ0]
  · rw [e 2 [4] rfl]
    simp [actPerm, ℓF, ℓ0]
  · rw [e 3 [5] rfl]
    simp [actPerm, ℓF, ℓ0]
  · rw [e 4 [6] rfl]
    simp [actPerm, ℓF, ℓ0]
  · rw [e 5 [7] rfl]
    simp [actPerm, ℓF, ℓ0]

@[expose] def dihW (k c : ℕ) : List ℕ := [2 * c + 1, 2 * k, 2 * c, 2 * k]

@[expose] def dihR (k c p : ℕ) : List ℕ × List ℕ := ((List.replicate p (dihW k c)).flatten, [])

@[expose] def sqR (k c g : ℕ) : List ℕ × List ℕ :=
  ([2 * g + 1] ++ dihW k c ++ [2 * g], dihW k c ++ dihW k c)

@[expose] def cubeR (a : ℕ) : List ℕ × List ℕ := ([2 * a, 2 * a, 2 * a], [])

@[expose] def commR (a b : ℕ) : List ℕ × List ℕ := ([2 * b, 2 * a], [2 * a, 2 * b])

@[expose] def yxR (x y z : ℕ) : List ℕ × List ℕ := ([2 * y, 2 * x, 2 * y + 1], [2 * z, 2 * x])

@[expose] def invR (k h x : ℕ) : List ℕ × List ℕ :=
  ([2 * k + 1, 2 * h + 1, 2 * x, 2 * h, 2 * k], [2 * h + 1, 2 * x + 1, 2 * h])

section Shapes

variable {E : List (List ℕ)} {ℓ : ℕ → Equiv.Perm (Fin 3510)}

theorem rp_dihW (k c : ℕ) :
    refsPerm ℓ E (dihW k c) = ev ℓ E k * (ev ℓ E c * ev ℓ E k * (ev ℓ E c)⁻¹) := by
  simp [dihW, refsPerm, refPerm_two_mul, refPerm_two_mul_add_one, mul_assoc]

theorem rp_dihR (k c p : ℕ) :
    refsPerm ℓ E (dihR k c p).1 = (ev ℓ E k * (ev ℓ E c * ev ℓ E k * (ev ℓ E c)⁻¹)) ^ p := by
  rw [dihR, refsPerm_flatten_replicate, rp_dihW]

theorem rp_sqR (k c g : ℕ) :
    refsPerm ℓ E (sqR k c g).1 =
      ev ℓ E g * (ev ℓ E k * (ev ℓ E c * ev ℓ E k * (ev ℓ E c)⁻¹)) * (ev ℓ E g)⁻¹ ∧
    refsPerm ℓ E (sqR k c g).2 = (ev ℓ E k * (ev ℓ E c * ev ℓ E k * (ev ℓ E c)⁻¹)) ^ 2 := by
  refine ⟨?_, ?_⟩
  · rw [sqR, refsPerm_append, refsPerm_append, rp_dihW]
    simp [refsPerm, refPerm_two_mul, refPerm_two_mul_add_one, mul_assoc]
  · rw [sqR, refsPerm_append, rp_dihW, sq]

theorem rp_cubeR (a : ℕ) : refsPerm ℓ E (cubeR a).1 = ev ℓ E a ^ 3 ∧ refsPerm ℓ E (cubeR a).2 = 1 := by
  refine ⟨?_, rfl⟩
  simp [cubeR, refsPerm, refPerm_two_mul, pow_three, mul_assoc]

theorem rp_commR (a b : ℕ) : refsPerm ℓ E (commR a b).1 = ev ℓ E a * ev ℓ E b ∧
    refsPerm ℓ E (commR a b).2 = ev ℓ E b * ev ℓ E a := by
  simp [commR, refsPerm, refPerm_two_mul]

theorem rp_yxR (x y z : ℕ) : refsPerm ℓ E (yxR x y z).1 = (ev ℓ E y)⁻¹ * ev ℓ E x * ev ℓ E y ∧
    refsPerm ℓ E (yxR x y z).2 = ev ℓ E x * ev ℓ E z := by
  simp [yxR, refsPerm, refPerm_two_mul, refPerm_two_mul_add_one, mul_assoc]

theorem rp_invR (k h x : ℕ) : refsPerm ℓ E (invR k h x).1 =
      ev ℓ E k * (ev ℓ E h * ev ℓ E x * (ev ℓ E h)⁻¹) * (ev ℓ E k)⁻¹ ∧
    refsPerm ℓ E (invR k h x).2 = (ev ℓ E h * ev ℓ E x * (ev ℓ E h)⁻¹)⁻¹ := by
  simp [invR, refsPerm, refPerm_two_mul, refPerm_two_mul_add_one, mul_assoc]

end Shapes

section Certs2


theorem rel {i : ℕ} {rl : List ℕ × List ℕ} (hrl : CFSG.KD.W4F22.rels.getD i ([], []) = rl)
    (hc : relK i = true) (h1 : refsPerm ℓF CFSG.KD.W4F22.E rl.1 ∈ fi22P)
    (h2 : refsPerm ℓF CFSG.KD.W4F22.E rl.2 ∈ fi22P) :
    refsPerm ℓF CFSG.KD.W4F22.E rl.1 = refsPerm ℓF CFSG.KD.W4F22.E rl.2 := by
  have hc' : relB 12 8 LF CFSG.KD.W4F22.E [0, 1, 2, 3, 6, 4] rl = true := by
    rw [← hrl]
    exact hc
  exact eq_of_relB letters wordOK Fi22Base.baseOf_fi22P h1 h2 hc'

theorem mov {i : ℕ} {m : List ℕ} (hm : (CFSG.KD.W4F22.movs.getD i ([], 0)).1 = m)
    (hc : movK i = true) : refsPerm ℓF CFSG.KD.W4F22.E m ≠ 1 := by
  unfold movK at hc
  rw [← hm]
  exact movB_sound letters wordOK (Nat.blt_eq.mp (band_left hc)) (band_right hc)

theorem dih_order {k c p i j : ℕ} [Fact p.Prime] (hk : k < 6) (hc6 : 6 ≤ c)
    (hrl : CFSG.KD.W4F22.rels.getD i ([], []) = dihR k c p) (hi : relK i = true)
    (hm : (CFSG.KD.W4F22.movs.getD j ([], 0)).1 = dihW k c) (hj : movK j = true) :
    orderOf (fi22ExtRep k * (vE c * fi22ExtRep k * (vE c)⁻¹)) = p := by
  have hx : fi22ExtRep k * (vE c * fi22ExtRep k * (vE c)⁻¹) ∈ fi22P := by
    have h := dih_mem hk (vE_mem hc6)
    simpa only [mul_assoc] using h
  have hx' : vE k * (vE c * vE k * (vE c)⁻¹) ∈ fi22P := by
    rw [vE_T hk]
    exact hx
  have h1 : refsPerm ℓF CFSG.KD.W4F22.E (dihR k c p).1 ∈ fi22P := by
    rw [rp_dihR]
    exact fi22P.pow_mem hx' p
  have hr := rel hrl hi h1 fi22P.one_mem
  have hn := mov hm hj
  rw [rp_dihR] at hr
  rw [rp_dihW] at hn
  change (vE k * (vE c * vE k * (vE c)⁻¹)) ^ p = 1 at hr
  change vE k * (vE c * vE k * (vE c)⁻¹) ≠ 1 at hn
  rw [vE_T hk] at hr hn
  exact orderOf_eq_prime hr hn

theorem cube_of {i a : ℕ} (ha : 6 ≤ a) (hrl : CFSG.KD.W4F22.rels.getD i ([], []) = cubeR a)
    (hc : relK i = true) : vE a ^ 3 = 1 := by
  have h1 : refsPerm ℓF CFSG.KD.W4F22.E (cubeR a).1 ∈ fi22P := by
    rw [(rp_cubeR a).1]
    exact fi22P.pow_mem (vE_mem ha) 3
  have h2 : refsPerm ℓF CFSG.KD.W4F22.E (cubeR a).2 ∈ fi22P := by
    rw [(rp_cubeR a).2]
    exact fi22P.one_mem
  have h := rel hrl hc h1 h2
  rwa [(rp_cubeR a).1, (rp_cubeR a).2] at h

theorem comm_of {i a b : ℕ} (ha : 6 ≤ a) (hb : 6 ≤ b)
    (hrl : CFSG.KD.W4F22.rels.getD i ([], []) = commR a b) (hc : relK i = true) :
    vE a * vE b = vE b * vE a := by
  have h1 : refsPerm ℓF CFSG.KD.W4F22.E (commR a b).1 ∈ fi22P := by
    rw [(rp_commR a b).1]
    exact fi22P.mul_mem (vE_mem ha) (vE_mem hb)
  have h2 : refsPerm ℓF CFSG.KD.W4F22.E (commR a b).2 ∈ fi22P := by
    rw [(rp_commR a b).2]
    exact fi22P.mul_mem (vE_mem hb) (vE_mem ha)
  have h := rel hrl hc h1 h2
  rwa [(rp_commR a b).1, (rp_commR a b).2] at h

theorem yx_of {i x y z : ℕ} (hx : 6 ≤ x) (hy : 6 ≤ y) (hz : 6 ≤ z)
    (hrl : CFSG.KD.W4F22.rels.getD i ([], []) = yxR x y z) (hc : relK i = true) :
    (vE y)⁻¹ * vE x * vE y = vE x * vE z := by
  have h1 : refsPerm ℓF CFSG.KD.W4F22.E (yxR x y z).1 ∈ fi22P := by
    rw [(rp_yxR x y z).1]
    exact fi22P.mul_mem (fi22P.mul_mem (fi22P.inv_mem (vE_mem hy)) (vE_mem hx)) (vE_mem hy)
  have h2 : refsPerm ℓF CFSG.KD.W4F22.E (yxR x y z).2 ∈ fi22P := by
    rw [(rp_yxR x y z).2]
    exact fi22P.mul_mem (vE_mem hx) (vE_mem hz)
  have h := rel hrl hc h1 h2
  rwa [(rp_yxR x y z).1, (rp_yxR x y z).2] at h

theorem inv_of {i k h x : ℕ} (hk : k < 6) (hh : 6 ≤ h) (hx : 6 ≤ x)
    (hrl : CFSG.KD.W4F22.rels.getD i ([], []) = invR k h x) (hc : relK i = true) :
    fi22ExtRep k * (vE h * vE x * (vE h)⁻¹) * (fi22ExtRep k)⁻¹ = (vE h * vE x * (vE h)⁻¹)⁻¹ := by
  have hm : vE h * vE x * (vE h)⁻¹ ∈ fi22P :=
    fi22P.mul_mem (fi22P.mul_mem (vE_mem hh) (vE_mem hx)) (fi22P.inv_mem (vE_mem hh))
  have h1 : refsPerm ℓF CFSG.KD.W4F22.E (invR k h x).1 ∈ fi22P := by
    rw [(rp_invR k h x).1]
    change vE k * (vE h * vE x * (vE h)⁻¹) * (vE k)⁻¹ ∈ fi22P
    rw [vE_T hk]
    exact conj_mem_P (t_mem_R hk) hm
  have h2 : refsPerm ℓF CFSG.KD.W4F22.E (invR k h x).2 ∈ fi22P := by
    rw [(rp_invR k h x).2]
    exact fi22P.inv_mem hm
  have e := rel hrl hc h1 h2
  rw [(rp_invR k h x).1, (rp_invR k h x).2] at e
  change vE k * (vE h * vE x * (vE h)⁻¹) * (vE k)⁻¹ = (vE h * vE x * (vE h)⁻¹)⁻¹ at e
  rwa [vE_T hk] at e

end Certs2

theorem heis3 {G : Type*} [Group G] {x y : Fin 3 → G} {z : G} (hx3 : ∀ i, x i ^ 3 = 1)
    (hz3 : z ^ 3 = 1) (hxz : ∀ i, x i * z = z * x i) (hyz : ∀ i, y i * z = z * y i)
    (hyx : ∀ i, (y i)⁻¹ * x i * y i = x i * z) (hx01 : x 0 * x 1 = x 1 * x 0)
    (hx02 : x 0 * x 2 = x 2 * x 0) (hx12 : x 1 * x 2 = x 2 * x 1) (hy01 : y 0 * y 1 = y 1 * y 0)
    (hy02 : y 0 * y 2 = y 2 * y 0) (hy12 : y 1 * y 2 = y 2 * y 1)
    (hxy : ∀ i j, i ≠ j → x i * y j = y j * x i) (hz1 : z ≠ 1) : HeisCfg 3 3 x y z where
  xp := hx3
  zp := hz3
  zx := hxz
  zy := hyz
  yx := hyx
  xx i j := by
    fin_cases i <;> fin_cases j <;>
      first | rfl | exact hx01 | exact hx01.symm | exact hx02 | exact hx02.symm | exact hx12 |
        exact hx12.symm
  yy i j _ := by
    fin_cases i <;> fin_cases j <;>
      first | rfl | exact hy01 | exact hy01.symm | exact hy02 | exact hy02.symm | exact hy12 |
        exact hy12.symm
  xy := hxy
  z1 := hz1

theorem heisCfg_conj' {x y : Fin 3 → Equiv.Perm (Fin 3510)} {z : Equiv.Perm (Fin 3510)}
    (hxP : ∀ i, x i ∈ fi22P) (hyP : ∀ i, y i ∈ fi22P) (hzP : z ∈ fi22P)
    (hcfg : HeisCfg 3 3 x y z) (hy3 : ∀ i, y i ^ 3 = 1) {h t : Equiv.Perm (Fin 3510)}
    (hhP : h ∈ fi22P) (hinv : t * (h * x 0 * h⁻¹) * t⁻¹ = (h * x 0 * h⁻¹)⁻¹) :
    ∃ (x' y' : Fin 3 → Equiv.Perm (Fin 3510)) (z' : Equiv.Perm (Fin 3510)),
      (∀ i, x' i ∈ fi22P) ∧ (∀ i, y' i ∈ fi22P) ∧ z' ∈ fi22P ∧ HeisCfg 3 3 x' y' z' ∧
        (∀ i, y' i ^ 3 = 1) ∧ t * x' 0 * t⁻¹ = (x' 0)⁻¹ := by
  let f := (MulAut.conj h).toMonoidHom
  have hf : ∀ g, f g = h * g * h⁻¹ := fun g => rfl
  have hmem : ∀ {g}, g ∈ fi22P → f g ∈ fi22P := fun hg =>
    (hf _).symm ▸ fi22P.mul_mem (fi22P.mul_mem hhP hg) (fi22P.inv_mem hhP)
  have hfz : f z ≠ 1 := by
    rw [hf]
    intro e
    apply hcfg.z1
    calc z = h⁻¹ * (h * z * h⁻¹) * h := by group
      _ = 1 := by rw [e]; group
  refine ⟨fun i => f (x i), fun i => f (y i), f z, fun i => hmem (hxP i), fun i => hmem (hyP i),
    hmem hzP, hcfg.map f hfz, fun i => by rw [← map_pow, hy3 i, map_one], ?_⟩
  change t * f (x 0) * t⁻¹ = (f (x 0))⁻¹
  rw [hf]
  exact hinv

section Facts


theorem z_facts : vE 23 ^ 3 = 1 ∧ vE 23 ≠ 1 := by
  refine ⟨cube_of (a := 23) (by norm_num) rfl w4f22r5, ?_⟩
  have h := mov (i := 4) (m := [2 * 23]) rfl w4f22m4
  rw [refsPerm_cons, refPerm_two_mul] at h
  simpa [refsPerm, vE] using h

theorem cfgA : HeisCfg 3 3 ![vE 11, vE 12, vE 13] ![vE 14, vE 15, vE 16] (vE 23) ∧
    ∀ i, (![vE 14, vE 15, vE 16] i) ^ 3 = 1 := by
  have hy3 : ∀ i, (![vE 14, vE 15, vE 16] i) ^ 3 = 1 := by
    intro i
    fin_cases i
    · exact cube_of (a := 14) (by norm_num) rfl w4f22r7
    · exact cube_of (a := 15) (by norm_num) rfl w4f22r12
    · exact cube_of (a := 16) (by norm_num) rfl w4f22r17
  refine ⟨heis3 ?_ z_facts.1 ?_ ?_ ?_ (comm_of (a := 11) (b := 12) (by norm_num) (by norm_num) rfl
    w4f22r21) (comm_of (a := 11) (b := 13) (by norm_num) (by norm_num) rfl w4f22r23)
    (comm_of (a := 12) (b := 13) (by norm_num) (by norm_num) rfl w4f22r25)
    (comm_of (a := 14) (b := 15) (by norm_num) (by norm_num) rfl w4f22r22)
    (comm_of (a := 14) (b := 16) (by norm_num) (by norm_num) rfl w4f22r24)
    (comm_of (a := 15) (b := 16) (by norm_num) (by norm_num) rfl w4f22r26) ?_ z_facts.2, hy3⟩
  · intro i
    fin_cases i
    · exact cube_of (a := 11) (by norm_num) rfl w4f22r6
    · exact cube_of (a := 12) (by norm_num) rfl w4f22r11
    · exact cube_of (a := 13) (by norm_num) rfl w4f22r16
  · intro i
    fin_cases i
    · exact comm_of (a := 11) (b := 23) (by norm_num) (by norm_num) rfl w4f22r8
    · exact comm_of (a := 12) (b := 23) (by norm_num) (by norm_num) rfl w4f22r13
    · exact comm_of (a := 13) (b := 23) (by norm_num) (by norm_num) rfl w4f22r18
  · intro i
    fin_cases i
    · exact comm_of (a := 14) (b := 23) (by norm_num) (by norm_num) rfl w4f22r9
    · exact comm_of (a := 15) (b := 23) (by norm_num) (by norm_num) rfl w4f22r14
    · exact comm_of (a := 16) (b := 23) (by norm_num) (by norm_num) rfl w4f22r19
  · intro i
    fin_cases i
    · exact yx_of (x := 11) (y := 14) (z := 23) (by norm_num) (by norm_num) (by norm_num) rfl
        w4f22r10
    · exact yx_of (x := 12) (y := 15) (z := 23) (by norm_num) (by norm_num) (by norm_num) rfl
        w4f22r15
    · exact yx_of (x := 13) (y := 16) (z := 23) (by norm_num) (by norm_num) (by norm_num) rfl
        w4f22r20
  · intro i j hij
    fin_cases i <;> fin_cases j
    · exact absurd rfl hij
    · exact comm_of (a := 11) (b := 15) (by norm_num) (by norm_num) rfl w4f22r27
    · exact comm_of (a := 11) (b := 16) (by norm_num) (by norm_num) rfl w4f22r28
    · exact comm_of (a := 12) (b := 14) (by norm_num) (by norm_num) rfl w4f22r29
    · exact absurd rfl hij
    · exact comm_of (a := 12) (b := 16) (by norm_num) (by norm_num) rfl w4f22r30
    · exact comm_of (a := 13) (b := 14) (by norm_num) (by norm_num) rfl w4f22r31
    · exact comm_of (a := 13) (b := 15) (by norm_num) (by norm_num) rfl w4f22r32
    · exact absurd rfl hij

theorem cfgC : HeisCfg 3 3 ![vE 17, vE 18, vE 19] ![vE 20, vE 21, vE 22] (vE 23) ∧
    ∀ i, (![vE 20, vE 21, vE 22] i) ^ 3 = 1 := by
  have hy3 : ∀ i, (![vE 20, vE 21, vE 22] i) ^ 3 = 1 := by
    intro i
    fin_cases i
    · exact cube_of (a := 20) (by norm_num) rfl w4f22r34
    · exact cube_of (a := 21) (by norm_num) rfl w4f22r39
    · exact cube_of (a := 22) (by norm_num) rfl w4f22r44
  refine ⟨heis3 ?_ z_facts.1 ?_ ?_ ?_ (comm_of (a := 17) (b := 18) (by norm_num) (by norm_num) rfl
    w4f22r48) (comm_of (a := 17) (b := 19) (by norm_num) (by norm_num) rfl w4f22r50)
    (comm_of (a := 18) (b := 19) (by norm_num) (by norm_num) rfl w4f22r52)
    (comm_of (a := 20) (b := 21) (by norm_num) (by norm_num) rfl w4f22r49)
    (comm_of (a := 20) (b := 22) (by norm_num) (by norm_num) rfl w4f22r51)
    (comm_of (a := 21) (b := 22) (by norm_num) (by norm_num) rfl w4f22r53) ?_ z_facts.2, hy3⟩
  · intro i
    fin_cases i
    · exact cube_of (a := 17) (by norm_num) rfl w4f22r33
    · exact cube_of (a := 18) (by norm_num) rfl w4f22r38
    · exact cube_of (a := 19) (by norm_num) rfl w4f22r43
  · intro i
    fin_cases i
    · exact comm_of (a := 17) (b := 23) (by norm_num) (by norm_num) rfl w4f22r35
    · exact comm_of (a := 18) (b := 23) (by norm_num) (by norm_num) rfl w4f22r40
    · exact comm_of (a := 19) (b := 23) (by norm_num) (by norm_num) rfl w4f22r45
  · intro i
    fin_cases i
    · exact comm_of (a := 20) (b := 23) (by norm_num) (by norm_num) rfl w4f22r36
    · exact comm_of (a := 21) (b := 23) (by norm_num) (by norm_num) rfl w4f22r41
    · exact comm_of (a := 22) (b := 23) (by norm_num) (by norm_num) rfl w4f22r46
  · intro i
    fin_cases i
    · exact yx_of (x := 17) (y := 20) (z := 23) (by norm_num) (by norm_num) (by norm_num) rfl
        w4f22r37
    · exact yx_of (x := 18) (y := 21) (z := 23) (by norm_num) (by norm_num) (by norm_num) rfl
        w4f22r42
    · exact yx_of (x := 19) (y := 22) (z := 23) (by norm_num) (by norm_num) (by norm_num) rfl
        w4f22r47
  · intro i j hij
    fin_cases i <;> fin_cases j
    · exact absurd rfl hij
    · exact comm_of (a := 17) (b := 21) (by norm_num) (by norm_num) rfl w4f22r54
    · exact comm_of (a := 17) (b := 22) (by norm_num) (by norm_num) rfl w4f22r55
    · exact comm_of (a := 18) (b := 20) (by norm_num) (by norm_num) rfl w4f22r56
    · exact absurd rfl hij
    · exact comm_of (a := 18) (b := 22) (by norm_num) (by norm_num) rfl w4f22r57
    · exact comm_of (a := 19) (b := 20) (by norm_num) (by norm_num) rfl w4f22r58
    · exact comm_of (a := 19) (b := 21) (by norm_num) (by norm_num) rfl w4f22r59
    · exact absurd rfl hij

theorem w4f22_dihedral :
    (∃ c ∈ fi22P, orderOf (fi22ExtRep 0 * (c * fi22ExtRep 0 * c⁻¹)) = 13) ∧
      (∃ c ∈ fi22P, orderOf (fi22ExtRep 3 * (c * fi22ExtRep 3 * c⁻¹)) = 11) ∧
      ∃ c ∈ fi22P, orderOf (fi22ExtRep 5 * (c * fi22ExtRep 5 * c⁻¹)) = 11 := by
  have : Fact (Nat.Prime 13) := ⟨by norm_num⟩
  have : Fact (Nat.Prime 11) := ⟨by norm_num⟩
  exact ⟨⟨vE 6, vE_mem (by norm_num), dih_order (k := 0) (c := 6) (p := 13) (i := 0) (j := 0)
      (by norm_num) (by norm_num) rfl w4f22r0 rfl w4f22m0⟩,
    ⟨vE 7, vE_mem (by norm_num), dih_order (k := 3) (c := 7) (p := 11) (i := 1) (j := 1)
      (by norm_num) (by norm_num) rfl w4f22r1 rfl w4f22m1⟩,
    vE 8, vE_mem (by norm_num), dih_order (k := 5) (c := 8) (p := 11) (i := 2) (j := 2)
      (by norm_num) (by norm_num) rfl w4f22r2 rfl w4f22m2⟩

theorem w4f22_five :
    ∃ c ∈ fi22P, orderOf (fi22ExtRep 1 * (c * fi22ExtRep 1 * c⁻¹)) = 5 ∧
      ∃ g ∈ fi22P, g * (fi22ExtRep 1 * (c * fi22ExtRep 1 * c⁻¹)) * g⁻¹ =
        (fi22ExtRep 1 * (c * fi22ExtRep 1 * c⁻¹)) ^ 2 := by
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  have hw : vE 1 * (vE 9 * vE 1 * (vE 9)⁻¹) ∈ fi22P := by
    rw [vE_T (k := 1) (by norm_num)]
    simpa only [mul_assoc] using dih_mem (k := 1) (by norm_num) (vE_mem (i := 9) (by norm_num))
  have h1 : refsPerm ℓF CFSG.KD.W4F22.E (sqR 1 9 10).1 ∈ fi22P := by
    rw [(rp_sqR 1 9 10).1]
    exact fi22P.mul_mem (fi22P.mul_mem (vE_mem (by norm_num)) hw)
      (fi22P.inv_mem (vE_mem (by norm_num)))
  have h2 : refsPerm ℓF CFSG.KD.W4F22.E (sqR 1 9 10).2 ∈ fi22P := by
    rw [(rp_sqR 1 9 10).2]
    exact fi22P.pow_mem hw 2
  have e := rel (i := 4) (rl := sqR 1 9 10) rfl w4f22r4 h1 h2
  rw [(rp_sqR 1 9 10).1, (rp_sqR 1 9 10).2] at e
  change vE 10 * (vE 1 * (vE 9 * vE 1 * (vE 9)⁻¹)) * (vE 10)⁻¹ =
    (vE 1 * (vE 9 * vE 1 * (vE 9)⁻¹)) ^ 2 at e
  rw [vE_T (k := 1) (by norm_num)] at e
  exact ⟨vE 9, vE_mem (by norm_num), dih_order (k := 1) (c := 9) (p := 5) (i := 3) (j := 3)
    (by norm_num) (by norm_num) rfl w4f22r3 rfl w4f22m3, vE 10, vE_mem (by norm_num), e⟩

theorem w4f22_heisCfg {k : ℕ} (hk : k < 6) :
    ∃ (x y : Fin 3 → Equiv.Perm (Fin 3510)) (z : Equiv.Perm (Fin 3510)),
      (∀ i, x i ∈ fi22P) ∧ (∀ i, y i ∈ fi22P) ∧ z ∈ fi22P ∧ HeisCfg 3 3 x y z ∧
        (∀ i, y i ^ 3 = 1) ∧ fi22ExtRep k * x 0 * (fi22ExtRep k)⁻¹ = (x 0)⁻¹ := by
  have vmem {a b c : ℕ} (ha : 6 ≤ a) (hb : 6 ≤ b) (hc : 6 ≤ c) :
      ∀ i, ![vE a, vE b, vE c] i ∈ fi22P := by
    intro i
    fin_cases i
    exacts [vE_mem ha, vE_mem hb, vE_mem hc]
  have hzP : vE 23 ∈ fi22P := vE_mem (by norm_num)
  have fA {j h : ℕ} (hj : j < 6) (hh : 6 ≤ h)
      (hinv : fi22ExtRep j * (vE h * vE 11 * (vE h)⁻¹) * (fi22ExtRep j)⁻¹ =
        (vE h * vE 11 * (vE h)⁻¹)⁻¹) :
      ∃ (x y : Fin 3 → Equiv.Perm (Fin 3510)) (z : Equiv.Perm (Fin 3510)),
        (∀ i, x i ∈ fi22P) ∧ (∀ i, y i ∈ fi22P) ∧ z ∈ fi22P ∧ HeisCfg 3 3 x y z ∧
          (∀ i, y i ^ 3 = 1) ∧ fi22ExtRep j * x 0 * (fi22ExtRep j)⁻¹ = (x 0)⁻¹ :=
    heisCfg_conj' (vmem (by norm_num) (by norm_num) (by norm_num))
      (vmem (by norm_num) (by norm_num) (by norm_num)) hzP cfgA.1 cfgA.2 (vE_mem hh) hinv
  have fC {j h : ℕ} (hj : j < 6) (hh : 6 ≤ h)
      (hinv : fi22ExtRep j * (vE h * vE 17 * (vE h)⁻¹) * (fi22ExtRep j)⁻¹ =
        (vE h * vE 17 * (vE h)⁻¹)⁻¹) :
      ∃ (x y : Fin 3 → Equiv.Perm (Fin 3510)) (z : Equiv.Perm (Fin 3510)),
        (∀ i, x i ∈ fi22P) ∧ (∀ i, y i ∈ fi22P) ∧ z ∈ fi22P ∧ HeisCfg 3 3 x y z ∧
          (∀ i, y i ^ 3 = 1) ∧ fi22ExtRep j * x 0 * (fi22ExtRep j)⁻¹ = (x 0)⁻¹ :=
    heisCfg_conj' (vmem (by norm_num) (by norm_num) (by norm_num))
      (vmem (by norm_num) (by norm_num) (by norm_num)) hzP cfgC.1 cfgC.2 (vE_mem hh) hinv
  interval_cases k
  · exact fA (h := 24) (by norm_num) (by norm_num)
      (inv_of (i := 60) (by norm_num) (by norm_num) (by norm_num) rfl w4f22r60)
  · exact fA (h := 25) (by norm_num) (by norm_num)
      (inv_of (i := 61) (by norm_num) (by norm_num) (by norm_num) rfl w4f22r61)
  · exact fA (h := 26) (by norm_num) (by norm_num)
      (inv_of (i := 62) (by norm_num) (by norm_num) (by norm_num) rfl w4f22r62)
  · exact fA (h := 27) (by norm_num) (by norm_num)
      (inv_of (i := 63) (by norm_num) (by norm_num) (by norm_num) rfl w4f22r63)
  · exact fC (h := 28) (by norm_num) (by norm_num)
      (inv_of (i := 64) (by norm_num) (by norm_num) (by norm_num) rfl w4f22r64)
  · exact fA (h := 29) (by norm_num) (by norm_num)
      (inv_of (i := 65) (by norm_num) (by norm_num) (by norm_num) rfl w4f22r65)

end Facts

end CertificateChecks.KernelW4F22

end
