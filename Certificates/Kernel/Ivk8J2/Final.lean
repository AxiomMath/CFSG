module

public import Certificates.Kernel.Ivk8J2.Checks
public import Certificates.Kernel.Sporadic.OddCore.J2CnF
public import CFSG.Certificates.Kernel.Ivk8CentSound
public import CFSG.Sporadic.SmallOddCore.J2
public import CFSG.GroupTheory.ABGLocalTools.OddInvolution
import CFSG.Certificates.Kernel.Spor.PcompFacts

public section

namespace CertificateChecks.KernelIvk8J2

open Subgroup CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KS.PEnum CFSG.KS.MulH
  CFSG.KS.Ivk8Cent CFSG.Sporadic.Th CFSG.Sporadic.Th.Native CFSG.Sporadic.Schreier
  CFSG.Sporadic.Schreier.Native CFSG.Sporadic.SmallOddCore CFSG.Sporadic.SmallOddCore.Native
  CertificateChecks.KernelSpor CertificateChecks.KernelSpor.J2Cn

theorem cover_of {K : Subgroup (Equiv.Perm (Fin 315))} {E : Array Table}
    (hE : ∀ k < E.size, ∃ c ∈ K, Rep 315 E[k]! c) (hd : hkeysDistinct 315 E.toList = true)
    (hsz : Nat.card K ≤ E.size) : ∀ y ∈ K, ∃ k, ∃ hk : k < E.size, Rep 315 E[k] y := by
  have hrep : ∀ k < E.size, Rep 315 E[k]! (tablePerm 315 E[k]!) := fun k hk => by
    obtain ⟨c, -, h⟩ := hE k hk
    rw [tablePerm_eq h]
    exact h
  have hnd := nodup_of_hkeysDistinct (forall₂_tablePerm hrep) hd
  intro y hy
  have hmem := mem_of_nodup_of_card_le hnd (K := K) (fun x hx => by
      obtain ⟨k, hk, rfl⟩ := mem_map_tablePerm hrep hx
      obtain ⟨c, hc, h⟩ := hE k hk
      rw [tablePerm_eq h]
      exact hc)
    (by rw [List.length_map, Array.length_toList]; exact hsz) y hy
  obtain ⟨k, hk, rfl⟩ := mem_map_tablePerm hrep hmem
  refine ⟨k, hk, ?_⟩
  have h := hrep k hk
  rwa [getElem!_pos E k hk] at h ⊢

theorem order_of_queue {K : Subgroup (Equiv.Perm (Fin 315))} {Q : Array Table}
    {x y : Equiv.Perm (Fin 315)} (hQ : ∀ j < Q.size, ∃ c ∈ K, Rep 315 Q[j]! (c * x * c⁻¹))
    {T : Table} (hy : Rep 315 T y) (hm : memT 315 Q T = true) : orderOf y = orderOf x := by
  have hrep : ∀ j < Q.size, Rep 315 Q[j]! (tablePerm 315 Q[j]!) := fun j hj => by
    obtain ⟨c, -, h⟩ := hQ j hj
    rw [tablePerm_eq h]
    exact h
  obtain ⟨j, hj, rfl⟩ := memT_spec hrep hy hm
  obtain ⟨c, -, h⟩ := hQ j hj
  rw [tablePerm_eq h, show c * x * c⁻¹ = (MulAut.conj c) x by simp, MulEquiv.orderOf_eq]

theorem entry_of_queue {K : Subgroup (Equiv.Perm (Fin 315))} {cnt : Nat} {TQ PLQ : Nat → Nat}
    {x y : Equiv.Perm (Fin 315)}
    (hQ : ∀ j < (hRec 315 9 cnt TQ PLQ).1.size, ∃ c ∈ K,
      Rep 315 (hRec 315 9 cnt TQ PLQ).1[j]! (c * x * c⁻¹))
    (hc : ∀ i < cnt, canonK 315 9 (mask 9) (315 * 9) (TQ i) = true)
    {T : Table} (hy : Rep 315 T y) (hm : memT 315 (hRec 315 9 cnt TQ PLQ).1 T = true) :
    ∃ i < cnt, PR 315 9 (TQ i) y := by
  have hrep : ∀ j < (hRec 315 9 cnt TQ PLQ).1.size,
      Rep 315 (hRec 315 9 cnt TQ PLQ).1[j]! (tablePerm 315 (hRec 315 9 cnt TQ PLQ).1[j]!) :=
    fun j hj => by
      obtain ⟨c, -, h⟩ := hQ j hj
      rw [tablePerm_eq h]
      exact h
  obtain ⟨j, hj, hyj⟩ := memT_spec hrep hy hm
  have hj' := rec_lt hj
  refine ⟨j, hj', hc j hj', ?_⟩
  have h := hrep j hj
  rw [← hyj, getElem!_pos _ j hj, rec_get hj] at h
  exact h

theorem gens_of {a k t : Nat} (hk : a + k ≤ 42) (ht : t < 42)
    (h : allN k (fun j => bAnd(sK (F (Nat.add a j)), commK (F (Nat.add a j)) (F t))) = true)
    {K : Subgroup (Equiv.Perm (Fin 315))}
    (hK : closure (tp 315 '' {x | x ∈ (cgL a k).toArray}) = K) :
    ∀ l < (cgL a k).toArray.size, Rep 315 (cgL a k).toArray[l]! (tp 315 (cgL a k).toArray[l]!) ∧
      Rep 315 ((cgL a k).toArray.map (invT 315))[l]! (tp 315 (cgL a k).toArray[l]!)⁻¹ ∧
      tp 315 (cgL a k).toArray[l]! ∈ K := by
  intro l hl
  have h1 := Array.all_eq_true.1 (cg_all a k t hk ht h) l hl
  rw [← getElem!_pos _ l hl] at h1
  simp only [Bool.and_eq_true] at h1
  have hr := rep_tp h1.1.1.1
  refine ⟨hr, ?_, ?_⟩
  · rw [getElem!_pos _ l (by simpa using hl), Array.getElem_map, ← getElem!_pos _ l hl]
    exact rep_invT hr h1.2
  · rw [← hK]
    exact subset_closure ⟨_, getElem!_mem_array hl, rfl⟩

theorem ord_rep {r p t : Nat} (hr : r < 42) (ht : t < 42) (h : oddK r p t = true)
    (hdp : CFSG.Sporadic.Schreier.Native.divParts p = [1]) (hp : 0 < p) :
    orderOf (tp 315 (j2CentTbl r)) = p :=
  (ordTest_iff_perm (rep_tp (permF hr)) hp).1 (oddF hr ht h hdp).2.2.2

theorem row_cent
    {i : Nat} (hi : i < j2Rows.length) {t : Table}
    {cg : List Table} {N : Nat} (h1 : (j2Rows[i]'hi).rep = t) (h2 : (j2Rows[i]'hi).centGens = cg)
    (h3 : (j2Rows[i]'hi).centOrder = N) :
    closure (tp 315 '' {x | x ∈ cg.toArray}) =
        j2P ⊓ centralizer ({tp 315 t} : Set (Equiv.Perm (Fin 315))) ∧
      Nat.card ↥(j2P ⊓ centralizer ({tp 315 t} : Set (Equiv.Perm (Fin 315)))) = N := by
  obtain ⟨-, -, -, hrows, -⟩ := ctuc_j2_all_involution_fixed_subgroups_odd_core_trivial
  obtain ⟨-, -, -, hK, hcard, -⟩ := hrows _ (List.getElem_mem hi)
  unfold CFSG.Sporadic.SmallOddCore.j2C at hK
  rw [h1, h2] at hK
  rw [h1, h3] at hcard
  exact ⟨hK, hcard⟩

theorem dom31
    {y : Equiv.Perm (Fin 315)}
    (hy : y ∈ j2P ⊓ centralizer ({tp 315 (j2CentTbl 31)} : Set (Equiv.Perm (Fin 315))))
    (h3 : orderOf y = 3) : ∃ i < J2Q3a.cnt, PR 315 9 (J2Q3a.T i) y := by
  obtain ⟨hK', hcard'⟩ := row_cent (i := 2) (by decide) (t := j2CentTbl 31) (cg := cgL 32 4)
    (N := 1920) (by simp [j2Rows]) (by simp [j2Rows]; rfl) (by simp [j2Rows])
  set K := j2P ⊓ centralizer ({tp 315 (j2CentTbl 31)} : Set (Equiv.Perm (Fin 315)))
  have hg := gens_of (by norm_num) (by norm_num) kcg.2.2 hK'
  have hE := mulTreeOK_spec (by norm_num) K (gg := fun l => tp 315 (cgL 32 4).toArray[l]!)
    (fun l hl => ⟨(hg l hl).1, (hg l hl).2.2⟩) recC2.2.1
  obtain ⟨k, hk, hyk⟩ := cover_of hE recC2.2.2 (le_of_eq (by rw [hcard', hRec_size, hc2])) y hy
  have hs := Array.all_eq_true.1 sel3 k hk
  have hsel : selOK 315 [3, 5] (hRec 315 9 J2C2.cnt J2C2.T J2C2.PL).1[k] = true := by
    rw [selOK_iff (by norm_num) hyk]
    refine ⟨fun e => ?_, 3, by simp, by rw [← h3]; exact pow_orderOf_eq_one y⟩
    rw [e, orderOf_one] at h3
    exact absurd h3 (by norm_num)
  rw [hsel, Bool.not_true, Bool.false_or, Bool.or_eq_true, Bool.or_eq_true] at hs
  have hQ := fun r (hr : r < 42) {Q : Array Table} {par lab : Array Nat}
      (hq : conjTreeOK 315 (cgL 32 4).toArray ((cgL 32 4).toArray.map (invT 315)) (j2CentTbl r)
        Q par lab = true) =>
    conjTreeOK_spec K (gg := fun l => tp 315 (cgL 32 4).toArray[l]!) hg (rep_tp (permF hr)) hq
  rcases hs with h1 | h1 | h1
  · exact entry_of_queue (hQ 36 (by norm_num) recQ3a.2.1) (canonR (pe_all' q3aE)) hyk h1
  · have := order_of_queue (hQ 38 (by norm_num) recQ3b.2.1) hyk h1
    rw [h3, ord_rep (by norm_num) (by norm_num) kodd.2.2.2.2.2.2.1 (by decide) (by norm_num)] at this
    exact absurd this (by norm_num)
  · have := order_of_queue (hQ 40 (by norm_num) recQ3c.2.1) hyk h1
    rw [h3, ord_rep (by norm_num) (by norm_num) kodd.2.2.2.2.2.2.2 (by decide) (by norm_num)] at this
    exact absurd this (by norm_num)

theorem dom17
    {y : Equiv.Perm (Fin 315)}
    (hy : y ∈ j2P ⊓ centralizer ({tp 315 (j2CentTbl 17)} : Set (Equiv.Perm (Fin 315))))
    (h3 : orderOf y = 3) : ∃ i < J2Q2c.cnt, PR 315 9 (J2Q2c.T i) y := by
  obtain ⟨hK', hcard'⟩ := row_cent (i := 1) (by decide) (t := j2CentTbl 17) (cg := cgL 18 5)
    (N := 240) (by simp [j2Rows]) (by simp [j2Rows]; rfl) (by simp [j2Rows])
  set K := j2P ⊓ centralizer ({tp 315 (j2CentTbl 17)} : Set (Equiv.Perm (Fin 315)))
  have hg := gens_of (by norm_num) (by norm_num) kcg.2.1 hK'
  have hE := mulTreeOK_spec (by norm_num) K (gg := fun l => tp 315 (cgL 18 5).toArray[l]!)
    (fun l hl => ⟨(hg l hl).1, (hg l hl).2.2⟩) recC1.2.1
  obtain ⟨k, hk, hyk⟩ := cover_of hE recC1.2.2 (le_of_eq (by rw [hcard', hRec_size, hc1])) y hy
  have hs := Array.all_eq_true.1 sel2 k hk
  have hsel : selOK 315 [3, 5] (hRec 315 9 J2C1.cnt J2C1.T J2C1.PL).1[k] = true := by
    rw [selOK_iff (by norm_num) hyk]
    refine ⟨fun e => ?_, 3, by simp, by rw [← h3]; exact pow_orderOf_eq_one y⟩
    rw [e, orderOf_one] at h3
    exact absurd h3 (by norm_num)
  rw [hsel, Bool.not_true, Bool.false_or, Bool.or_eq_true, Bool.or_eq_true] at hs
  have hQ := fun r (hr : r < 42) {Q : Array Table} {par lab : Array Nat}
      (hq : conjTreeOK 315 (cgL 18 5).toArray ((cgL 18 5).toArray.map (invT 315)) (j2CentTbl r)
        Q par lab = true) =>
    conjTreeOK_spec K (gg := fun l => tp 315 (cgL 18 5).toArray[l]!) hg (rep_tp (permF hr)) hq
  rcases hs with h1 | h1 | h1
  · have := order_of_queue (hQ 23 (by norm_num) recQ2a.2.1) hyk h1
    rw [h3, ord_rep (by norm_num) (by norm_num) kodd.2.2.1 (by decide) (by norm_num)] at this
    exact absurd this (by norm_num)
  · have := order_of_queue (hQ 26 (by norm_num) recQ2b.2.1) hyk h1
    rw [h3, ord_rep (by norm_num) (by norm_num) kodd.2.2.2.1 (by decide) (by norm_num)] at this
    exact absurd this (by norm_num)
  · exact entry_of_queue (hQ 29 (by norm_num) recQ2c.2.1) (canonR (pe_all' q2cE)) hyk h1

@[expose] noncomputable def gl (l : Nat) : Equiv.Perm (Fin 315) :=
  if l = 0 then j2Gen 0 else if l = 1 then j2Gen 1 else if l = 2 then (j2Gen 0)⁻¹ else (j2Gen 1)⁻¹

theorem pr_S {j : Nat}
    (hj : j < 2) : PR 315 9 (J2P.S j) (j2Gen j) := by
  have hsz : j2PGTbls.size = 2 := rfl
  refine ⟨Sc hj, ?_⟩
  have h := j2_groupData.rep j (by rw [hsz]; exact hj)
  rwa [(pg_tabs.2 j hj).1] at h

theorem pr_SI {j : Nat}
    (hj : j < 2) : PR 315 9 (J2P.SI j) (j2Gen j)⁻¹ :=
  ⟨SIc hj, Rep.inv_of_invOK (pr_S hj).2
    (invOK_unpack (Sc hj) (SIc hj) (allN_spec J2PC.permP j (by omega)))⟩

theorem beq_ne {l m : Nat} (h : l ≠ m) : Nat.beq l m = false := by
  cases e : Nat.beq l m
  · rfl
  · exact absurd (Nat.eq_of_beq_eq_true e) h

theorem pr_lt (l : Nat) :
    PR 315 9 (lt l) (gl l) := by
  unfold lt gl
  by_cases h0 : l = 0
  · subst h0
    exact pr_S (by norm_num)
  by_cases h1 : l = 1
  · subst h1
    exact pr_S (by norm_num)
  by_cases h2 : l = 2
  · subst h2
    exact pr_SI (by norm_num)
  rw [if_neg h0, if_neg h1, if_neg h2, beq_ne h0, beq_ne h1, beq_ne h2]
  exact pr_SI (by norm_num)

theorem gl_mem (l : Nat) : gl l ∈ j2P := by
  have h0 : j2Gen 0 ∈ j2P := subset_closure (by simp)
  have h1 : j2Gen 1 ∈ j2P := subset_closure (by simp)
  unfold gl
  split_ifs
  · exact h0
  · exact h1
  · exact inv_mem h0
  · exact inv_mem h1

@[expose] noncomputable def pw (ws : List Nat) : Equiv.Perm (Fin 315) := (ws.map gl).prod

theorem pw_mem (ws : List Nat) : pw ws ∈ j2P :=
  list_prod_mem fun x hx => by
    obtain ⟨l, -, rfl⟩ := List.mem_map.1 hx
    exact gl_mem l

theorem pr_w (ws : List Nat) :
    PR 315 9 (evW 315 9 lt ws) (pw ws) :=
  evW_rep J2Cn.hn pr_lt ws

theorem hfacts :
    pw wA * pw wA = 1 ∧ pw wB * pw wB = 1 ∧ pw wC * pw wC = 1 ∧
    pw wA * pw wB = pw wB * pw wA ∧ pw wA * pw wC = pw wC * pw wA ∧
    pw wB * pw wC = pw wC * pw wB ∧ pw wC ≠ 1 ∧ pw wA * pw wB ≠ 1 ∧
    pw wC ≠ pw wA * pw wB :=
  hOK_sound J2Cn.hn pr_lt ch5246_h

theorem pr_F {k : Nat} (hk : k < 42) : PR 315 9 (J2CentT.F k) (tp 315 (j2CentTbl k)) :=
  ⟨Fc hk, by
    change Rep 315 (tabT (unpack 315 9 (F k))) _
    rw [← tabF hk]
    exact rep_tp (permF hk)⟩

theorem efacts :
    (pw c1i = (pw c1)⁻¹ ∧ pw c1 * tp 315 (j2CentTbl 17) * (pw c1)⁻¹ = pw wC) ∧
    (pw c2i = (pw c2)⁻¹ ∧ pw c2 * tp 315 (j2CentTbl 31) * (pw c2)⁻¹ = pw wA * pw wB) ∧
    (pw c3i = (pw c3)⁻¹ ∧
      pw c3 * tp 315 (j2CentTbl 17) * (pw c3)⁻¹ = pw wA * pw wB * pw wC) := by
  have h := ch5246_tE
  unfold wH at h
  rw [withH_eq] at h
  beta_reduce at h
  generalize hb1 : conjOK 315 9 (evW 315 9 lt c1) (evW 315 9 lt c1i) (J2CentT.F 17)
    (evW 315 9 lt wC) = b1 at h
  generalize hb2 : conjOK 315 9 (evW 315 9 lt c2) (evW 315 9 lt c2i) (J2CentT.F 31)
    (pc 315 9 (evW 315 9 lt wA) (evW 315 9 lt wB)) = b2 at h
  generalize hb3 : conjOK 315 9 (evW 315 9 lt c3) (evW 315 9 lt c3i) (J2CentT.F 17)
    (pc 315 9 (pc 315 9 (evW 315 9 lt wA) (evW 315 9 lt wB)) (evW 315 9 lt wC)) = b3 at h
  obtain ⟨h1, h⟩ := bAnd_and h
  obtain ⟨h2, h3⟩ := bAnd_and h
  rw [h1] at hb1
  rw [h2] at hb2
  rw [h3] at hb3
  exact ⟨conjOK_sound J2Cn.hn (pr_w c1) (pr_w c1i) (pr_F (by norm_num)) (pr_w wC) hb1,
    conjOK_sound J2Cn.hn (pr_w c2) (pr_w c2i) (pr_F (by norm_num)) ((pr_w wA).pc (pr_w wB)) hb2,
    conjOK_sound J2Cn.hn (pr_w c3) (pr_w c3i) (pr_F (by norm_num))
      (((pr_w wA).pc (pr_w wB)).pc (pr_w wC)) hb3⟩

@[expose] noncomputable def hsP : List (Equiv.Perm (Fin 315)) :=
  [pw wA, pw wB, pw wA * pw wB, pw wC, pw wA * pw wC, pw wB * pw wC, pw wA * pw wB * pw wC]

theorem hs_pr :
    List.Forall₂ (PR 315 9) [evW 315 9 lt wA, evW 315 9 lt wB,
      pc 315 9 (evW 315 9 lt wA) (evW 315 9 lt wB), evW 315 9 lt wC,
      pc 315 9 (evW 315 9 lt wA) (evW 315 9 lt wC), pc 315 9 (evW 315 9 lt wB) (evW 315 9 lt wC),
      pc 315 9 (pc 315 9 (evW 315 9 lt wA) (evW 315 9 lt wB)) (evW 315 9 lt wC)] hsP :=
  .cons (pr_w wA) (.cons (pr_w wB) (.cons ((pr_w wA).pc (pr_w wB)) (.cons (pr_w wC)
    (.cons ((pr_w wA).pc (pr_w wC)) (.cons ((pr_w wB).pc (pr_w wC))
      (.cons (((pr_w wA).pc (pr_w wB)).pc (pr_w wC)) .nil))))))

theorem wit_of {c ci : List Nat}
    {cnt : Nat} {T : Nat → Nat} (h : chkC c ci cnt T = true) (hci : pw ci = (pw c)⁻¹)
    {i : Nat} (hi : i < cnt) {τ : Equiv.Perm (Fin 315)} (hT : PR 315 9 (T i) τ) :
    (∃ a ∈ hsP, (pw c * τ * (pw c)⁻¹ * (a * (pw c * τ * (pw c)⁻¹) * a)) ^ 27 ≠ 1) ∨
      ∃ a ∈ hsP, ∃ b ∈ hsP, (pw c * τ * (pw c)⁻¹ * (a * (pw c * τ * (pw c)⁻¹) * a) *
        (b * (pw c * τ * (pw c)⁻¹) * b)) ^ 27 ≠ 1 := by
  unfold chkC wH at h
  rw [withH_eq] at h
  simp only [PF.strictB_eqP] at h
  have hci' := pr_w ci
  rw [hci] at hci'
  exact chkKP_at J2Cn.hn (pr_w c) hci' hs_pr h hi hT

theorem kleinFour_pair5246 {G : Type*} [Group G] {a b : G} (ha : a * a = 1)
    (hb : b * b = 1) (ha1 : a ≠ 1) (hb1 : b ≠ 1) (hab : a ≠ b) (hc : a * b = b * a) :
    IsKleinFour (closure {a, b}) := by
  have e1 : a * (a * b) = b := by rw [← mul_assoc, ha, one_mul]
  have e2 : a * b * a = b := by rw [mul_assoc, ← hc, ← mul_assoc, ha, one_mul]
  have e3 : b * (a * b) = a := by rw [← mul_assoc, ← hc, mul_assoc, hb, mul_one]
  have e4 : a * b * b = a := by rw [mul_assoc, hb, mul_one]
  have e5 : a * b * (a * b) = 1 := by rw [← mul_assoc, e2, hb]
  let P : G → Prop := fun x => x = 1 ∨ x = a ∨ x = b ∨ x = a * b
  have hmul : ∀ x y, P x → P y → P (x * y) := by
    rintro x y (rfl | rfl | rfl | rfl) (rfl | rfl | rfl | rfl) <;>
      simp only [P, one_mul, mul_one, ha, hb, ← hc, e1, e2, e3, e4, e5, true_or, or_true]
  have hinv : ∀ x, P x → P x⁻¹ := by
    rintro x (rfl | rfl | rfl | rfl)
    · exact Or.inl inv_one
    · exact Or.inr (Or.inl (inv_eq_of_mul_eq_one_right ha))
    · exact Or.inr (Or.inr (Or.inl (inv_eq_of_mul_eq_one_right hb)))
    · exact Or.inr (Or.inr (Or.inr (inv_eq_of_mul_eq_one_right e5)))
  let K : Subgroup G :=
    { carrier := {x | P x}
      mul_mem' := fun hx hy => hmul _ _ hx hy
      one_mem' := Or.inl rfl
      inv_mem' := fun hx => hinv _ hx }
  have hK : closure {a, b} = K := by
    apply le_antisymm
    · rw [closure_le]
      rintro x (rfl | rfl)
      · exact Or.inr (Or.inl rfl)
      · exact Or.inr (Or.inr (Or.inl rfl))
    · rintro x (rfl | rfl | rfl | rfl)
      · exact one_mem _
      · exact subset_closure (Set.mem_insert _ _)
      · exact subset_closure (Set.mem_insert_of_mem _ rfl)
      · exact mul_mem (subset_closure (Set.mem_insert _ _))
          (subset_closure (Set.mem_insert_of_mem _ rfl))
  have hab1 : a * b ≠ 1 := fun h => hab (by
    calc a = a * (b * b) := by rw [hb, mul_one]
      _ = (a * b) * b := by rw [mul_assoc]
      _ = b := by rw [h, one_mul])
  have haab : a ≠ a * b := fun h => hb1 (by rw [← e1, ← h, ha])
  have hbab : b ≠ a * b := fun h => ha1 (by rw [← e4, ← h, hb])
  have hset : (K : Set G) = {1, a, b, a * b} := by
    ext x
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
    rfl
  have hcard : Nat.card K = 4 := by
    rw [← SetLike.coe_sort_coe, hset, Nat.card_coe_set_eq, Set.ncard_insert_of_notMem,
      Set.ncard_insert_of_notMem, Set.ncard_pair hbab]
    · simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
      exact ⟨hab, haab⟩
    · simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
      exact ⟨ha1.symm, hb1.symm, hab1.symm⟩
  have hsq : ∀ x : K, x ^ 2 = 1 := by
    rintro ⟨x, hx⟩
    apply Subtype.ext
    rw [Subgroup.coe_pow, OneMemClass.coe_one, pow_two]
    rcases hx with rfl | rfl | rfl | rfl
    · exact mul_one 1
    · exact ha
    · exact hb
    · exact e5
  rw [hK]
  refine ⟨hcard, ?_⟩
  rcases (Nat.dvd_prime Nat.prime_two).mp (Monoid.exponent_dvd_of_forall_pow_eq_one hsq) with
    h | h
  · have : Subsingleton K := Monoid.exp_eq_one_iff.mp h
    have := Nat.card_of_subsingleton (1 : K)
    omega
  · exact h

theorem conj_into {G : Type*} [Group G] [Finite G] {p : ℕ} [Fact p.Prime] {M Q P : Subgroup G}
    (hP : IsPGroup p P) (hPM : P ≤ M) (hidx : ¬ p ∣ P.relIndex M) (hQM : Q ≤ M)
    (hQp : IsPGroup p Q) : ∃ g ∈ M, ∀ y ∈ Q, g⁻¹ * y * g ∈ P := by
  let S : Sylow p M := (hP.of_equiv (subgroupOfEquivOfLe hPM).symm).toSylow hidx
  have hS : (S : Subgroup M) = P.subgroupOf M := rfl
  have hQ' : IsPGroup p (Q.subgroupOf M) := hQp.of_equiv (subgroupOfEquivOfLe hQM).symm
  obtain ⟨S', hS'⟩ := hQ'.exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq M S S'
  refine ⟨g, g.2, fun y hy => ?_⟩
  have h1 : (⟨y, hQM hy⟩ : M) ∈ (S' : Subgroup M) := hS' hy
  rw [← hg, Sylow.coe_subgroup_smul] at h1
  obtain ⟨s, hs, hsy⟩ := Subgroup.mem_smul_pointwise_iff_exists _ _ _ |>.1 h1
  rw [hS] at hs
  have hs' : (s : G) ∈ P := hs
  have hy' : (g : G) * s * (g : G)⁻¹ = y := congrArg Subtype.val hsy
  have e : (g : G)⁻¹ * y * g = s := by
    rw [← hy']
    group
  rw [e]
  exact hs'

theorem noThree_j2P :
    ∀ S W : Subgroup (Equiv.Perm (Fin 315)), S ≤ j2P →
    W ≤ j2P → Nat.card S = 2 ^ 7 → IsPGroup 3 W →
    S ≤ normalizer (W : Set (Equiv.Perm (Fin 315))) → W = ⊥ := by
  intro S W hS hW hcard hW3 hSW
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨hA2, hB2, hC2, hAB, hAC, hBC, hC1, hAB1, hCAB⟩ := hfacts
  obtain ⟨⟨e1i, e1⟩, ⟨e2i, e2⟩, ⟨e3i, e3⟩⟩ := efacts
  set A := pw wA
  set B := pw wB
  set C := pw wC
  set H := closure ({A, B, C} : Set (Equiv.Perm (Fin 315)))
  have hgens : ∀ s ∈ ({A, B, C} : Set (Equiv.Perm (Fin 315))), s ∈ j2P := by
    rintro s (rfl | rfl | rfl)
    · exact pw_mem wA
    · exact pw_mem wB
    · exact pw_mem wC
  have hHP : H ≤ j2P := (closure_le _).2 hgens
  have hcomm1 : ∀ x ∈ H, ∀ s ∈ ({A, B, C} : Set (Equiv.Perm (Fin 315))), Commute x s := by
    intro x hx
    induction hx using closure_induction with
    | mem y hy =>
      rintro s hs
      rcases hy with rfl | rfl | rfl <;> rcases hs with rfl | rfl | rfl
      · exact Commute.refl A
      · exact hAB
      · exact hAC
      · exact hAB.symm
      · exact Commute.refl B
      · exact hBC
      · exact hAC.symm
      · exact hBC.symm
      · exact Commute.refl C
    | one => exact fun s _ => Commute.one_left s
    | mul y z _ _ hy hz => exact fun s hs => (hy s hs).mul_left (hz s hs)
    | inv y _ hy => exact fun s hs => (hy s hs).inv_left
  have hcomm : ∀ x ∈ H, ∀ y ∈ H, Commute x y := by
    intro x hx y hy
    induction hy using closure_induction with
    | mem z hz => exact hcomm1 x hx z hz
    | one => exact Commute.one_right x
    | mul y z _ _ hy hz => exact hy.mul_right hz
    | inv y _ hy => exact hy.inv_right
  have hsq : ∀ x ∈ H, x * x = 1 := by
    intro x hx
    induction hx using closure_induction with
    | mem y hy =>
      rcases hy with rfl | rfl | rfl
      · exact hA2
      · exact hB2
      · exact hC2
    | one => exact mul_one 1
    | mul y z hy hz ihy ihz =>
      calc y * z * (y * z) = y * y * (z * z) := by
            rw [mul_assoc, ← mul_assoc z y z, ← (hcomm y hy z hz).eq]
            group
        _ = 1 := by rw [ihy, ihz, mul_one]
    | inv y _ hy => rw [← mul_inv_rev, hy, inv_one]
  have hH2 : IsPGroup 2 H := fun x => ⟨1, by
    apply Subtype.ext
    rw [Subgroup.coe_pow, OneMemClass.coe_one, pow_one, pow_two]
    exact hsq x x.2⟩
  have hmemA : A ∈ H := subset_closure (by simp)
  have hmemB : B ∈ H := subset_closure (by simp)
  have hmemC : C ∈ H := subset_closure (by simp)
  have hsH : ∀ a ∈ hsP, a ∈ H := by
    intro a ha
    simp only [hsP, List.mem_cons, List.not_mem_nil, or_false] at ha
    rcases ha with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact hmemA
    · exact hmemB
    · exact mul_mem hmemA hmemB
    · exact hmemC
    · exact mul_mem hmemA hmemC
    · exact mul_mem hmemB hmemC
    · exact mul_mem (mul_mem hmemA hmemB) hmemC
  have hS2 : IsPGroup 2 S := IsPGroup.of_card hcard
  have hidx : ¬ 2 ∣ S.relIndex j2P := by
    have h1 := Subgroup.relIndex_mul_card S j2P
    rw [inf_eq_left.mpr hS, card_j2P, hcard] at h1
    omega
  obtain ⟨g, hgP, hg⟩ := conj_into hS2 hS hidx hHP hH2
  set K := W.comap (MulAut.conj g⁻¹).toMonoidHom
  have memK : ∀ x, x ∈ K ↔ g⁻¹ * x * g ∈ W := fun x => by
    simp [K, MulAut.conj_apply]
  have hKP : K ≤ j2P := by
    intro x hx
    have h1 := hW ((memK x).1 hx)
    have e : x = g * (g⁻¹ * x * g) * g⁻¹ := by group
    rw [e]
    exact mul_mem (mul_mem hgP h1) (inv_mem hgP)
  have hHK : H ≤ normalizer (K : Set (Equiv.Perm (Fin 315))) := by
    intro y hy
    rw [mem_normalizer_iff]
    intro x
    have hs := hSW (hg y hy)
    rw [mem_normalizer_iff] at hs
    rw [memK, memK, hs (g⁻¹ * x * g)]
    have e : g⁻¹ * y * g * (g⁻¹ * x * g) * (g⁻¹ * y * g)⁻¹ = g⁻¹ * (y * x * y⁻¹) * g := by group
    rw [e]
  have hK3 : IsPGroup 3 K := hW3.comap_of_injective _ (MulAut.conj g⁻¹).injective
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hK3
  have hk3 : k ≤ 3 := by
    by_contra hk4
    have h1 : Nat.card K ∣ 604800 := card_j2P ▸ Subgroup.card_dvd_of_le hKP
    rw [hk] at h1
    have h2 : 3 ^ 4 ∣ 3 ^ k := pow_dvd_pow 3 (by omega)
    have := h2.trans h1
    norm_num at this
  have hexp : ∀ z ∈ K, z ^ 27 = 1 := by
    intro z hz
    have h1 : (⟨z, hz⟩ : K) ^ Nat.card K = 1 := pow_card_eq_one'
    obtain ⟨m, hm⟩ : Nat.card K ∣ 27 := by
      rw [hk]
      exact pow_dvd_pow 3 hk3
    have h2 := congrArg Subtype.val h1
    rw [Subgroup.coe_pow, OneMemClass.coe_one] at h2
    rw [hm, pow_mul, h2, one_pow]
  have hwit : ∀ x ∈ K, (∃ a ∈ hsP, (x * (a * x * a)) ^ 27 ≠ 1) ∨
      (∃ a ∈ hsP, ∃ b ∈ hsP, (x * (a * x * a) * (b * x * b)) ^ 27 ≠ 1) → False := by
    have hconj : ∀ a ∈ hsP, ∀ x ∈ K, a * x * a ∈ K := by
      intro a ha x hx
      have h1 := (mem_normalizer_iff.1 (hHK (hsH a ha)) x).1 hx
      rwa [inv_eq_of_mul_eq_one_right (hsq a (hsH a ha))] at h1
    rintro x hx (⟨a, ha, hne⟩ | ⟨a, ha, b, hb, hne⟩)
    · exact hne (hexp _ (mul_mem hx (hconj a ha x hx)))
    · exact hne (hexp _ (mul_mem (mul_mem hx (hconj a ha x hx)) (hconj b hb x hx)))
  have hE := kleinFour_pair5246 hC2 (by
      calc A * B * (A * B) = A * A * (B * B) := by rw [mul_assoc, ← mul_assoc B A B, ← hAB]; group
        _ = 1 := by rw [hA2, hB2, mul_one]) hC1 hAB1 hCAB
    (by rw [← mul_assoc, ← hAC, mul_assoc, ← hBC, ← mul_assoc])
  have hEH : closure ({C, A * B} : Set (Equiv.Perm (Fin 315))) ≤ H := by
    rw [closure_le]
    rintro s (rfl | rfl)
    · exact hmemC
    · exact mul_mem hmemA hmemB
  have hABC1 : A * B * C ≠ 1 := fun h => hCAB ((eq_inv_of_mul_eq_one_right h).trans
    (inv_eq_of_mul_eq_one_right (hsq _ (mul_mem hmemA hmemB))))
  have hT1 : C ∈ closure ({C, A * B} : Set (Equiv.Perm (Fin 315))) :=
    subset_closure (Set.mem_insert _ _)
  have hT2 : A * B ∈ closure ({C, A * B} : Set (Equiv.Perm (Fin 315))) :=
    subset_closure (Set.mem_insert_of_mem _ rfl)
  have hodd : Odd (Nat.card K) := by
    rw [hk]
    exact Odd.pow (by decide)
  have h4 := CFSG.ABGLocalTools.four_group_odd_eq_mul_centralizers (K := K) hodd
    (hEH.trans hHK) (a₁ := C) (a₂ := A * B) (a₃ := A * B * C)
    hT1 hT2 (mul_mem hT2 hT1) hC1 hAB1 hABC1 hCAB
    (fun h => hAB1 (mul_right_cancel (h.symm.trans (one_mul C).symm)))
    (fun h => hC1 (mul_left_cancel (h.symm.trans (mul_one (A * B)).symm)))
  have finish : ∀ {c ci : List Nat} {cnt : Nat} {T : Nat → Nat} {t : Table}
      {e : Equiv.Perm (Fin 315)}, chkC c ci cnt T = true → pw ci = (pw c)⁻¹ →
      pw c * tp 315 t * (pw c)⁻¹ = e →
      (∀ y ∈ j2P ⊓ centralizer ({tp 315 t} : Set (Equiv.Perm (Fin 315))), orderOf y = 3 →
        ∃ i < cnt, PR 315 9 (T i) y) →
      ∀ x ∈ K, orderOf x = 3 → x * e = e * x → False := by
    intro c ci cnt T t e hchk hci he hdom x hx hx3 hxe
    have ht : tp 315 t = (pw c)⁻¹ * e * pw c := by
      rw [← he]
      group
    have hy : (pw c)⁻¹ * x * pw c ∈ j2P ⊓ centralizer ({tp 315 t} : Set (Equiv.Perm (Fin 315))) := by
      refine mem_inf.mpr ⟨mul_mem (mul_mem (inv_mem (pw_mem c)) (hKP hx)) (pw_mem c), ?_⟩
      rw [mem_centralizer_singleton_iff, ht]
      calc (pw c)⁻¹ * x * pw c * ((pw c)⁻¹ * e * pw c) = (pw c)⁻¹ * (x * e) * pw c := by group
        _ = (pw c)⁻¹ * (e * x) * pw c := by rw [hxe]
        _ = _ := by group
    have hconj : (MulAut.conj (pw c)⁻¹) x = (pw c)⁻¹ * x * pw c := by
      simp [MulAut.conj_apply]
    have hy3 : orderOf ((pw c)⁻¹ * x * pw c) = 3 := by
      rw [← hconj, MulEquiv.orderOf_eq, hx3]
    obtain ⟨i, hi, hT⟩ := hdom _ hy hy3
    have hw := wit_of hchk hci hi hT
    have hx' : pw c * ((pw c)⁻¹ * x * pw c) * (pw c)⁻¹ = x := by group
    rw [hx'] at hw
    exact hwit x hx hw
  have h3el : ∀ e u, u ∈ K ⊓ centralizer ({e} : Set (Equiv.Perm (Fin 315))) → u ≠ 1 →
      ∃ x ∈ K, orderOf x = 3 ∧ x * e = e * x := by
    intro e u hu hu1
    set F := K ⊓ centralizer ({e} : Set (Equiv.Perm (Fin 315)))
    have hF : IsPGroup 3 F := hK3.to_le inf_le_left
    obtain ⟨m, hm⟩ := IsPGroup.iff_orderOf.mp hF ⟨u, hu⟩
    have hm0 : m ≠ 0 := by
      rintro rfl
      rw [pow_zero, orderOf_eq_one_iff] at hm
      exact hu1 (congrArg Subtype.val hm)
    have hdvd : 3 ∣ Nat.card F :=
      (dvd_pow_self 3 hm0).trans (hm ▸ orderOf_dvd_natCard _)
    obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := F) 3 hdvd
    refine ⟨x, (mem_inf.mp x.2).1, by rw [Subgroup.orderOf_coe, hx], ?_⟩
    exact mem_centralizer_singleton_iff.mp (mem_inf.mp x.2).2
  by_contra hne
  have hKne : K ≠ ⊥ := by
    intro hK
    apply hne
    rw [eq_bot_iff]
    intro w hw
    have h1 : g * w * g⁻¹ ∈ K := (memK _).2 (by
      have e : g⁻¹ * (g * w * g⁻¹) * g = w := by group
      rw [e]
      exact hw)
    rw [hK, mem_bot] at h1
    rw [mem_bot]
    calc w = g⁻¹ * (g * w * g⁻¹) * g := by group
      _ = 1 := by rw [h1]; group
  obtain ⟨⟨x0, hx0⟩, hx01⟩ := (Subgroup.ne_bot_iff_exists_ne_one).mp hKne
  have hx0' : x0 ≠ 1 := fun h => hx01 (Subtype.ext h)
  have hx0s : x0 ∈ (K : Set (Equiv.Perm (Fin 315))) := hx0
  rw [h4] at hx0s
  obtain ⟨uv, ⟨u, hu, v, hv, rfl⟩, w, hw, hx0e⟩ := hx0s
  by_cases hu1 : u = 1
  · by_cases hv1 : v = 1
    · have hw1 : w ≠ 1 := by
        rintro rfl
        apply hx0'
        rw [← hx0e, hu1, hv1]
        group
      obtain ⟨x, hx, hx3, hxe⟩ := h3el _ w hw hw1
      exact finish ch5246_t2c3 e3i e3 (fun _ hy h3 => dom17 hy h3) x hx hx3 hxe
    · obtain ⟨x, hx, hx3, hxe⟩ := h3el _ v hv hv1
      exact finish ch5246_t3a e2i e2 (fun _ hy h3 => dom31 hy h3) x hx hx3 hxe
  · obtain ⟨x, hx, hx3, hxe⟩ := h3el _ u hu hu1
    exact finish ch5246_t2c1 e1i e1 (fun _ hy h3 => dom17 hy h3) x hx hx3 hxe

end CertificateChecks.KernelIvk8J2

end
