module

public import Certificates.Kernel.HN1408.AKChk
public import Certificates.Kernel.HN1408.SylTFacts

public section

set_option maxRecDepth 400000

namespace CFSG.KD.HN1408.AK

open Subgroup CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KS.MulH CFSG.KC.BfsPin
open CFSG.EvenSporadicStandard.HNRecog CFSG.EvenSporadicStandard.HNRecog.HaradaModel
open CFSG.Sporadic.Th CFSG.Sporadic.Th.Native CFSG.Sporadic.SmallOddCore
open CFSG.Sporadic.Schreier.Native CFSG.Sporadic.SmallOddCore.Native CFSG.KD.HN1408

@[expose] noncomputable def uE (i : Nat) : Equiv.Perm (Fin 1408) := elemW (uWords.getD i [])

@[expose] noncomputable def sel (c : Bool) (g : Equiv.Perm (Fin 1408)) : Equiv.Perm (Fin 1408) :=
  cond c g 1

@[expose] noncomputable def bs (k i : Nat) : Bool := Nat.beq (bt k i) 1

@[expose] noncomputable def itE (k : Nat) : Equiv.Perm (Fin 1408) :=
  sel (bs k 0) (uE 0) * (sel (bs k 1) (uE 1) * (sel (bs k 2) (uE 2) * (sel (bs k 3) (uE 3) *
    (sel (bs k 4) (uE 4) * sel (bs k 5) (uE 5)))))

theorem u_letters {i : Nat} (hi : i < 6) : lettersOK (uWords.getD i []) = true := by
  interval_cases i <;> decide

theorem repU {i : Nat} (hi : i < 6) : RepC (U i) (uE i) := repC_word (u_letters hi)

theorem strictN_app' (y : Nat) (k : Nat → Nat) : strictN y k = k y := by cases y <;> rfl

theorem rep_step {c : Bool} {X Y : Nat} {g h : Equiv.Perm (Fin 1408)} (hX : RepC X g)
    (hY : RepC Y h) : RepC (nIf(c, pc X Y, Y)) (sel c g * h) := by
  cases c
  · change RepC Y (1 * h)
    rw [one_mul]
    exact hY
  · exact repC_pc hX hY

theorem rep_first {c : Bool} {X : Nat} {g : Equiv.Perm (Fin 1408)} (hX : RepC X g) :
    RepC (nIf(c, X, idK)) (sel c g) := by
  cases c
  · exact CzT.repC_idK
  · exact hX

theorem pt_step {c : Bool} {X y x : Nat} {g h : Equiv.Perm (Fin 1408)} (hX : RepC X g)
    (hx : x < 1408) (hy : y = (h ⟨x, hx⟩).val) :
    nIf(c, pt X y, y) = ((sel c g * h) ⟨x, hx⟩).val := by
  cases c
  · change y = ((1 * h) ⟨x, hx⟩).val
    rw [one_mul]
    exact hy
  · change pt X y = ((g * h) ⟨x, hx⟩).val
    rw [Equiv.Perm.mul_apply, hy, repC_pt hX (Fin.isLt _)]

theorem pt_first {c : Bool} {X x : Nat} {g : Equiv.Perm (Fin 1408)} (hX : RepC X g)
    (hx : x < 1408) : nIf(c, pt X x, x) = (sel c g ⟨x, hx⟩).val := by
  cases c
  · rfl
  · exact repC_pt hX hx

theorem rep_itK {X0 X1 X2 X3 X4 X5 : Nat} (h0 : RepC X0 (uE 0)) (h1 : RepC X1 (uE 1))
    (h2 : RepC X2 (uE 2)) (h3 : RepC X3 (uE 3)) (h4 : RepC X4 (uE 4)) (h5 : RepC X5 (uE 5))
    (k : Nat) : RepC (itK X0 X1 X2 X3 X4 X5 k) (itE k) := by
  unfold itK
  simp only [strictN_app']
  exact rep_step h0 (rep_step h1 (rep_step h2 (rep_step h3 (rep_step h4 (rep_first h5)))))

theorem itP_eq {X0 X1 X2 X3 X4 X5 : Nat} (h0 : RepC X0 (uE 0)) (h1 : RepC X1 (uE 1))
    (h2 : RepC X2 (uE 2)) (h3 : RepC X3 (uE 3)) (h4 : RepC X4 (uE 4)) (h5 : RepC X5 (uE 5))
    (k x : Nat) (hx : x < 1408) : itP X0 X1 X2 X3 X4 X5 k x = (itE k ⟨x, hx⟩).val := by
  unfold itP
  simp only [strictN_app']
  exact pt_step h0 hx (pt_step h1 hx (pt_step h2 hx (pt_step h3 hx (pt_step h4 hx
    (pt_first h5 hx)))))

theorem basicB_parts {X0 X1 X2 X3 X4 X5 Z1 : Nat} (h : basicB X0 X1 X2 X3 X4 X5 Z1 = true) :
    involK X0 = true ∧ involK X1 = true ∧ involK X2 = true ∧ involK X3 = true ∧
      involK X4 = true ∧ involK X5 = true ∧
      commP X0 X1 = true ∧ commP X0 X2 = true ∧ commP X0 X3 = true ∧ commP X0 X4 = true ∧
      commP X0 X5 = true ∧ commP X1 X2 = true ∧ commP X1 X3 = true ∧ commP X1 X4 = true ∧
      commP X1 X5 = true ∧ commP X2 X3 = true ∧ commP X2 X4 = true ∧ commP X2 X5 = true ∧
      commP X3 X4 = true ∧ commP X3 X5 = true ∧ commP X4 X5 = true ∧
      pc X0 (pc X2 (pc X3 X5)) = Z1 ∧
      (∀ k < 63, bIf(Nat.beq (itP X0 X1 X2 X3 X4 X5 (Nat.succ k) 0) 0,
        bIf(Nat.beq (itP X0 X1 X2 X3 X4 X5 (Nat.succ k) 1) 1, false, true), true) = true) := by
  unfold basicB at h
  obtain ⟨a0, h⟩ := CFSG.KD.HN1408.mkA h
  obtain ⟨a1, h⟩ := CFSG.KD.HN1408.mkA h
  obtain ⟨a2, h⟩ := CFSG.KD.HN1408.mkA h
  obtain ⟨a3, h⟩ := CFSG.KD.HN1408.mkA h
  obtain ⟨a4, h⟩ := CFSG.KD.HN1408.mkA h
  obtain ⟨a5, h⟩ := CFSG.KD.HN1408.mkA h
  obtain ⟨c01, h⟩ := CFSG.KD.HN1408.mkA h
  obtain ⟨c02, h⟩ := CFSG.KD.HN1408.mkA h
  obtain ⟨c03, h⟩ := CFSG.KD.HN1408.mkA h
  obtain ⟨c04, h⟩ := CFSG.KD.HN1408.mkA h
  obtain ⟨c05, h⟩ := CFSG.KD.HN1408.mkA h
  obtain ⟨c12, h⟩ := CFSG.KD.HN1408.mkA h
  obtain ⟨c13, h⟩ := CFSG.KD.HN1408.mkA h
  obtain ⟨c14, h⟩ := CFSG.KD.HN1408.mkA h
  obtain ⟨c15, h⟩ := CFSG.KD.HN1408.mkA h
  obtain ⟨c23, h⟩ := CFSG.KD.HN1408.mkA h
  obtain ⟨c24, h⟩ := CFSG.KD.HN1408.mkA h
  obtain ⟨c25, h⟩ := CFSG.KD.HN1408.mkA h
  obtain ⟨c34, h⟩ := CFSG.KD.HN1408.mkA h
  obtain ⟨c35, h⟩ := CFSG.KD.HN1408.mkA h
  obtain ⟨c45, h⟩ := CFSG.KD.HN1408.mkA h
  obtain ⟨ez, h⟩ := CFSG.KD.HN1408.mkA h
  exact ⟨a0, a1, a2, a3, a4, a5, c01, c02, c03, c04, c05, c12, c13, c14, c15, c23, c24, c25, c34,
    c35, c45, Nat.eq_of_beq_eq_true ez, fun k hk => allN_spec h k hk⟩

theorem basic_parts : basicB (U 0) (U 1) (U 2) (U 3) (U 4) (U 5) (WK wordZ₁) = true := by
  have h := basic_ok
  unfold basicK at h
  simp only [strictB_app] at h
  exact h

theorem sq_of_involK {X : Nat} {g : Equiv.Perm (Fin 1408)} (hX : RepC X g) (h : involK X = true) :
    g * g = 1 := by
  unfold involK at h
  obtain ⟨e, -⟩ := CFSG.KD.HN1408.mkA h
  have h1 := repC_pc hX hX
  rw [Nat.eq_of_beq_eq_true e] at h1
  exact eq_of_repC h1 CzT.repC_idK

theorem comm_of_commP {X Y : Nat} {g h : Equiv.Perm (Fin 1408)} (hX : RepC X g) (hY : RepC Y h)
    (hc : commP X Y = true) : g * h = h * g := by
  have h1 := repC_pc hX hY
  rw [Nat.eq_of_beq_eq_true hc] at h1
  exact eq_of_repC h1 (repC_pc hY hX)

theorem u_sq {i : Nat} (hi : i < 6) : uE i * uE i = 1 := by
  obtain ⟨a0, a1, a2, a3, a4, a5, -⟩ := basicB_parts basic_parts
  interval_cases i
  · exact sq_of_involK (repU (by norm_num)) a0
  · exact sq_of_involK (repU (by norm_num)) a1
  · exact sq_of_involK (repU (by norm_num)) a2
  · exact sq_of_involK (repU (by norm_num)) a3
  · exact sq_of_involK (repU (by norm_num)) a4
  · exact sq_of_involK (repU (by norm_num)) a5

theorem u_comm_lt {i j : Nat} (hij : i < j) (hj : j < 6) : uE i * uE j = uE j * uE i := by
  obtain ⟨-, -, -, -, -, -, c01, c02, c03, c04, c05, c12, c13, c14, c15, c23, c24, c25, c34, c35,
    c45, -⟩ := basicB_parts basic_parts
  have r : ∀ l, l < 6 → RepC (U l) (uE l) := fun l hl => repU hl
  interval_cases j <;> interval_cases i
  · exact comm_of_commP (r 0 (by norm_num)) (r 1 (by norm_num)) c01
  · exact comm_of_commP (r 0 (by norm_num)) (r 2 (by norm_num)) c02
  · exact comm_of_commP (r 1 (by norm_num)) (r 2 (by norm_num)) c12
  · exact comm_of_commP (r 0 (by norm_num)) (r 3 (by norm_num)) c03
  · exact comm_of_commP (r 1 (by norm_num)) (r 3 (by norm_num)) c13
  · exact comm_of_commP (r 2 (by norm_num)) (r 3 (by norm_num)) c23
  · exact comm_of_commP (r 0 (by norm_num)) (r 4 (by norm_num)) c04
  · exact comm_of_commP (r 1 (by norm_num)) (r 4 (by norm_num)) c14
  · exact comm_of_commP (r 2 (by norm_num)) (r 4 (by norm_num)) c24
  · exact comm_of_commP (r 3 (by norm_num)) (r 4 (by norm_num)) c34
  · exact comm_of_commP (r 0 (by norm_num)) (r 5 (by norm_num)) c05
  · exact comm_of_commP (r 1 (by norm_num)) (r 5 (by norm_num)) c15
  · exact comm_of_commP (r 2 (by norm_num)) (r 5 (by norm_num)) c25
  · exact comm_of_commP (r 3 (by norm_num)) (r 5 (by norm_num)) c35
  · exact comm_of_commP (r 4 (by norm_num)) (r 5 (by norm_num)) c45

theorem u_comm {i j : Nat} (hi : i < 6) (hj : j < 6) : uE i * uE j = uE j * uE i := by
  rcases lt_trichotomy i j with h | rfl | h
  · exact u_comm_lt h hj
  · rfl
  · exact (u_comm_lt h hi).symm

theorem z1_eq : uE 0 * (uE 2 * (uE 3 * uE 5)) = elemZ₁ := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, ez, -⟩ :=
    basicB_parts basic_parts
  have h := repC_pc (repU (i := 0) (by norm_num)) (repC_pc (repU (i := 2) (by norm_num))
    (repC_pc (repU (i := 3) (by norm_num)) (repU (i := 5) (by norm_num))))
  rw [ez] at h
  exact eq_of_repC h (repC_word (by decide))

theorem bIf_ne {a b : Bool} (h : bIf(a, bIf(b, false, true), true) = true) :
    a = false ∨ b = false := by
  cases a <;> cases b <;> simp_all

theorem itE_ne_one {k : Nat} (hk0 : 0 < k) (hk : k < 64) : itE k ≠ 1 := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hm⟩ :=
    basicB_parts basic_parts
  obtain ⟨k', rfl⟩ : ∃ k', k = Nat.succ k' := ⟨k - 1, by omega⟩
  have h := hm k' (by omega)
  have r : ∀ l, l < 6 → RepC (U l) (uE l) := fun l hl => repU hl
  have e := itP_eq (r 0 (by norm_num)) (r 1 (by norm_num)) (r 2 (by norm_num)) (r 3 (by norm_num))
    (r 4 (by norm_num)) (r 5 (by norm_num)) (Nat.succ k')
  intro h1
  rcases bIf_ne h with h' | h'
  · rw [e 0 (by norm_num), h1] at h'
    simp at h'
  · rw [e 1 (by norm_num), h1] at h'
    simp at h'

theorem half_parts : allN 5 (fun i => halvesK (U i)) = true ∧ Nat.ble 704 (pt (U 5) 0) = true :=
  (bAnd_iff _ _).1 half_ok

theorem u_blocks {i : Nat} (hi : i < 5) : uE i ∈ blocks1408 := by
  obtain ⟨h1, -⟩ := half_parts
  have hr := repU (i := i) (by omega)
  exact mem_blocks1408_of_preservesHalves hr.2 (halves_eq hr.1 (allN_spec h1 i hi))

theorem u5_not_blocks : uE 5 ∉ blocks1408 := by
  obtain ⟨-, h2⟩ := half_parts
  have hr := repU (i := 5) (by norm_num)
  refine not_mem_blocks1408_of_swapsZero hr.2 ?_
  rw [swapsZero_eq hr.1]
  exact decide_eq_true (Nat.ble_eq.mp h2)

theorem gen_eq (j : Fin 7) : elemW [j.val + 1] = h1408GenPerm j := by
  simp [elemW, CFSG.EvenSporadicStandard.TwoHS.wordVal, h1408Perms]

theorem blk_or_swap_P : ∀ g ∈ P1408, g ∈ blocks1408 ∨ SylTF.Swap g := by
  refine SylTF.blk_or_swap_closure ?_
  rintro _ ⟨j, rfl⟩
  have hr := repC_word (lettersOK_gen j.isLt)
  rw [← gen_eq j]
  exact SylTF.blkGenK_spec (fun p hp => repC_pt hr hp) (allN_spec genBlkP_ok j.val j.isLt)

theorem normGens_letters {l : Nat} (hl : l < 3) : lettersOK (normGens.getD l []) = true := by
  interval_cases l <;> decide

theorem normB_parts {X0 X1 X2 X3 X4 X5 G l : Nat} (h : normB X0 X1 X2 X3 X4 X5 G l = true)
    {i : Nat} (hi : i < 6) :
    pc G (cond (Nat.beq i 0) X0 (cond (Nat.beq i 1) X1 (cond (Nat.beq i 2) X2
      (cond (Nat.beq i 3) X3 (cond (Nat.beq i 4) X4 X5))))) =
      pc (itK X0 X1 X2 X3 X4 X5 (aCode.getD (6 * l + i) 0)) G := by
  unfold normB at h
  obtain ⟨e0, h⟩ := CFSG.KD.HN1408.mkA h
  obtain ⟨e1, h⟩ := CFSG.KD.HN1408.mkA h
  obtain ⟨e2, h⟩ := CFSG.KD.HN1408.mkA h
  obtain ⟨e3, h⟩ := CFSG.KD.HN1408.mkA h
  obtain ⟨e4, e5⟩ := CFSG.KD.HN1408.mkA h
  interval_cases i
  · exact Nat.eq_of_beq_eq_true e0
  · exact Nat.eq_of_beq_eq_true e1
  · exact Nat.eq_of_beq_eq_true e2
  · exact Nat.eq_of_beq_eq_true e3
  · exact Nat.eq_of_beq_eq_true e4
  · exact Nat.eq_of_beq_eq_true e5

theorem pick_rep {X0 X1 X2 X3 X4 X5 : Nat} (h0 : RepC X0 (uE 0)) (h1 : RepC X1 (uE 1))
    (h2 : RepC X2 (uE 2)) (h3 : RepC X3 (uE 3)) (h4 : RepC X4 (uE 4)) (h5 : RepC X5 (uE 5))
    {i : Nat} (hi : i < 6) :
    RepC (cond (Nat.beq i 0) X0 (cond (Nat.beq i 1) X1 (cond (Nat.beq i 2) X2
      (cond (Nat.beq i 3) X3 (cond (Nat.beq i 4) X4 X5))))) (uE i) := by
  interval_cases i <;> assumption

theorem norm_rel {l i : Nat} (hl : l < 3) (hi : i < 6) :
    elemW (normGens.getD l []) * uE i = itE (aCode.getD (6 * l + i) 0) * elemW (normGens.getD l []) := by
  have h := norm_ok
  unfold normK at h
  simp only [strictB_app] at h
  have hl' := allN_spec h l hl
  have e := normB_parts hl' hi
  have r : ∀ l, l < 6 → RepC (U l) (uE l) := fun l hl => repU hl
  have hG := repC_word (normGens_letters hl)
  have h1 := repC_pc hG (pick_rep (r 0 (by norm_num)) (r 1 (by norm_num)) (r 2 (by norm_num))
    (r 3 (by norm_num)) (r 4 (by norm_num)) (r 5 (by norm_num)) hi)
  rw [e] at h1
  exact eq_of_repC h1 (repC_pc (rep_itK (r 0 (by norm_num)) (r 1 (by norm_num))
    (r 2 (by norm_num)) (r 3 (by norm_num)) (r 4 (by norm_num)) (r 5 (by norm_num)) _) hG)

theorem anyK_spec : ∀ {n : Nat} {f : Nat → Bool}, anyK n f = true → ∃ k < n, f k = true
  | 0, _, h => absurd h Bool.false_ne_true
  | n + 1, f, h => by
    change bIf(f n, true, anyK n f) = true at h
    cases hfn : f n
    · have h' : anyK n f = true := by
        rw [hfn] at h
        exact h
      obtain ⟨k, hk, e⟩ := anyK_spec h'
      exact ⟨k, by omega, e⟩
    · exact ⟨n, by omega, hfn⟩

theorem u0_eq : uE 0 = elemZ := by
  have e : uWords.getD 0 [] = wordZ := by decide
  rw [uE, e]
  rfl

theorem uE_cent {i : Nat} (hi : i < 6) :
    uE i ∈ P1408 ⊓ centralizer ({elemZ} : Set (Equiv.Perm (Fin 1408))) := by
  refine mem_inf.2 ⟨elemW_mem _, Subgroup.mem_centralizer_iff.2 ?_⟩
  rintro _ rfl
  rw [← u0_eq]
  exact u_comm (by norm_num) hi

theorem sel_cent (c : Bool) {i : Nat} (hi : i < 6) :
    sel c (uE i) ∈ P1408 ⊓ centralizer ({elemZ} : Set (Equiv.Perm (Fin 1408))) := by
  cases c
  · exact one_mem _
  · exact uE_cent hi

theorem itE_cent (k : Nat) :
    itE k ∈ P1408 ⊓ centralizer ({elemZ} : Set (Equiv.Perm (Fin 1408))) :=
  mul_mem (sel_cent _ (by norm_num)) (mul_mem (sel_cent _ (by norm_num)) (mul_mem
    (sel_cent _ (by norm_num)) (mul_mem (sel_cent _ (by norm_num)) (mul_mem
    (sel_cent _ (by norm_num)) (sel_cent _ (by norm_num))))))

theorem cent_parts : CzT.czScan CzT.T0 CzT.T1 (centRow (U 0) (U 1) (U 2) (U 3) (U 4) (U 5)) = true := by
  have h := cent_ok
  unfold centK at h
  simp only [strictB_app] at h
  exact h

theorem cent_le (hP : Nat.card ↥P1408 = 177408000) {x : Equiv.Perm (Fin 1408)} (hx : x ∈ P1408)
    (hc : ∀ i < 6, x * uE i = uE i * x) : ∃ k < 64, x = itE k := by
  have r : ∀ l, l < 6 → RepC (U l) (uE l) := fun l hl => repU hl
  have hxC : x ∈ P1408 ⊓ centralizer ({elemZ} : Set (Equiv.Perm (Fin 1408))) := by
    refine mem_inf.2 ⟨hx, Subgroup.mem_centralizer_iff.2 ?_⟩
    rintro _ rfl
    rw [← u0_eq]
    exact (hc 0 (by norm_num)).symm
  obtain ⟨i, hi, j, hj, rfl⟩ := (CzT.mem_iff hP).1 hxC
  have hev : ∀ y (hy : y < 1408), pt (CzT.T0 i) (pt (CzT.T1 j) y) =
      ((CzT.t0P i * CzT.t1P j) ⟨y, hy⟩).val := fun y hy => CzT.ev_eq hi hj hy
  have hrow := CzT.czScan_spec cent_parts i hi j hj
  unfold centRow at hrow
  simp only [strictB_app] at hrow
  rcases CFSG.KD.HN1408.mkIf hrow with ⟨-, hany⟩ | ⟨hf, -⟩
  · obtain ⟨k, hk, hb⟩ := anyK_spec hany
    have e := itP_eq (r 0 (by norm_num)) (r 1 (by norm_num)) (r 2 (by norm_num))
      (r 3 (by norm_num)) (r 4 (by norm_num)) (r 5 (by norm_num)) k
    exact ⟨k, hk, CzT.base_eq hP hxC (itE_cent k) hev (e 0 (by norm_num)).symm
      (e 1 (by norm_num)).symm hb⟩
  · rw [CzT.commB_of hev (r 1 (by norm_num)) (hc 1 (by norm_num)),
      CzT.commB_of hev (r 2 (by norm_num)) (hc 2 (by norm_num)),
      CzT.commB_of hev (r 3 (by norm_num)) (hc 3 (by norm_num)),
      CzT.commB_of hev (r 5 (by norm_num)) (hc 5 (by norm_num))] at hf
    exact absurd hf (by decide)

abbrev nG : Subgroup (Equiv.Perm (Fin 1408)) := closure (elemW '' {w | w ∈ normGens})

theorem fuseRow_spec {T : List (Nat × Nat × Nat)} {k : Nat} (h : fuseRow T k = true) :
    ((T.getD k (0, 0, 0)).2.2 = 0 ∧ typeBase.getD (typeIdx k) 0 = k) ∨
      ((T.getD k (0, 0, 0)).2.2 ≠ 0 ∧ (T.getD k (0, 0, 0)).1 < 64 ∧ (T.getD k (0, 0, 0)).1 ≠ 0 ∧
        (T.getD k (0, 0, 0)).1 ≠ 16 ∧ (T.getD k (0, 0, 0)).2.1 < 3 ∧
        (T.getD (T.getD k (0, 0, 0)).1 (0, 0, 0)).2.2 + 1 = (T.getD k (0, 0, 0)).2.2 ∧
        typeIdx (T.getD k (0, 0, 0)).1 = typeIdx k) := by
  simp only [fuseRow] at h
  generalize T.getD k (0, 0, 0) = r at h ⊢
  obtain ⟨p, l, d⟩ := r
  dsimp only at h ⊢
  by_cases hd : d = 0
  · rw [if_pos hd] at h
    exact Or.inl ⟨hd, of_decide_eq_true h⟩
  · rw [if_neg hd] at h
    simp only [Bool.and_eq_true, decide_eq_true_eq, bne_iff_ne, ne_eq, beq_iff_eq] at h
    right
    refine ⟨hd, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> tauto

theorem fuse_row {k : Nat} (hk : k < 64) (h0 : k ≠ 0) (h16 : k ≠ 16) : fuseRow aTree k = true := by
  have h := fuse_ok
  simp only [fuseK, fuseKT, List.all_eq_true, List.mem_range] at h
  have hk' := h k hk
  simp only [Bool.or_eq_true, beq_iff_eq, h0, h16, false_or] at hk'
  exact hk'

theorem pick3 {G0 G1 G2 : Nat} {g0 g1 g2 : Equiv.Perm (Fin 1408)} (h0 : RepC G0 g0)
    (h1 : RepC G1 g1) (h2 : RepC G2 g2) {l : Nat} (hl : l < 3) :
    RepC (nIf(Nat.beq l 0, G0, nIf(Nat.beq l 1, G1, G2)))
      (if l = 0 then g0 else if l = 1 then g1 else g2) := by
  interval_cases l
  · exact h0
  · exact h1
  · exact h2

theorem ng_eq {l : Nat} (hl : l < 3) :
    (if l = 0 then elemW (normGens.getD 0 []) else if l = 1 then elemW (normGens.getD 1 [])
      else elemW (normGens.getD 2 [])) = elemW (normGens.getD l []) := by
  interval_cases l <;> rfl

theorem ng_mem {l : Nat} (hl : l < 3) : elemW (normGens.getD l []) ∈ nG := by
  refine subset_closure ⟨_, ?_, rfl⟩
  interval_cases l <;> decide

theorem fuseRel_parts : ∀ k < 64,
    fuseRelB (U 0) (U 1) (U 2) (U 3) (U 4) (U 5) (WK (normGens.getD 0 []))
      (WK (normGens.getD 1 [])) (WK (normGens.getD 2 [])) k = true := by
  have h := fuseRel_ok
  unfold fuseRelK at h
  simp only [strictB_app] at h
  exact fun k hk => allN_spec h k hk

theorem fuse_rel {k : Nat} (hk : k < 64) (hd : (aTree.getD k (0, 0, 0)).2.2 ≠ 0)
    (hl : (aTree.getD k (0, 0, 0)).2.1 < 3) :
    elemW (normGens.getD (aTree.getD k (0, 0, 0)).2.1 []) * itE (aTree.getD k (0, 0, 0)).1 =
      itE k * elemW (normGens.getD (aTree.getD k (0, 0, 0)).2.1 []) := by
  have h := fuseRel_parts k hk
  unfold fuseRelB at h
  have e0 : Nat.beq (aTree.getD k (0, 0, 0)).2.2 0 = false :=
    Bool.eq_false_iff.2 fun h' => hd (Nat.eq_of_beq_eq_true h')
  rw [e0] at h
  change strictB _ _ = true at h
  simp only [strictB_app] at h
  have r : ∀ l, l < 6 → RepC (U l) (uE l) := fun l hl => repU hl
  have hG := pick3 (repC_word (normGens_letters (l := 0) (by norm_num)))
    (repC_word (normGens_letters (l := 1) (by norm_num)))
    (repC_word (normGens_letters (l := 2) (by norm_num))) hl
  rw [ng_eq hl] at hG
  have hI := fun m => rep_itK (r 0 (by norm_num)) (r 1 (by norm_num)) (r 2 (by norm_num))
    (r 3 (by norm_num)) (r 4 (by norm_num)) (r 5 (by norm_num)) m
  have h1 := repC_pc hG (hI (aTree.getD k (0, 0, 0)).1)
  rw [Nat.eq_of_beq_eq_true h] at h1
  exact eq_of_repC h1 (repC_pc (hI k) hG)

theorem fuse_conj : ∀ d k, (aTree.getD k (0, 0, 0)).2.2 = d → k < 64 → k ≠ 0 → k ≠ 16 →
    ∃ n ∈ nG, n * itE (typeBase.getD (typeIdx k) 0) * n⁻¹ = itE k := by
  intro d
  induction d with
  | zero =>
    intro k hd hk h0 h16
    rcases fuseRow_spec (fuse_row hk h0 h16) with ⟨-, hb⟩ | ⟨hd', -⟩
    · refine ⟨1, one_mem _, ?_⟩
      rw [hb]
      group
    · exact absurd hd hd'
  | succ d ih =>
    intro k hd hk h0 h16
    rcases fuseRow_spec (fuse_row hk h0 h16) with ⟨hd', -⟩ | ⟨hd0, hp, hp0, hp16, hl, hdp, ht⟩
    · rw [hd'] at hd
      exact absurd hd (Nat.succ_ne_zero d).symm
    · obtain ⟨n, hn, e⟩ := ih (aTree.getD k (0, 0, 0)).1 (by omega) hp hp0 hp16
      rw [ht] at e
      have hrel := fuse_rel hk hd0 hl
      refine ⟨elemW (normGens.getD (aTree.getD k (0, 0, 0)).2.1 []) * n,
        mul_mem (ng_mem hl) hn, ?_⟩
      rw [eq_mul_inv_of_mul_eq hrel.symm, ← e]
      group

end CFSG.KD.HN1408.AK

end
