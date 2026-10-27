module

public import Certificates.Kernel.OmegaEight.E4O8CentGlue
public import Certificates.Kernel.OmegaEight.E4O8SgK
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelO8.E4C

open CFSG.KC.Enum CFSG.KC.O8 CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.EvenSmallLie.OmegaEight
  CFSG.KC.PCent CFSG.KC.Misc.ArrEnum CertificateChecks.KernelO8 CFSG.Monster.B.Co2
  CFSG.Monster.B.Co2.Native CFSG.ClassicalInvolution.Q3.TL4.E4O8

@[expose] noncomputable def sgT (i : Nat) : Subgroup (Equiv.Perm (Fin 360)) :=
  Subgroup.closure {toPerm 360 9 (sgUK i), toPerm 360 9 (sgVK i)}

theorem sg_mem_iff {L : List Nat} {x : Nat} : e4Mem L x = true ↔ x ∈ L := by
  unfold e4Mem
  rw [List.any_eq_true]
  constructor
  · rintro ⟨y, hy, e⟩
    rw [Nat.eq_of_beq_eq_true e]
    exact hy
  · intro hx
    exact ⟨x, hx, Nat.beq_refl x⟩

theorem sg_not_of {b : Bool} (h : bIf(b, false, true) = true) : b = false := by
  cases b <;> revert h <;> decide

theorem sg_of_not {b : Bool} (h : bIf(b, false, true) = false) : b = true := by
  cases b <;> revert h <;> decide

theorem sg_and {a b : Bool} (h : bAnd(a, b) = true) : a = true ∧ b = true := by
  cases a <;> cases b <;> revert h <;> decide

theorem sg_or {c d : Bool} (h : bIf(c, true, d) = true) (hd : d = false) : c = true := by
  subst hd
  cases c <;> revert h <;> decide

theorem sg_or4 {b0 b1 b2 b3 : Bool} (h : bIf(b0, true, bIf(b1, true, bIf(b2, true, b3))) = true) :
    b0 = true ∨ b1 = true ∨ b2 = true ∨ b3 = true := by
  cases b0 <;> cases b1 <;> cases b2 <;> cases b3 <;> revert h <;> decide

theorem sg_at6 {f1 f2 f3 a1 a2 a3 : Bool} (h : bIf(f1, true, bIf(f2, true, bIf(f3, true,
    bIf(a1, false, bIf(a2, false, bIf(a3, false, true)))))) = true) :
    (f1 = true ∨ f2 = true ∨ f3 = true) ∨ (a1 = false ∧ a2 = false ∧ a3 = false) := by
  cases f1 <;> cases f2 <;> cases f3 <;> cases a1 <;> cases a2 <;> cases a3 <;> revert h <;> decide

theorem sg_one3 {c d e : Bool} (h : bIf(c, bIf(d, false, true), e) = true) :
    (c = true ∧ d = false) ∨ (c = false ∧ e = true) := by
  cases c <;> cases d <;> cases e <;> revert h <;> decide

theorem sg_conj_closure (g a b : Equiv.Perm (Fin 360)) :
    (Subgroup.closure {a, b}).map (MulAut.conj g).toMonoidHom =
      Subgroup.closure {g * a * g⁻¹, g * b * g⁻¹} := by
  rw [MonoidHom.map_closure, Set.image_pair]
  rfl

theorem sg_card_conj (g : Equiv.Perm (Fin 360)) (H : Subgroup (Equiv.Perm (Fin 360))) :
    Nat.card (H.map (MulAut.conj g).toMonoidHom) = Nat.card H :=
  Subgroup.card_map_of_injective (MulAut.conj g).injective

theorem sg_pm : CFSG.KC.BfsPin.PP 360 9 (AP.S 8) ∧ CFSG.KC.BfsPin.PP 360 9 (AP.S 9) ∧
    (∀ i < 4, CFSG.KC.BfsPin.PP 360 9 (sgUK i)) ∧ ∀ i < 4, CFSG.KC.BfsPin.PP 360 9 (sgVK i) := by
  have h := ch55118pm
  simp only [bAnd_iff] at h
  obtain ⟨h8, h9, hu, hv⟩ := h
  exact ⟨e4c_pp h8, e4c_pp h9, fun i hi => e4c_pp (allN_spec hu i hi),
    fun i hi => e4c_pp (allN_spec hv i hi)⟩

theorem sg_T0 : sgT 0 = Subgroup.closure {toPerm 360 9 e4U, toPerm 360 9 om0V} := by
  have h := ch55118t
  simp only [bAnd_iff] at h
  obtain ⟨-, -, -, hu, hv, -⟩ := h
  rw [sgT, Nat.eq_of_beq_eq_true hu, Nat.eq_of_beq_eq_true hv]

theorem sg_T_conj {i : Nat} (hi : i < 3) : CFSG.KC.BfsPin.PP 360 9 (sgQK i) ∧
    toPerm 360 9 (sgQK i) ∈ e4H0 ∧
    sgT (i + 1) = (sgT 0).map (MulAut.conj (toPerm 360 9 (sgQK i))).toMonoidHom ∧
    sgUK (i + 1) ∉ sgE.getD 0 [] := by
  obtain ⟨hp0, -, -, -, -, -, hpu, hpv⟩ := e4c_pm
  obtain ⟨-, -, hpU, hpV⟩ := sg_pm
  have h := ch55118t
  simp only [bAnd_iff] at h
  obtain ⟨-, -, hlet, -, -, hw⟩ := h
  have e := allN_spec hw i hi
  simp only [bAnd_iff] at e
  obtain ⟨eQ, eu, ev, en⟩ := e
  have hq := wordK_sound ch550106sz hp0 _ (e4c_lets hlet i)
  rw [← Nat.eq_of_beq_eq_true eQ] at hq
  refine ⟨hq.1, hq.2, ?_, fun hm => ?_⟩
  · have hu' := e4c_mul (hpU (i + 1) (by omega)) hq.1
    have hu'' := e4c_mul hq.1 hpu
    rw [Nat.eq_of_beq_eq_true eu, hu''] at hu'
    have hv' := e4c_mul (hpV (i + 1) (by omega)) hq.1
    have hv'' := e4c_mul hq.1 hpv
    rw [Nat.eq_of_beq_eq_true ev, hv''] at hv'
    rw [sg_T0, sg_conj_closure, sgT, eq_mul_inv_of_mul_eq hu'.symm,
      eq_mul_inv_of_mul_eq hv'.symm]
  · have en' := sg_not_of en
    rw [sg_mem_iff.2 hm] at en'
    exact Bool.noConfusion en'

theorem sg_E_eq {i : Nat} (hi : i < 4) :
    sgE.getD i [] = e4Q (pc (sgUK i) (sgUK i)) (sgUK i) (sgVK i) := by
  have h := allN_spec ch55118e i hi
  simp only [bAnd_iff] at h
  exact beq_iff_eq.mp h.1

theorem sg_E_sub {i : Nat} (hi : i < 4) : ∀ x ∈ sgE.getD i [],
    CFSG.KC.BfsPin.PP 360 9 x ∧ toPerm 360 9 x ∈ sgT i := by
  obtain ⟨-, -, hpU, hpV⟩ := sg_pm
  have hu := hpU i hi
  have hv := hpV i hi
  have hU : toPerm 360 9 (sgUK i) ∈ sgT i := Subgroup.subset_closure (Set.mem_insert _ _)
  have hV : toPerm 360 9 (sgVK i) ∈ sgT i :=
    Subgroup.subset_closure (Set.mem_insert_of_mem _ rfl)
  have hm : ∀ {a b : Nat}, CFSG.KC.BfsPin.PP 360 9 a → CFSG.KC.BfsPin.PP 360 9 b →
      toPerm 360 9 a ∈ sgT i → toPerm 360 9 b ∈ sgT i →
      CFSG.KC.BfsPin.PP 360 9 (pc a b) ∧ toPerm 360 9 (pc a b) ∈ sgT i :=
    fun ha hb ha' hb' => ⟨ha.mul hb, by rw [e4c_mul ha hb]; exact Subgroup.mul_mem _ ha' hb'⟩
  have hr := hm hu hu hU hU
  have hab := hm hu hv hU hV
  intro x hx
  rw [sg_E_eq hi] at hx
  simp only [e4Q, List.mem_cons, List.not_mem_nil, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨CFSG.KC.BfsPin.PP.id ch550106sz, by rw [e4c_pid]; exact Subgroup.one_mem _⟩
  · exact hr
  · exact ⟨hu, hU⟩
  · exact hm hu hr.1 hU hr.2
  · exact ⟨hv, hV⟩
  · exact hm hv hr.1 hV hr.2
  · exact hab
  · exact hm hab.1 hr.1 hab.2 hr.2

theorem sg_mem_T {i : Nat} (hi : i < 4) {g : Equiv.Perm (Fin 360)} (hg : g ∈ sgT i) :
    ∃ x ∈ sgE.getD i [], toPerm 360 9 x = g := by
  obtain ⟨-, -, hpU, hpV⟩ := sg_pm
  have h := allN_spec ch55118e i hi
  simp only [bAnd_iff] at h
  obtain ⟨-, hc, -⟩ := h
  unfold sgClos at hc
  simp only [bAnd_iff] at hc
  obtain ⟨h1, hcl⟩ := hc
  have hstep : ∀ c, CFSG.KC.BfsPin.PP 360 9 c → (∀ x ∈ sgE.getD i [], pc c x ∈ sgE.getD i []) →
      ∀ n : Nat, ∀ g, (∃ x ∈ sgE.getD i [], toPerm 360 9 x = g) →
        ∃ x ∈ sgE.getD i [], toPerm 360 9 x = toPerm 360 9 c ^ n * g := by
    intro c hpc hcL n
    induction n with
    | zero =>
      intro g hg
      rwa [pow_zero, one_mul]
    | succ n ih =>
      intro g hg
      obtain ⟨x, hx, e⟩ := ih g hg
      refine ⟨pc c x, hcL x hx, ?_⟩
      rw [pow_succ', mul_assoc, ← e, e4c_mul hpc (sg_E_sub hi x hx).1]
  have hgen : ∀ c, CFSG.KC.BfsPin.PP 360 9 c →
      (∀ x ∈ sgE.getD i [], pc c x ∈ sgE.getD i []) →
      (∀ g, (∃ x ∈ sgE.getD i [], toPerm 360 9 x = g) →
        ∃ x ∈ sgE.getD i [], toPerm 360 9 x = toPerm 360 9 c * g) ∧
      ∀ g, (∃ x ∈ sgE.getD i [], toPerm 360 9 x = g) →
        ∃ x ∈ sgE.getD i [], toPerm 360 9 x = (toPerm 360 9 c)⁻¹ * g := by
    intro c hpc hcL
    refine ⟨fun g hg => by simpa using hstep c hpc hcL 1 g hg, fun g hg => ?_⟩
    have hpos := orderOf_pos (toPerm 360 9 c)
    have e : (toPerm 360 9 c)⁻¹ = toPerm 360 9 c ^ (orderOf (toPerm 360 9 c) - 1) := by
      refine (eq_inv_of_mul_eq_one_left ?_).symm
      rw [← pow_succ, Nat.sub_add_cancel hpos, pow_orderOf_eq_one]
    rw [e]
    exact hstep c hpc hcL _ g hg
  have hU := hgen _ (hpU i hi) fun x hx => sg_mem_iff.1 (sg_and (allL_iff.1 hcl x hx)).1
  have hV := hgen _ (hpV i hi) fun x hx => sg_mem_iff.1 (sg_and (allL_iff.1 hcl x hx)).2
  unfold sgT at hg
  induction hg using Subgroup.closure_induction_left with
  | one => exact ⟨pid, sg_mem_iff.1 h1, e4c_pid⟩
  | mul_left a ha y _ hy =>
    rcases ha with rfl | rfl
    · exact hU.1 _ hy
    · exact hV.1 _ hy
  | inv_mul_cancel a ha y _ hy =>
    rcases ha with rfl | rfl
    · exact hU.2 _ hy
    · exact hV.2 _ hy

theorem sg_card_T {i : Nat} (hi : i < 4) : Nat.card (sgT i) = Nat.card (sgT 0) := by
  rcases Nat.eq_zero_or_pos i with rfl | hi0
  · rfl
  · obtain ⟨j, rfl⟩ : ∃ j, i = j + 1 := ⟨i - 1, by omega⟩
    rw [(sg_T_conj (by omega : j < 3)).2.2.1, sg_card_conj]

theorem sg_RU_conj : ∀ a ∈ RU.map Prod.fst,
    CFSG.KC.BfsPin.PP 360 9 a ∧ ∃ t ∈ e4H0, t * toPerm 360 9 e4U * t⁻¹ = toPerm 360 9 a := by
  obtain ⟨hp0, -, -, -, -, -, hpu, -⟩ := e4c_pm
  have hu := ch550106u
  simp only [bAnd_iff] at hu
  have h1 := hu.1
  unfold classK at h1
  rw [Bool.and_eq_true] at h1
  obtain ⟨hI, horb⟩ := h1
  have hA : ∀ k < 6, ∀ y, conjI 360 9 g0K gi0K k y = conjAct 360 9 g0K k y := by
    intro k hk y
    have e := Nat.eq_of_beq_eq_true (allN_spec hI k hk)
    unfold conjI conjAct
    rw [e]
  obtain ⟨-, hr⟩ := orbRecK_sound horb
  intro a ha
  obtain ⟨r, hr', rfl⟩ := List.mem_map.1 ha
  exact reach_conj hp0 hA hpu (hr r hr')

theorem sg_RU_complete {t : Equiv.Perm (Fin 360)} (ht : t ∈ e4H0) :
    ∃ a ∈ RU.map Prod.fst, toPerm 360 9 a = t * toPerm 360 9 e4U * t⁻¹ := by
  classical
  by_contra hno
  simp only [not_exists, not_and] at hno
  have hu := ch550106u
  simp only [bAnd_iff] at hu
  have h1 := hu.1
  unfold classK at h1
  rw [Bool.and_eq_true] at h1
  obtain ⟨hs, -⟩ := orbRecK_sound h1.2
  set S : Finset (Equiv.Perm (Fin 360)) := ((RU.map Prod.fst).map (toPerm 360 9)).toFinset
  have hS : S.card = 24 := by
    rw [List.toFinset_card_of_nodup, List.length_map, List.length_map,
      Nat.eq_of_beq_eq_true hu.2]
    refine List.Nodup.map_on (fun x hx y hy e => ?_) (hs.imp (fun h => Nat.ne_of_lt h))
    exact toPerm_injective (sg_RU_conj x hx).1 (sg_RU_conj y hy).1 e
  have hx : t * toPerm 360 9 e4U * t⁻¹ ∉ S := by
    intro hm
    obtain ⟨a, ha, e⟩ := List.mem_map.1 (List.mem_toFinset.1 hm)
    exact hno a ha e
  have hb := card_mul_card_centralizer_le (H := e4H0) (v := toPerm 360 9 e4U)
    (insert (t * toPerm 360 9 e4U * t⁻¹) S) (fun s hs' => by
      rcases Finset.mem_insert.1 hs' with rfl | hs'
      · exact ⟨t, ht, rfl⟩
      · obtain ⟨a, ha, rfl⟩ := List.mem_map.1 (List.mem_toFinset.1 hs')
        exact (sg_RU_conj a ha).2)
  rw [Finset.card_insert_of_notMem hx, hS, ← e4c_H1.1, e4c_H1.2, e4c_H0.2] at hb
  omega

theorem sg_R2 {h : Equiv.Perm (Fin 360)} (hh : h ∈ e4H2) :
    ∃ r ∈ sgR, CFSG.KC.BfsPin.PP 360 9 r.1 ∧ toPerm 360 9 r.1 = h := by
  classical
  obtain ⟨-, -, hp2, -, -, -, -, -⟩ := e4c_pm
  have hg := ch55118h
  simp only [bAnd_iff] at hg
  obtain ⟨hR, hlen⟩ := hg
  obtain ⟨hs, hr⟩ := orbRecK_sound hR
  have hval : ∀ x ∈ sgR.map Prod.fst, CFSG.KC.BfsPin.PP 360 9 x ∧ toPerm 360 9 x ∈ e4H2 := by
    intro x hx
    obtain ⟨r, hr', rfl⟩ := List.mem_map.1 hx
    exact e4c_reach_left hp2 (hr r hr')
  set S : Finset (Equiv.Perm (Fin 360)) := ((sgR.map Prod.fst).map (toPerm 360 9)).toFinset
  have hS : S.card = 1152 := by
    rw [List.toFinset_card_of_nodup, List.length_map, List.length_map,
      Nat.eq_of_beq_eq_true hlen]
    refine List.Nodup.map_on (fun x hx y hy e => ?_) (hs.imp (fun h => Nat.ne_of_lt h))
    exact toPerm_injective (hval x hx).1 (hval y hy).1 e
  by_cases hhS : h ∈ S
  · obtain ⟨x, hx, rfl⟩ := List.mem_map.1 (List.mem_toFinset.1 hhS)
    obtain ⟨r, hr', rfl⟩ := List.mem_map.1 hx
    exact ⟨r, hr', (hval _ hx).1, rfl⟩
  · have h1 := e4c_card_le (K := e4H2) (insert h S) (fun s hs' => by
      rcases Finset.mem_insert.1 hs' with rfl | hs'
      · exact hh
      · obtain ⟨x, hx, rfl⟩ := List.mem_map.1 (List.mem_toFinset.1 hs')
        exact (hval x hx).2)
    rw [Finset.card_insert_of_notMem hhS, hS, e4c_H2.2] at h1
    omega

theorem sg_gen {j : Nat} (hj : j < 10) (hp : CFSG.KC.BfsPin.PP 360 9 (AP.S j)) :
    gen j = toPerm 360 9 (AP.S j) := by
  rw [gen, gen_get hj, e4c_toPerm (permB_of_pp hp)]

theorem sg_S {s : Equiv.Perm (Fin 360)}
    (hs : s ∈ [1, gen 8, gen 8 * gen 8, gen 9, gen 9 * gen 8, gen 9 * (gen 8 * gen 8)]) :
    ∃ k < 6, CFSG.KC.BfsPin.PP 360 9 (sgS k) ∧ toPerm 360 9 (sgS k) = s := by
  obtain ⟨h8, h9, -, -⟩ := sg_pm
  have g8 := sg_gen (by norm_num) h8
  have g9 := sg_gen (by norm_num) h9
  have p1 := CFSG.KC.BfsPin.PP.id ch550106sz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
  rcases hs with rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨0, by norm_num, p1, e4c_pid⟩
  · exact ⟨1, by norm_num, h8, g8.symm⟩
  · exact ⟨2, by norm_num, h8.mul h8, by
      change toPerm 360 9 (pc (AP.S 8) (AP.S 8)) = _
      rw [e4c_mul h8 h8, g8]⟩
  · exact ⟨3, by norm_num, h9, g9.symm⟩
  · exact ⟨4, by norm_num, h9.mul h8, by
      change toPerm 360 9 (pc (AP.S 9) (AP.S 8)) = _
      rw [e4c_mul h9 h8, g8, g9]⟩
  · exact ⟨5, by norm_num, h9.mul (h8.mul h8), by
      change toPerm 360 9 (pc (AP.S 9) (pc (AP.S 8) (AP.S 8))) = _
      rw [e4c_mul (q := pc (AP.S 8) (AP.S 8)) h9 (h8.mul h8), e4c_mul h8 h8, g8, g9]⟩

theorem sgWalk_spec {Y : Nat} : ∀ (R : List (Nat × Nat × Nat × Nat)) (ps : List Nat),
    sgWalk Y R ps = true → ∀ r ∈ R, ∃ p, sgOne Y r.1 p = true
  | [], _, _, r, hr => absurd hr List.not_mem_nil
  | r :: R, ps, h, r', hr' => by
    have h' : bAnd(sgOne Y r.1 (ps.headD (nat_lit 360)), sgWalk Y R ps.tail) = true := h
    obtain ⟨h1, h2⟩ := sg_and h'
    rcases List.mem_cons.1 hr' with rfl | hr'
    · exact ⟨_, h1⟩
    · exact sgWalk_spec R ps.tail h2 r' hr'

theorem sgAt_spec {y : Nat} (h : sgAt y = true) :
    (sgFix y 1 = true ∨ sgFix y 2 = true ∨ sgFix y 3 = true) ∨
      (sgAct y 1 = false ∧ sgAct y 2 = false ∧ sgAct y 3 = false) := by
  unfold sgAt at h
  exact sg_at6 h

theorem sgAct_spec {y i : Nat} (h : sgAct y i = false) : ∀ j < 8,
    ¬ (pc (pc y (sgUK i)) y = sgNUK i j ∧ pc (pc y (sgVK i)) y = sgNVK i j) := by
  unfold sgAct sgActZ at h
  have h' := sg_of_not h
  intro j hj ⟨eu, ev⟩
  have e := sg_not_of (allN_spec h' j hj)
  rw [eu, ev, Nat.beq_refl, Nat.beq_refl] at e
  revert e
  decide

theorem sg_NU {i j : Nat} (hi : i < 4) (hj : j < 8) :
    CFSG.KC.BfsPin.PP 360 9 (sgNUK i j) ∧ CFSG.KC.BfsPin.PP 360 9 (sgNVK i j) ∧
    toPerm 360 9 (sgNUK i j) = toPerm 360 9 (sgEK i j) * toPerm 360 9 (sgUK i) *
      (toPerm 360 9 (sgEK i j))⁻¹ ∧
    toPerm 360 9 (sgNVK i j) = toPerm 360 9 (sgEK i j) * toPerm 360 9 (sgVK i) *
      (toPerm 360 9 (sgEK i j))⁻¹ := by
  obtain ⟨-, -, hpU, hpV⟩ := sg_pm
  have hlen : (sgE.getD i []).length = 8 := by rw [sg_E_eq hi]; rfl
  have hmem : ∀ j < 8, CFSG.KC.BfsPin.PP 360 9 (sgEK i j) := by
    intro j hj
    have hj' : j < (sgE.getD i []).length := by omega
    have hm : sgEK i j ∈ sgE.getD i [] := by
      rw [sgEK, List.getD_eq_getElem _ _ hj']
      exact List.getElem_mem _
    exact (sg_E_sub hi _ hm).1
  have h := allN_spec ch55118e i hi
  simp only [bAnd_iff] at h
  have e := allN_spec h.2.2 j hj
  simp only [bAnd_iff] at e
  obtain ⟨einv, eu, ev⟩ := e
  have hji : sgInv j < 8 := by
    interval_cases j <;> decide
  have hw := hmem j hj
  have hwi := hmem _ hji
  have hinv : toPerm 360 9 (sgEK i (sgInv j)) = (toPerm 360 9 (sgEK i j))⁻¹ := by
    refine eq_inv_of_mul_eq_one_right ?_
    rw [← e4c_mul hw hwi, Nat.eq_of_beq_eq_true einv, e4c_pid]
  rw [Nat.eq_of_beq_eq_true eu, Nat.eq_of_beq_eq_true ev]
  refine ⟨(hw.mul (hpU i hi)).mul hwi, (hw.mul (hpV i hi)).mul hwi, ?_, ?_⟩
  · rw [e4c_mul (p := pc (sgEK i j) (sgUK i)) (hw.mul (hpU i hi)) hwi, e4c_mul hw (hpU i hi),
      hinv]
  · rw [e4c_mul (p := pc (sgEK i j) (sgVK i)) (hw.mul (hpV i hi)) hwi, e4c_mul hw (hpV i hi),
      hinv]

theorem e4c_sg : ∀ y : Equiv.Perm (Fin 360),
    (∃ s ∈ [1, gen 8, gen 8 * gen 8, gen 9, gen 9 * gen 8, gen 9 * (gen 8 * gen 8)],
      s⁻¹ * y ∈ omegaT) →
    y * permOfArr 360 (u0A ()) = permOfArr 360 (u0A ()) * y →
    y * permOfArr 360 (v0A ()) = permOfArr 360 (v0A ()) * y → y * y = 1 →
    ∀ g ∈ omegaT, g * mainPerm 0 = mainPerm 0 * g →
    (Subgroup.closure {permOfArr 360 (u0A ()), permOfArr 360 (v0A ())}).map
        (MulAut.conj g).toMonoidHom ≠
      Subgroup.closure {permOfArr 360 (u0A ()), permOfArr 360 (v0A ())} →
    ∀ w ∈ (Subgroup.closure {permOfArr 360 (u0A ()), permOfArr 360 (v0A ())}).map
        (MulAut.conj g).toMonoidHom,
    (∀ b ∈ (Subgroup.closure {permOfArr 360 (u0A ()), permOfArr 360 (v0A ())}).map
        (MulAut.conj g).toMonoidHom, y * b * y⁻¹ = w * b * w⁻¹) →
    ∃ d ∈ omegaT, d * mainPerm 0 = mainPerm 0 * d ∧
      (Subgroup.closure {permOfArr 360 (u0A ()), permOfArr 360 (v0A ())}).map
          (MulAut.conj d).toMonoidHom ≠
        Subgroup.closure {permOfArr 360 (u0A ()), permOfArr 360 (v0A ())} ∧
      ∀ b ∈ (Subgroup.closure {permOfArr 360 (u0A ()), permOfArr 360 (v0A ())}).map
        (MulAut.conj d).toMonoidHom, y * b = b * y := by
  classical
  rw [← e4c_u0, ← e4c_v0, ← sg_T0]
  rintro y ⟨s, hs, hsy⟩ hyu hyv hyy g hg hgx hne w hw hact
  obtain ⟨hp0, -, -, -, -, -, hpu, hpv⟩ := e4c_pm
  obtain ⟨-, -, hpU, hpV⟩ := sg_pm
  have hH0 := e4c_H0.1
  have hH0Ω : ∀ {t}, t ∈ e4H0 → t ∈ omegaT ∧ t * mainPerm 0 = mainPerm 0 * t := fun ht => by
    rw [hH0] at ht
    obtain ⟨h1, h2⟩ := Subgroup.mem_inf.1 ht
    exact ⟨h1, Subgroup.mem_centralizer_singleton_iff.1 h2⟩
  obtain ⟨k, hk, hpS, rfl⟩ := sg_S hs
  have hy := ch55118y
  simp only [bAnd_iff] at hy
  obtain ⟨-, -, hlet, hyk⟩ := hy
  have e := allN_spec hyk k hk
  simp only [bAnd_iff] at e
  obtain ⟨eY, eYu, eYv⟩ := e
  have hc := wordK_sound ch550106sz hp0 _ (e4c_lets hlet k)
  have hpY : CFSG.KC.BfsPin.PP 360 9 (sgYK k) := by
    rw [Nat.eq_of_beq_eq_true eY]
    exact hpS.mul hc.1
  have hY : toPerm 360 9 (sgYK k) = toPerm 360 9 (sgS k) *
      toPerm 360 9 (wordK 360 9 g0K (sgW.getD k [])) := by
    rw [Nat.eq_of_beq_eq_true eY, e4c_mul hpS hc.1]
  have hcΩ := (hH0Ω hc.2).1
  have hYu : Commute (toPerm 360 9 (sgYK k)) (toPerm 360 9 e4U) := e4c_comm hpY hpu eYu
  have hYv : Commute (toPerm 360 9 (sgYK k)) (toPerm 360 9 om0V) := e4c_comm hpY hpv eYv
  set h := (toPerm 360 9 (sgYK k))⁻¹ * y with hdef
  have hhΩ : h ∈ omegaT := by
    have e1 : h = (toPerm 360 9 (wordK 360 9 g0K (sgW.getD k [])))⁻¹ *
        ((toPerm 360 9 (sgS k))⁻¹ * y) := by
      rw [hdef, hY, mul_inv_rev, mul_assoc]
    rw [e1]
    exact omegaT.mul_mem (omegaT.inv_mem hcΩ) hsy
  have hhH := e4c_mem_H2 hhΩ (hYu.inv_left.mul_left hyu) (hYv.inv_left.mul_left hyv)
  obtain ⟨r, hr, hpr, hrh⟩ := sg_R2 hhH
  have hyc : y = toPerm 360 9 (pc (sgYK k) r.1) := by
    rw [e4c_mul hpY hpr, hrh, hdef, mul_inv_cancel_left]
  have hpy : CFSG.KC.BfsPin.PP 360 9 (pc (sgYK k) r.1) := hpY.mul hpr
  obtain ⟨p, hp⟩ := sgWalk_spec sgR _ (allN_spec ch55118s k hk) r hr
  unfold sgOne at hp
  have hat : sgAt (pc (sgYK k) r.1) = true := by
    rcases sg_one3 hp with ⟨hb, hn⟩ | ⟨-, h2⟩
    · exfalso
      have hp360 : p < 360 := Nat.blt_eq.mp hb
      have e1 := congrArg (fun z : Equiv.Perm (Fin 360) => (z ⟨p, hp360⟩ : Nat)) hyy
      simp only [Equiv.Perm.coe_one, id_eq] at e1
      rw [hyc, e4c_mul hpY hpr] at e1
      simp only [Equiv.Perm.coe_mul, Function.comp_apply] at e1
      rw [toPerm_apply hpY, toPerm_apply hpr, toPerm_apply hpY, toPerm_apply hpr] at e1
      exact Nat.ne_of_beq_eq_false hn e1
    · exact h2
  rcases sgAt_spec hat with hfix | ⟨a1, a2, a3⟩
  ·
    obtain ⟨i, hi, hfi⟩ : ∃ i < 3, sgFix (pc (sgYK k) r.1) (i + 1) = true := by
      rcases hfix with h1 | h1 | h1
      · exact ⟨0, by norm_num, h1⟩
      · exact ⟨1, by norm_num, h1⟩
      · exact ⟨2, by norm_num, h1⟩
    obtain ⟨hpq, hqH, hTq, hUn⟩ := sg_T_conj hi
    unfold sgFix at hfi
    simp only [bAnd_iff] at hfi
    have cu := e4c_comm hpy (hpU (i + 1) (by omega)) hfi.1
    have cv := e4c_comm hpy (hpV (i + 1) (by omega)) hfi.2
    refine ⟨toPerm 360 9 (sgQK i), (hH0Ω hqH).1, (hH0Ω hqH).2, fun heq => ?_, fun b hb => ?_⟩
    · have hU : toPerm 360 9 (sgUK (i + 1)) ∈ sgT 0 := by
        rw [← heq, ← hTq]
        unfold sgT
        exact Subgroup.subset_closure (Set.mem_insert _ _)
      obtain ⟨x, hx, ex⟩ := sg_mem_T (by norm_num) hU
      have := toPerm_injective (sg_E_sub (by norm_num) x hx).1 (hpU (i + 1) (by omega)) ex
      exact hUn (this ▸ hx)
    · rw [← hTq] at hb
      have hle : sgT (i + 1) ≤ Subgroup.centralizer {y} := by
        rw [sgT, Subgroup.closure_le]
        rintro z (rfl | rfl)
        · rw [SetLike.mem_coe, Subgroup.mem_centralizer_singleton_iff, hyc]
          exact cu.symm
        · rw [SetLike.mem_coe, Subgroup.mem_centralizer_singleton_iff, hyc]
          exact cv.symm
      exact (Subgroup.mem_centralizer_singleton_iff.1 (hle hb)).symm
  ·
    exfalso
    have hgH : g ∈ e4H0 := by
      rw [hH0]
      exact Subgroup.mem_inf.2 ⟨hg, Subgroup.mem_centralizer_singleton_iff.2 hgx⟩
    obtain ⟨a, ha, ea⟩ := sg_RU_complete hgH
    have hr' := ch55118r
    simp only [bAnd_iff] at hr'
    obtain ⟨hpairs, hvm, huv⟩ := hr'
    obtain ⟨-, t, ht, et⟩ := sg_RU_conj om0V (sg_mem_iff.1 hvm)
    obtain ⟨b, hb, eb0⟩ := sg_RU_complete (e4H0.mul_mem hgH ht)
    have eb : toPerm 360 9 b = g * toPerm 360 9 om0V * g⁻¹ := by
      rw [eb0, ← et]
      group
    have hpa := (sg_RU_conj a ha).1
    have hpb := (sg_RU_conj b hb).1
    have hab : e4Comm a b = false := by
      cases hc : e4Comm a b
      · rfl
      · exfalso
        have c1 := e4c_comm hpa hpb hc
        rw [ea, eb] at c1
        have c2 : toPerm 360 9 e4U * toPerm 360 9 om0V =
            toPerm 360 9 om0V * toPerm 360 9 e4U := by
          simpa [mul_assoc] using congrArg (fun z => g⁻¹ * z * g) c1
        have c3 : pc e4U om0V = pc om0V e4U := toPerm_injective (hpu.mul hpv) (hpv.mul hpu)
          (by rw [e4c_mul hpu hpv, e4c_mul hpv hpu, c2])
        have c4 : e4Comm e4U om0V = false := by
          revert huv
          cases e4Comm e4U om0V <;> decide
        unfold e4Comm at c4
        rw [c3, Nat.beq_refl] at c4
        exact Bool.noConfusion c4
    have hco : sgCo a b = true := sg_or (allL_iff.1 (allL_iff.1 hpairs a ha) b hb) hab
    obtain ⟨i, hi, hin⟩ : ∃ i < 4, sgIn i a b = true := by
      unfold sgCo at hco
      rcases sg_or4 hco with h0 | h0 | h0 | h0
      · exact ⟨0, by norm_num, h0⟩
      · exact ⟨1, by norm_num, h0⟩
      · exact ⟨2, by norm_num, h0⟩
      · exact ⟨3, by norm_num, h0⟩
    unfold sgIn at hin
    simp only [bAnd_iff] at hin
    have haT := (sg_E_sub hi a (sg_mem_iff.1 hin.1)).2
    have hbT := (sg_E_sub hi b (sg_mem_iff.1 hin.2)).2
    have hB : (sgT 0).map (MulAut.conj g).toMonoidHom = sgT i := by
      refine Subgroup.eq_of_le_of_card_ge ?_ (le_of_eq (by rw [sg_card_T hi, sg_card_conj]))
      rw [sg_T0, sg_conj_closure, Subgroup.closure_le]
      rintro z (rfl | rfl)
      · rw [← ea]
        exact haT
      · rw [← eb]
        exact hbT
    rcases Nat.eq_zero_or_pos i with rfl | hi0
    · exact hne hB
    rw [hB] at hw hact
    obtain ⟨x, hx, rfl⟩ := sg_mem_T hi hw
    obtain ⟨j, hj, ej⟩ : ∃ j < 8, sgEK i j = x := by
      have hlen : (sgE.getD i []).length = 8 := by rw [sg_E_eq hi]; rfl
      obtain ⟨j, hj, ej⟩ := List.mem_iff_getElem.1 hx
      exact ⟨j, by omega, by rw [sgEK, List.getD_eq_getElem _ _ hj, ej]⟩
    subst ej
    obtain ⟨pnu, pnv, enu, env⟩ := sg_NU hi hj
    have hyi : y⁻¹ = y := inv_eq_of_mul_eq_one_right hyy
    have zu := hact (toPerm 360 9 (sgUK i)) (by
      unfold sgT
      exact Subgroup.subset_closure (Set.mem_insert _ _))
    have zv := hact (toPerm 360 9 (sgVK i)) (by
      unfold sgT
      exact Subgroup.subset_closure (Set.mem_insert_of_mem _ rfl))
    rw [← enu, hyi, hyc, ← e4c_mul hpy (hpU i hi),
      ← e4c_mul (p := pc (pc (sgYK k) r.1) (sgUK i)) (q := pc (sgYK k) r.1)
        (hpy.mul (hpU i hi)) hpy] at zu
    rw [← env, hyi, hyc, ← e4c_mul hpy (hpV i hi),
      ← e4c_mul (p := pc (pc (sgYK k) r.1) (sgVK i)) (q := pc (sgYK k) r.1)
        (hpy.mul (hpV i hi)) hpy] at zv
    have ai : sgAct (pc (sgYK k) r.1) i = false := by
      obtain ⟨i', rfl⟩ : ∃ i', i = i' + 1 := ⟨i - 1, by omega⟩
      have hi' : i' < 3 := by omega
      interval_cases i'
      · exact a1
      · exact a2
      · exact a3
    exact sgAct_spec ai j hj ⟨toPerm_injective ((hpy.mul (hpU i hi)).mul hpy) pnu zu,
      toPerm_injective ((hpy.mul (hpV i hi)).mul hpy) pnv zv⟩

end CertificateChecks.KernelO8.E4C

end
