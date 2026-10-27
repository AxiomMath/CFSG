module

public import Certificates.Kernel.HN1408.XInnerChk
public import Certificates.Kernel.HN1408.XCentGlue
public import Certificates.Kernel.HN1408.TabXRecFacts
import CFSG.Certificates.Kernel.Spor.RawOrbEval

public section

set_option maxRecDepth 400000

namespace CFSG.KD.HN1408.XInner

open Subgroup CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KD.HN1408.CzT
open CFSG.KD.HN1408.TabX CFSG.KD.HN1408.XCent CFSG.EvenSporadicStandard.HNRecog
open CFSG.EvenSporadicStandard.HNRecog.Section4.XModel CFSG.EvenSporadicStandard.HNRecog.Section3

theorem conj_five {G : Type*} [Group G] [Finite G] (h25 : ¬ 25 ∣ Nat.card G) {c w y : G}
    (hc5 : c ^ 5 = 1) (hc1 : c ≠ 1) (hw : w * c = c ^ 2 * w) (hy5 : y ^ 5 = 1) (hy1 : y ≠ 1) :
    ∃ h : G, h * c * h⁻¹ = y := by
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  have key : ∀ x : G, orderOf x = 5 → ∃ S : Sylow 5 G, (S : Subgroup G) = zpowers x := by
    intro x hx
    have hp : IsPGroup 5 (zpowers x) :=
      IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hx, pow_one])
    obtain ⟨S, hS⟩ := hp.exists_le_sylow
    refine ⟨S, (Subgroup.eq_of_le_of_card_ge hS ?_).symm⟩
    rw [Nat.card_zpowers, hx]
    obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp S.isPGroup'
    have hd : Nat.card (S : Subgroup G) ∣ Nat.card G := Subgroup.card_subgroup_dvd_card _
    have hge : 5 ≤ Nat.card (S : Subgroup G) := by
      have := Subgroup.card_le_of_le hS
      rwa [Nat.card_zpowers, hx] at this
    rw [hn] at hd hge ⊢
    rcases n with _ | _ | n
    · norm_num at hge
    · norm_num
    · have h25' : (25 : ℕ) ∣ 5 ^ (n + 2) := ⟨5 ^ n, by ring⟩
      exact absurd (h25'.trans hd) h25
  obtain ⟨S, hS⟩ := key c (orderOf_eq_prime hc5 hc1)
  obtain ⟨T, hT⟩ := key y (orderOf_eq_prime hy5 hy1)
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq G S T
  have hm : ((g • S : Sylow 5 G) : Subgroup G) = (S : Subgroup G).map (MulAut.conj g).toMonoidHom := by
    rw [Sylow.coe_subgroup_smul, Subgroup.pointwise_smul_def]
    rfl
  have hyT : y ∈ (T : Subgroup G) := by
    rw [hT]
    exact mem_zpowers y
  rw [← hg, hm] at hyT
  obtain ⟨s, hs, hsy⟩ := Subgroup.mem_map.1 hyT
  have hsy' : g * s * g⁻¹ = y := by simpa [MulAut.conj_apply] using hsy
  rw [hS] at hs
  obtain ⟨n, hn⟩ := Submonoid.mem_powers_iff _ _ |>.1 (mem_powers_iff_mem_zpowers.2 hs)
  have oc : orderOf c = 5 := orderOf_eq_prime hc5 hc1
  have hn5 : c ^ (n % 5) = s := by rw [← oc, pow_mod_orderOf, hn]
  have hw' : w * c * w⁻¹ = c ^ 2 := by rw [hw, mul_inv_cancel_right]
  have hpw : ∀ m : ℕ, w * c ^ m * w⁻¹ = c ^ (2 * m) := by
    intro m
    rw [← conj_pow, hw', pow_mul]
  have hlt : n % 5 < 5 := Nat.mod_lt _ (by norm_num)
  generalize n % 5 = m at hn5 hlt
  subst hn5
  interval_cases m
  · exfalso
    rw [pow_zero, mul_one, mul_inv_cancel] at hsy'
    exact hy1 hsy'.symm
  · exact ⟨g, by rw [← hsy', pow_one]⟩
  · refine ⟨g * w, ?_⟩
    have e : g * w * c * (g * w)⁻¹ = g * (w * c * w⁻¹) * g⁻¹ := by group
    rw [e, hw', hsy']
  · refine ⟨g * w * w * w, ?_⟩
    have e : g * w * w * w * c * (g * w * w * w)⁻¹ =
        g * (w * (w * (w * c * w⁻¹) * w⁻¹) * w⁻¹) * g⁻¹ := by group
    have e8 : c ^ (2 * 4) = c ^ 3 := by
      rw [(by norm_num : 2 * 4 = 5 + 3), pow_add, hc5, one_mul]
    rw [e, hw', hpw 2, hpw 4, e8, hsy']
  · refine ⟨g * w * w, ?_⟩
    have e : g * w * w * c * (g * w * w)⁻¹ = g * (w * (w * c * w⁻¹) * w⁻¹) * g⁻¹ := by group
    rw [e, hw', hpw 2, hsy']

abbrev PR (F : Nat → Nat) (g : Equiv.Perm (Fin 1408)) : Prop :=
  ∀ x (hx : x < 1408), F x = (g ⟨x, hx⟩).val

theorem PR.comp {F H : Nat → Nat} {g h : Equiv.Perm (Fin 1408)} (hF : PR F g) (hH : PR H h) :
    PR (fun x => F (H x)) (g * h) := by
  intro x hx
  have hy : H x < 1408 := by rw [hH x hx]; exact Fin.isLt _
  have e : (⟨H x, hy⟩ : Fin 1408) = h ⟨x, hx⟩ := Fin.ext (hH x hx)
  change F (H x) = _
  rw [hF _ hy, e, Equiv.Perm.mul_apply]

theorem pr_id : PR (fun x => x) 1 := fun _ _ => rfl

theorem pr_pt {X : Nat} {g : Equiv.Perm (Fin 1408)} (h : RepC X g) : PR (pt X) g :=
  fun _ hx => repC_pt h hx

theorem pr_ev {c : Nat} (hc : c < 30720) : PR (ev c) (elC c) := fun _ hx => ev_elC hc hx

theorem pr_congr {F : Nat → Nat} {g h : Equiv.Perm (Fin 1408)} (hF : PR F g) (e : g = h) :
    PR F h := by
  rw [← e]
  exact hF

theorem relF_spec {X Xi Y Yi : Nat → Nat} {x xi y yi : Equiv.Perm (Fin 1408)} (hX : PR X x)
    (hXi : PR Xi xi) (hY : PR Y y) (hYi : PR Yi yi) :
    PR (relF X Xi Y Yi) (x * (x * (y * (xi * (yi * (x * (y * (xi * (xi * (y * (xi * (y *
      (xi * yi))))))))))))) := by
  intro p hp
  rw [relF.eq_1]
  exact (hX.comp (hX.comp (hY.comp (hXi.comp (hYi.comp (hX.comp (hY.comp (hXi.comp (hXi.comp
    (hY.comp (hXi.comp (hY.comp (hXi.comp hYi))))))))))))) p hp

theorem relA_eq {x y : Equiv.Perm (Fin 1408)} :
    x * (x * (y * (x⁻¹ * (y⁻¹ * (x * (y * (x⁻¹ * (x⁻¹ * (y * (x⁻¹ * (y * (x⁻¹ * y⁻¹)))))))))))) =
      Section4.relA x y := by
  simp only [Section4.relA, mul_assoc]

theorem pw4_spec {X : Nat → Nat} {x : Equiv.Perm (Fin 1408)} (hX : PR X x) (h5 : x ^ 5 = 1) :
    PR (pw4 X) x⁻¹ := by
  have e : x * (x * (x * x)) = x⁻¹ := by
    rw [eq_inv_iff_mul_eq_one, ← h5]
    simp only [pow_succ, pow_zero, one_mul, mul_assoc]
  intro p hp
  rw [pw4.eq_1]
  exact pr_congr (hX.comp (hX.comp (hX.comp hX))) e p hp

theorem pw2_spec {Y : Nat → Nat} {y : Equiv.Perm (Fin 1408)} (hY : PR Y y) (h3 : y ^ 3 = 1) :
    PR (pw2 Y) y⁻¹ := by
  have e : y * y = y⁻¹ := by
    rw [eq_inv_iff_mul_eq_one, ← h3]
    simp only [pow_succ, pow_zero, one_mul, mul_assoc]
  intro p hp
  rw [pw2.eq_1]
  exact pr_congr (hY.comp hY) e p hp

theorem relA_mem {G : Type*} [Group G] {K : Subgroup G} {x y : G} (hx : x ∈ K) (hy : y ∈ K) :
    Section4.relA x y ∈ K := by
  have hxi := K.inv_mem hx
  have hyi := K.inv_mem hy
  unfold Section4.relA
  repeat' apply K.mul_mem
  all_goals assumption

theorem relA_spec {X Y : Nat → Nat} {x y : Equiv.Perm (Fin 1408)} (hX : PR X x) (hY : PR Y y)
    (h5 : x ^ 5 = 1) (h3 : y ^ 3 = 1) : PR (relF X (pw4 X) Y (pw2 Y)) (Section4.relA x y) :=
  pr_congr (relF_spec hX (pw4_spec hX h5) hY (pw2_spec hY h3)) relA_eq

theorem headG_parts {C₁ C₂ Ha U₁ U₂ Ec : Nat} {Cd Dc : Nat → Nat}
    (h : xiHeadG C₁ C₂ Ha U₁ U₂ Ec Cd Dc = true) :
    (∀ k < 5, Cd k < 30720) ∧ (∀ k < 10, Dc k < 30720) ∧
    eqB (fun x => pt Ha (pt U₁ x)) (fun x => pt U₁ (pt Ha x)) = true ∧
    eqB (fun x => pt Ha (pt U₂ x)) (fun x => pt U₂ (pt Ha x)) = true ∧
    eqB (fun x => pt C₁ (ev (Cd 1) (ev (Cd 0) x))) (fun x => ev (Cd 0) (ev (Cd 1) x)) = true ∧
    eqB (fun x => pt C₂ (ev (Cd 3) (ev (Cd 2) x))) (fun x => ev (Cd 2) (ev (Cd 3) x)) = true ∧
    eqB (fun x => pt C₁ (pt C₁ (pt C₁ (pt C₁ (pt C₁ x))))) (fun x => x) = true ∧
    pt C₁ 0 ≠ 0 ∧
    eqB (fun x => pt C₂ (pt C₂ (pt C₂ x))) (fun x => x) = true ∧
    eqB (fun x => relF (pt C₁) (pw4 (pt C₁)) (pt C₂) (pw2 (pt C₂)) x) (fun x => pt Ha x) = true ∧
    eqB (fun x => ev (Cd 4) (pt C₁ x)) (fun x => pt C₁ (pt C₁ (ev (Cd 4) x))) = true ∧
    eqB (fun x => pt Ec (pt U₂ (pt U₁ x))) (fun x => pt U₁ (pt U₂ x)) = true ∧
    (∀ k < 10, eqB (fun x => ev (Dc k) (pt C₁ x)) (fun x => pt C₁ (ev (Dc k) x)) = true) := by
  unfold xiHeadG at h
  obtain ⟨h1, h⟩ := mkA h
  obtain ⟨h2, h⟩ := mkA h
  obtain ⟨h3, h⟩ := mkA h
  obtain ⟨h4, h⟩ := mkA h
  obtain ⟨h5, h⟩ := mkA h
  obtain ⟨h6, h⟩ := mkA h
  obtain ⟨h7, h⟩ := mkA h
  obtain ⟨h8, h⟩ := mkA h
  obtain ⟨h9, h⟩ := mkA h
  obtain ⟨h10, h⟩ := mkA h
  obtain ⟨h11, h⟩ := mkA h
  obtain ⟨h12, h13⟩ := mkA h
  refine ⟨fun k hk => Nat.blt_eq.mp (allN_spec h1 k hk),
    fun k hk => Nat.blt_eq.mp (allN_spec h2 k hk), h3, h4, h5, h6, h7, fun e => ?_, h9, h10, h11,
    h12, fun k hk => allN_spec h13 k hk⟩
  rw [e] at h8
  exact absurd (mkNot h8) (by decide : ¬ (Nat.beq 0 0 = false))

theorem head_gen {C₁ C₂ Ha U₁ U₂ W : Nat} {Cd Dc : Nat → Nat}
    (h : (strictB C₁ fun C₁ => strictB C₂ fun C₂ => strictB Ha fun Ha =>
      strictB U₁ fun U₁ => strictB U₂ fun U₂ => strictB (pwK C₁ C₂ W) fun Ec =>
        xiHeadG C₁ C₂ Ha U₁ U₂ Ec Cd Dc) = true) :
    xiHeadG C₁ C₂ Ha U₁ U₂ (pwK C₁ C₂ W) Cd Dc = true := by
  simp only [Orb.strictB_eq] at h
  exact h

theorem head_all :
    xiHeadG (CT 0) (CT 1) (WK wordA) (G 0) (G 1) (pwK (CT 0) (CT 1) wCom) cds dcs = true := by
  have h := head_ok
  rw [xiHead.eq_1] at h
  exact head_gen h

theorem repC_a : RepC (WK wordA) elemA := repC_word (by decide)

theorem a_memX : elemA ∈ P1408 ⊓ centralizer ({elemZ} : Set (Equiv.Perm (Fin 1408))) := by
  obtain ⟨-, -, -, ca, -⟩ := ctK_parts czT_ct
  exact mem_cent_of repC_a (elemW_mem _) ca

theorem u1_memX (hP : Nat.card ↥P1408 = 177408000) :
    elemW xU1 ∈ P1408 ⊓ centralizer ({elemZ} : Set (Equiv.Perm (Fin 1408))) := by
  rw [← closure_u hP]
  exact subset_closure (by simp)

theorem u2_memX (hP : Nat.card ↥P1408 = 177408000) :
    elemW xU2 ∈ P1408 ⊓ centralizer ({elemZ} : Set (Equiv.Perm (Fin 1408))) := by
  rw [← closure_u hP]
  exact subset_closure (by simp)

theorem c1_memX : elemW xC1 ∈ P1408 ⊓ centralizer ({elemZ} : Set (Equiv.Perm (Fin 1408))) :=
  nC_le XCent.c1_mem

theorem c2_memX : elemW xC2 ∈ P1408 ⊓ centralizer ({elemZ} : Set (Equiv.Perm (Fin 1408))) :=
  nC_le XCent.c2_mem

theorem cds_lt {k : Nat} (hk : k < 5) : cds k < 30720 := (headG_parts head_all).1 k hk

theorem dcs_lt {k : Nat} (hk : k < 10) : dcs k < 30720 := (headG_parts head_all).2.1 k hk

theorem eqX (hP : Nat.card ↥P1408 = 177408000) {f₁ f₂ : Nat → Nat} {g h : Equiv.Perm (Fin 1408)}
    (hg : g ∈ P1408 ⊓ centralizer ({elemZ} : Set (Equiv.Perm (Fin 1408))))
    (hh : h ∈ P1408 ⊓ centralizer ({elemZ} : Set (Equiv.Perm (Fin 1408))))
    (h1 : PR f₁ g) (h2 : PR f₂ h) (e : eqB f₁ f₂ = true) : g = h :=
  eq_of_eqB hP hg hh h1 h2 e

theorem a_central (hP : Nat.card ↥P1408 = 177408000) :
    ∀ x ∈ P1408 ⊓ centralizer ({elemZ} : Set (Equiv.Perm (Fin 1408))), x * elemA = elemA * x := by
  obtain ⟨-, -, e1, e2, -⟩ := headG_parts head_all
  have k1 : elemA * elemW xU1 = elemW xU1 * elemA :=
    eqX hP (mul_mem a_memX (u1_memX hP)) (mul_mem (u1_memX hP) a_memX)
      ((pr_pt repC_a).comp (pr_pt repC_u1)) ((pr_pt repC_u1).comp (pr_pt repC_a)) e1
  have k2 : elemA * elemW xU2 = elemW xU2 * elemA :=
    eqX hP (mul_mem a_memX (u2_memX hP)) (mul_mem (u2_memX hP) a_memX)
      ((pr_pt repC_a).comp (pr_pt repC_u2)) ((pr_pt repC_u2).comp (pr_pt repC_a)) e2
  intro x hx
  rw [← closure_u hP] at hx
  refine Section4.XModel.commute_of_mem_closure ?_ hx
  intro y hy
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hy
  rcases hy with rfl | rfl
  · exact k1.symm
  · exact k2.symm

theorem c_mem_derived (hP : Nat.card ↥P1408 = 177408000) :
    elemW xC1 ∈ derivedOf (P1408 ⊓ centralizer ({elemZ} : Set (Equiv.Perm (Fin 1408)))) ∧
      elemW xC2 ∈ derivedOf (P1408 ⊓ centralizer ({elemZ} : Set (Equiv.Perm (Fin 1408)))) := by
  obtain ⟨-, -, -, -, e1, e2, -⟩ := headG_parts head_all
  have m : ∀ k < 5, elC (cds k) ∈ P1408 ⊓ centralizer ({elemZ} : Set (Equiv.Perm (Fin 1408))) :=
    fun k hk => elC_mem hP (cds_lt hk)
  have r : ∀ k < 5, PR (ev (cds k)) (elC (cds k)) := fun k hk => pr_ev (cds_lt hk)
  have comm_of : ∀ {c p q : Equiv.Perm (Fin 1408)}, c * (q * p) = p * q →
      c = p * q * p⁻¹ * q⁻¹ := by
    intro c p q e
    rw [← e]
    group
  have d1 := eqX hP (mul_mem c1_memX (mul_mem (m 1 (by norm_num)) (m 0 (by norm_num))))
    (mul_mem (m 0 (by norm_num)) (m 1 (by norm_num)))
    ((pr_pt repC_c1).comp ((r 1 (by norm_num)).comp (r 0 (by norm_num))))
    ((r 0 (by norm_num)).comp (r 1 (by norm_num))) e1
  have d2 := eqX hP (mul_mem c2_memX (mul_mem (m 3 (by norm_num)) (m 2 (by norm_num))))
    (mul_mem (m 2 (by norm_num)) (m 3 (by norm_num)))
    ((pr_pt repC_c2).comp ((r 3 (by norm_num)).comp (r 2 (by norm_num))))
    ((r 2 (by norm_num)).comp (r 3 (by norm_num))) e2
  rw [comm_of d1, comm_of d2]
  exact ⟨Section4.XModel.mem_derivedOf_comm (m 0 (by norm_num)) (m 1 (by norm_num)),
    Section4.XModel.mem_derivedOf_comm (m 2 (by norm_num)) (m 3 (by norm_num))⟩

theorem c_orders (hP : Nat.card ↥P1408 = 177408000) :
    elemW xC1 ^ 5 = 1 ∧ elemW xC1 ≠ 1 ∧ elemW xC2 ^ 3 = 1 ∧
      Section4.relA (elemW xC1) (elemW xC2) = elemA := by
  obtain ⟨-, -, -, -, -, -, e5, e0, e3, er, -⟩ := headG_parts head_all
  have hc1 := pr_pt repC_c1
  have hc2 := pr_pt repC_c2
  have m1 := c1_memX
  have m2 := c2_memX
  have h5 : elemW xC1 ^ 5 = 1 := by
    have e := eqX hP (mul_mem m1 (mul_mem m1 (mul_mem m1 (mul_mem m1 m1)))) (one_mem _)
      (hc1.comp (hc1.comp (hc1.comp (hc1.comp hc1)))) pr_id e5
    rw [← e]
    simp only [pow_succ, pow_zero, one_mul, mul_assoc]
  have h3 : elemW xC2 ^ 3 = 1 := by
    have e := eqX hP (mul_mem m2 (mul_mem m2 m2)) (one_mem _) (hc2.comp (hc2.comp hc2)) pr_id e3
    rw [← e]
    simp only [pow_succ, pow_zero, one_mul, mul_assoc]
  have h1 : elemW xC1 ≠ 1 := by
    intro e
    apply e0
    rw [hc1 0 (by norm_num), e]
    rfl
  exact ⟨h5, h1, h3, eqX hP (relA_mem m1 m2) a_memX (relA_spec hc1 hc2 h5 h3) (pr_pt repC_a) er⟩

theorem w_conj (hP : Nat.card ↥P1408 = 177408000) :
    elC (cds 4) * elemW xC1 = elemW xC1 ^ 2 * elC (cds 4) := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, ew, -⟩ := headG_parts head_all
  have hw := cds_lt (k := 4) (by norm_num)
  have hwX := elC_mem hP hw
  have e := eqX hP (mul_mem hwX c1_memX) (mul_mem c1_memX (mul_mem c1_memX hwX))
    ((pr_ev hw).comp (pr_pt repC_c1)) ((pr_pt repC_c1).comp ((pr_pt repC_c1).comp (pr_ev hw))) ew
  rw [e, pow_two, mul_assoc]

theorem conj_c1 (hP : Nat.card ↥P1408 = 177408000) {y : Equiv.Perm (Fin 1408)}
    (hy : y ∈ P1408 ⊓ centralizer ({elemZ} : Set (Equiv.Perm (Fin 1408)))) (hy5 : y ^ 5 = 1)
    (hy1 : y ≠ 1) :
    ∃ h ∈ P1408 ⊓ centralizer ({elemZ} : Set (Equiv.Perm (Fin 1408))), h * elemW xC1 * h⁻¹ = y := by
  obtain ⟨h5, h1, -, -⟩ := c_orders hP
  have hw := w_conj hP
  have hwX := elC_mem hP (cds_lt (k := 4) (by norm_num))
  have hcard : Nat.card ↥(P1408 ⊓ centralizer ({elemZ} : Set (Equiv.Perm (Fin 1408)))) = 30720 := by
    rw [← (czT_eq hP).1]
    exact (czT_eq hP).2
  obtain ⟨h, hh⟩ := conj_five (G := ↥(P1408 ⊓ centralizer ({elemZ} : Set (Equiv.Perm (Fin 1408)))))
    (by rw [hcard]; norm_num) (c := ⟨elemW xC1, c1_memX⟩) (w := ⟨elC (cds 4), hwX⟩) (y := ⟨y, hy⟩)
    (Subtype.ext (by simpa using h5)) (fun e => h1 (congrArg Subtype.val e))
    (Subtype.ext (by simpa using hw)) (Subtype.ext (by simpa using hy5))
    (fun e => hy1 (congrArg Subtype.val e))
  exact ⟨h, h.2, by simpa using congrArg Subtype.val hh⟩

theorem inF2_of {Dc : Nat → Nat} {C₂ A B : Nat} (h : inF2 Dc C₂ A B = true) :
    ∃ k < 10, eqB (fun x => pt A (pt B (ev (Dc k) x))) (fun x => ev (Dc k) (pt C₂ x)) = true := by
  unfold inF2 at h
  simp only [Bool.not_eq_true'] at h
  by_contra hne
  push Not at hne
  have ha : allN 10 (fun k =>
      !(eqB (fun x => pt A (pt B (ev (Dc k) x))) (fun x => ev (Dc k) (pt C₂ x)))) = true := by
    refine Orb.allN_iff.2 fun k hk => ?_
    rw [Bool.eq_false_iff.2 (hne k hk)]
    rfl
  rw [ha] at h
  exact absurd h (by decide)

theorem f2Row_of {Dc : Nat → Nat} {C₁ C₂ a0 a1 A B : Nat} (h : f2Row Dc C₁ C₂ a0 a1 A B = true)
    (hc : eqB (fun x => pt A (pt B (pt A (pt B (pt A (pt B x)))))) (fun x => x) = true)
    (hr0 : relF (pt C₁) (pw4 (pt C₁)) (fun p => pt A (pt B p)) (pw2 (fun p => pt A (pt B p))) 0 = a0)
    (hr1 : relF (pt C₁) (pw4 (pt C₁)) (fun p => pt A (pt B p)) (pw2 (fun p => pt A (pt B p))) 1 = a1) :
    ∃ k < 10, eqB (fun x => pt A (pt B (ev (Dc k) x))) (fun x => ev (Dc k) (pt C₂ x)) = true := by
  unfold f2Row at h
  rw [hc, hr0, hr1, Nat.beq_refl, Nat.beq_refl] at h
  exact inF2_of h

theorem scan_all :
    czScan T0 T1 (f2Row dcs (CT 0) (CT 1) (pt (WK wordA) 0) (pt (WK wordA) 1)) = true := by
  have h := XInner.scan_ok
  rw [xiScan.eq_1] at h
  simp only [Orb.strictB_eq] at h
  exact h

theorem f2_facts (hP : Nat.card ↥P1408 = 177408000) :
    ∀ v ∈ P1408 ⊓ centralizer ({elemZ} : Set (Equiv.Perm (Fin 1408))), v ^ 3 = 1 →
      Section4.relA (elemW xC1) v = elemA →
      ∃ d ∈ P1408 ⊓ centralizer ({elemZ} : Set (Equiv.Perm (Fin 1408))),
        d * elemW xC1 = elemW xC1 * d ∧ d * elemW xC2 * d⁻¹ = v := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, ed⟩ := headG_parts head_all
  have h5 := (c_orders hP).1
  intro v hv hv3 hrel
  obtain ⟨i, hi, j, hj, rfl⟩ := (mem_iff hP).1 hv
  have hev : PR (fun x => pt (T0 i) (pt (T1 j) x)) (t0P i * t1P j) := fun x hx => ev_eq hi hj hx
  have hrow := czScan_spec scan_all i hi j hj
  have hcube : eqB (fun x => pt (T0 i) (pt (T1 j) (pt (T0 i) (pt (T1 j) (pt (T0 i)
      (pt (T1 j) x)))))) (fun x => x) = true :=
    eqB_of_eq (pr_congr (hev.comp (hev.comp hev)) (by rw [← hv3, pow_three])) pr_id
  have hR := relA_spec (pr_pt repC_c1) hev h5 hv3
  rw [hrel] at hR
  have hr0 := (hR 0 (by norm_num)).trans (repC_pt repC_a (x := 0) (by norm_num)).symm
  have hr1 := (hR 1 (by norm_num)).trans (repC_pt repC_a (x := 1) (by norm_num)).symm
  obtain ⟨k, hk, e⟩ := f2Row_of hrow hcube hr0 hr1
  have hd := dcs_lt hk
  have hdX := elC_mem hP hd
  have hvd : t0P i * t1P j * elC (dcs k) = elC (dcs k) * elemW xC2 :=
    eqX hP (mul_mem hv hdX) (mul_mem hdX c2_memX) (hev.comp (pr_ev hd))
      ((pr_ev hd).comp (pr_pt repC_c2)) e
  have hdc : elC (dcs k) * elemW xC1 = elemW xC1 * elC (dcs k) :=
    eqX hP (mul_mem hdX c1_memX) (mul_mem c1_memX hdX) ((pr_ev hd).comp (pr_pt repC_c1))
      ((pr_pt repC_c1).comp (pr_ev hd)) (ed k hk)
  refine ⟨elC (dcs k), hdX, hdc, ?_⟩
  rw [← hvd, mul_inv_cancel_right]

theorem der_leN (hP : Nat.card ↥P1408 = 177408000) :
    derivedOf (P1408 ⊓ centralizer ({elemZ} : Set (Equiv.Perm (Fin 1408)))) ≤ nC := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, ec, -⟩ := headG_parts head_all
  obtain ⟨e, he, hre⟩ := pwK_mem wCom
  have heX := nC_le he
  have k : e * (elemW xU2 * elemW xU1) = elemW xU1 * elemW xU2 :=
    eqX hP (mul_mem heX (mul_mem (u2_memX hP) (u1_memX hP))) (mul_mem (u1_memX hP) (u2_memX hP))
      ((pr_pt hre).comp ((pr_pt repC_u2).comp (pr_pt repC_u1)))
      ((pr_pt repC_u1).comp (pr_pt repC_u2)) ec
  have hu : elemW xU1 * elemW xU2 * (elemW xU1)⁻¹ * (elemW xU2)⁻¹ ∈ nC := by
    have e' : elemW xU1 * elemW xU2 * (elemW xU1)⁻¹ * (elemW xU2)⁻¹ = e := by
      rw [← k]
      group
    rw [e']
    exact he
  have hconj : ∀ u ∈ ({elemW xU1, elemW xU2} : Set (Equiv.Perm (Fin 1408))),
      ∀ c ∈ ({elemW xC1, elemW xC2} : Set (Equiv.Perm (Fin 1408))),
      u * c * u⁻¹ ∈ nC ∧ u⁻¹ * c * u ∈ nC := by
    intro u hu c hc
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hu hc
    rcases hu with rfl | rfl <;> rcases hc with rfl | rfl
    · exact norm_lk (by norm_num) (by norm_num) repC_u1 repC_c1
    · exact norm_lk (by norm_num) (by norm_num) repC_u1 repC_c2
    · exact norm_lk (by norm_num) (by norm_num) repC_u2 repC_c1
    · exact norm_lk (by norm_num) (by norm_num) repC_u2 repC_c2
  have h := Section4.derivedOf_le_of_gen hconj hu
  rw [closure_u hP] at h
  exact h

theorem xInnerK : Nat.card ↥P1408 = 177408000 → XNFacts := by
  intro hP
  obtain ⟨h5, h1, h3, hrel⟩ := c_orders hP
  obtain ⟨hc1, hc2⟩ := c_mem_derived hP
  have hgen := der_leN hP
  have hF1 : ∀ y ∈ derivedOf XP, y ^ 5 = 1 → y ≠ 1 → ∃ h ∈ XP, h * elemW xC1 * h⁻¹ = y :=
    fun y hy hy5 hy1 => conj_c1 hP (derivedOf_le _ hy) hy5 hy1
  have hF2 : ∀ v ∈ derivedOf XP, v ^ 3 = 1 → Section4.relA (elemW xC1) v = elemA →
      ∃ d ∈ XP, d * elemW xC1 = elemW xC1 * d ∧ d * elemW xC2 * d⁻¹ = v :=
    fun v hv => f2_facts hP v (derivedOf_le _ hv)
  exact ⟨a_memX, a_central hP,
    Section4.xAutInner_of_ambient XP a_memX (a_central hP) hc1 hc2 hgen h5 h1 h3 hrel hF1 hF2,
    fun g hg n hn => norm_nC hP g hg n hn, hgen, hc1, hc2⟩

end CFSG.KD.HN1408.XInner

end
