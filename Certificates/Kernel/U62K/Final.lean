module

public import Certificates.Kernel.U62K.Pts
public import Certificates.Kernel.U62K.Sound
public import Certificates.Kernel.U62K.Assemble

public section

set_option maxRecDepth 400000

namespace CertificateChecks.U62Final

open Subgroup CFSG.EvenSporadicStandard.Induction.Fi CertificateChecks.U62Lift
  CertificateChecks.U62Assemble CertificateChecks.KernelU62K
open CFSG.Sporadic.Th hiding J a b closure_ab gA gB rows_B_cube
open CFSG.Sporadic.Fi23 (J lvl slvl sylG)
open CertificateChecks.KernelFi23T2 (eL pB)

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent


theorem mem_T' {x : CFSG.Sporadic.Fi23.J} : x ∈ T' ↔ InT x := by
  unfold InT T'
  rw [Subgroup.mem_inf, mem_stabAt]

theorem finite_T' : Finite ↥T' :=
  Nat.finite_of_card_ne_zero (by
    rw [card_T' U62Pts.ls_facts.1 (CertificateChecks.KernelFi23T2.lG_mem (by norm_num))
      U62Pts.ls_facts.2.2]
    norm_num)

theorem card_T'' : Nat.card ↥T' = 131072 :=
  card_T' U62Pts.ls_facts.1 (CertificateChecks.KernelFi23T2.lG_mem (by norm_num))
    U62Pts.ls_facts.2.2

@[expose] noncomputable def E : Subgroup ↥T' :=
  Subgroup.closure {y : ↥T' | ∃ b ∈ CFSG.KD.U62K.D.B, (y : CFSG.Sporadic.Fi23.J) = eL b}

@[expose] def X : Set ↥T' := {y | ∃ m < 3, (y : CFSG.Sporadic.Fi23.J) = eL (CFSG.KD.U62K.D.P.getD m 0)}

theorem basis_T' {b : ℕ} (hb : b ∈ CFSG.KD.U62K.D.B) : eL b ∈ T' :=
  mem_T'.2 (basis_spec.2.1 b hb).2.1

theorem pB_E : ∀ {l : List ℕ}, (∀ a ∈ l, a ∈ CFSG.KD.U62K.D.B) → ∀ s,
    ∃ h : pB l s ∈ T', (⟨pB l s, h⟩ : ↥T') ∈ E
  | [], _, s => by
    have hm : pB [] s ∈ T' := by
      rw [CertificateChecks.KernelFi23T2.pB_nil]
      exact T'.one_mem
    refine ⟨hm, ?_⟩
    have e : (⟨pB [] s, hm⟩ : ↥T') = 1 := Subtype.ext (CertificateChecks.KernelFi23T2.pB_nil s)
    rw [e]
    exact E.one_mem
  | a :: l, hl, s => by
    obtain ⟨h1, h2⟩ := pB_E (fun b hb => hl b (List.mem_cons_of_mem _ hb)) (s / 2)
    have ha := hl a List.mem_cons_self
    by_cases hs : s % 2 = 1
    · have e : pB (a :: l) s = eL a * pB l (s / 2) := by
        rw [CertificateChecks.KernelFi23T2.pB_cons, if_pos hs]
      have hm : pB (a :: l) s ∈ T' := by
        rw [e]
        exact T'.mul_mem (basis_T' ha) h1
      refine ⟨hm, ?_⟩
      have e' : (⟨pB (a :: l) s, hm⟩ : ↥T') =
          ⟨eL a, basis_T' ha⟩ * ⟨pB l (s / 2), h1⟩ := Subtype.ext e
      rw [e']
      exact E.mul_mem (Subgroup.subset_closure ⟨a, ha, rfl⟩) h2
    · have e : pB (a :: l) s = pB l (s / 2) := by
        rw [CertificateChecks.KernelFi23T2.pB_cons, if_neg hs, one_mul]
      have hm : pB (a :: l) s ∈ T' := by
        rw [e]
        exact h1
      refine ⟨hm, ?_⟩
      have e' : (⟨pB (a :: l) s, hm⟩ : ↥T') = ⟨pB l (s / 2), h1⟩ := Subtype.ext e
      rw [e']
      exact h2

theorem E_comm : ∀ u ∈ E, ∀ v ∈ E, u * v = v * u :=
  CertificateChecks.U62Group.closure_comm fun x ⟨a, ha, hxa⟩ y ⟨b, hb, hyb⟩ =>
    Subtype.ext (by
      rw [Subgroup.coe_mul, Subgroup.coe_mul, hxa, hyb]
      exact basis_spec.2.2 a ha b hb)

theorem E_sq : ∀ u ∈ E, u * u = 1 :=
  CertificateChecks.U62Group.closure_sq
    (fun x ⟨a, ha, hxa⟩ y ⟨b, hb, hyb⟩ => Subtype.ext (by
      rw [Subgroup.coe_mul, Subgroup.coe_mul, hxa, hyb]
      exact basis_spec.2.2 a ha b hb))
    fun x ⟨a, ha, hxa⟩ => Subtype.ext (by
      rw [Subgroup.coe_mul, hxa, Subgroup.coe_one]
      exact (basis_spec.2.1 a ha).2.2)

theorem card_E : 2 ^ 11 ≤ Nat.card E := by
  obtain ⟨f, -, hf⟩ := masks_spec
  have hB : ∀ a ∈ CFSG.KD.U62K.D.B, a ∈ CFSG.KD.U62K.D.B := fun _ h => h
  let F : Fin 2048 → E := fun s =>
    ⟨⟨pB CFSG.KD.U62K.D.B (f s), (pB_E hB (f s)).1⟩, (pB_E hB (f s)).2⟩
  have hF : Function.Injective F := fun s t hst => hf (by
    have := congrArg (fun z : E => ((z : ↥T') : J)) hst
    exact this)
  have : Finite ↥T' := finite_T'
  have := Nat.card_le_card_of_injective F hF
  rw [Nat.card_eq_fintype_card (α := Fin 2048), Fintype.card_fin] at this
  norm_num
  exact this

theorem large_mem_E (x : ↥T') (hx : IsLargeInvAt 14 x) : x ∈ E := by
  have : Finite ↥T' := finite_T'
  obtain ⟨hsq, hne, hc⟩ := hx
  have hsq' : (x : J) * x = 1 := by rw [← Subgroup.coe_mul, hsq, Subgroup.coe_one]
  have hne' : (x : J) ≠ 1 := fun h => hne (Subtype.ext h)
  rcases cover_spec (mem_T'.1 x.2) hsq' hne' with ⟨m, -, hm⟩ | ⟨g, hg, hinj⟩
  · obtain ⟨h1, h2⟩ := pB_E (fun _ h => h) m
    have e : x = ⟨pB CFSG.KD.U62K.D.B m, h1⟩ := Subtype.ext hm
    rw [e]
    exact h2
  · exfalso
    let g' : Fin 9 → ↥T' := fun s => ⟨g s, mem_T'.2 (hg s)⟩
    have h9 := CertificateChecks.U62Group.mul_card_centralizer_le ({x} : Set ↥T') g'
      (fun s t hst => hinj (by
        have := congrArg (fun z : ↥T' => (z : J)) (hst x rfl)
        simpa [g'] using this))
    rw [card_T''] at h9
    omega

theorem mem_closure_sw {g : CFSG.Sporadic.Fi23.J} (hg : g ∈ T') :
    g ∈ Subgroup.closure {g | ∃ u < 84, wE (CFSG.KD.U62K.sw u) = g} := by
  obtain ⟨hL, -, ht⟩ := U62Pts.ls_facts
  set t := CFSG.Perm.pairG sylG 2
  set K := Subgroup.closure {g | ∃ u < 84, wE (CFSG.KD.U62K.sw u) = g}
  have hT := orbit_T hL
  have htT : t ∈ slvl 0 := CertificateChecks.KernelFi23T2.lG_mem (by norm_num)
  have hswap : ∀ x ∈ slvl 0, idx 31671 x 14566 ≠ 14566 →
      idx 31671 x 14566 = 18249 ∧ idx 31671 x 18249 = 14566 := by
    intro x hx hne
    obtain ⟨h1, h2⟩ := hT x hx
    have h1' : idx 31671 x 14566 = 18249 := h1.resolve_left hne
    refine ⟨h1', h2.resolve_right fun h => ?_⟩
    have i1 := idx_inv_idx (n := 31671) x 14566
    have i2 := idx_inv_idx (n := 31671) x 18249
    rw [h1'] at i1
    rw [h] at i2
    exact absurd (i1.symm.trans i2) (by norm_num)
  have htq' : idx 31671 t 18249 = 14566 := (hswap t htT (by rw [ht]; norm_num)).2
  have hsw : ∀ u < 84, wE (CFSG.KD.U62K.sw u) ∈ K := fun u hu => subset_closure ⟨u, hu, rfl⟩
  refine CertificateChecks.U62Group.le_of_index_two (S := {g | ∃ l < 42, CFSG.Perm.pairG sylG l = g})
    (H := stabAt 31671 14566) (K := K) t ?_ ?_ ?_ g (by rw [← slvl_zero_eq]; exact (mem_T'.1 hg).1) (mem_T'.1 hg).2
  · intro a ha b hb haH hbH
    rw [← slvl_zero_eq] at ha hb
    have ka := hswap a ha haH
    have kb := hswap b hb hbH
    change idx 31671 (a * b) 14566 = 14566
    rw [idx_mul, kb.1, ka.2]
  · rintro s ⟨l, hl, rfl⟩ hsH
    have hsH' : idx 31671 (CFSG.Perm.pairG sylG l) 14566 = 14566 := hsH
    have e1 := (sw_spec (u := l) (by omega)).2
    have e2 := (sw_spec (u := 42 + l) (by omega)).2
    rw [if_pos hl, if_pos hsH'] at e1
    have hmove : idx 31671 (t * CFSG.Perm.pairG sylG l) 14566 ≠ 14566 := by
      rw [idx_mul, hsH', ht]; norm_num
    rw [if_neg (by omega), show 42 + l - 42 = l by omega, if_neg hmove] at e2
    exact ⟨e1 ▸ hsw l (by omega), e2 ▸ hsw (42 + l) (by omega)⟩
  · rintro s ⟨l, hl, rfl⟩ hsH
    have hsH' : idx 31671 (CFSG.Perm.pairG sylG l) 14566 ≠ 14566 := hsH
    have e1 := (sw_spec (u := l) (by omega)).2
    have e2 := (sw_spec (u := 42 + l) (by omega)).2
    rw [if_pos hl, if_neg hsH'] at e1
    have hfix : idx 31671 (t * CFSG.Perm.pairG sylG l) 14566 = 14566 := by
      rw [idx_mul, (hswap _ (CertificateChecks.KernelFi23T2.lG_mem hl) hsH').1, htq']
    rw [if_neg (by omega), show 42 + l - 42 = l by omega, if_pos hfix] at e2
    exact ⟨e1 ▸ hsw l (by omega), e2 ▸ hsw (42 + l) (by omega)⟩

theorem X_large : ∀ y ∈ X, IsLargeInvAt 14 y := by
  rintro y ⟨m, hm, hy⟩
  have : Finite ↥T' := finite_T'
  classical
  obtain ⟨-, hsq, hne, hlen, hcl⟩ := class_spec hm
  refine ⟨Subtype.ext (by rw [Subgroup.coe_mul, hy, Subgroup.coe_one]; exact hsq),
    fun h => hne (by rw [← hy, h, Subgroup.coe_one]), ?_⟩
  let L : List ↥T' := (CFSG.KD.U62K.D.C.getD m []).map
    fun z => if h : eL z ∈ T' then ⟨eL z, h⟩ else 1
  have hL : L.length ≤ 8 := by rw [List.length_map]; exact hlen
  have hc := CertificateChecks.KernelFi23T2.card_le_cent y L hL (fun g => by
    obtain ⟨z, hz, e⟩ := hcl g (mem_closure_sw g.2)
    have hzT : eL z ∈ T' := by
      rw [← e]
      have hyT : eL (CFSG.KD.U62K.D.P.getD m 0) ∈ T' := by
        rw [← hy]
        exact y.2
      exact T'.mul_mem (T'.mul_mem g.2 hyT) (T'.inv_mem g.2)
    refine List.mem_map.2 ⟨z, hz, ?_⟩
    rw [dif_pos hzT]
    refine Subtype.ext ?_
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, hy]
    exact e.symm)
  rw [card_T''] at hc
  omega

theorem card_cX : Nat.card (centralizer X) ≤ Nat.card E := by
  have : Finite ↥T' := finite_T'
  obtain ⟨-, g, hg, hinj⟩ := orbit_spec
  let g' : Fin 64 → ↥T' := fun s => ⟨g s, mem_T'.2 (hg s)⟩
  have h64 := CertificateChecks.U62Group.mul_card_centralizer_le X g' (fun s t hst => hinj s t
    fun m hm => by
      have hmX : (⟨eL (CFSG.KD.U62K.D.P.getD m 0), mem_T'.2 (class_spec hm).1⟩ : ↥T') ∈ X := ⟨m, hm, rfl⟩
      have := congrArg (fun z : ↥T' => (z : J)) (hst _ hmX)
      simpa [g'] using this)
  rw [card_T''] at h64
  have := card_E
  omega

theorem u62_facts : CFSG.EvenSporadicStandard.Solomon78.InvolutionFixesElem ↥(lvl 2) 64 ∧
    ∃ x y : CFSG.Sporadic.Fi23.J, x ∈ lvl 2 ∧ y ∈ lvl 2 ∧ x * y * x⁻¹ * y⁻¹ = CFSG.Sporadic.Fi23.d := by
  obtain ⟨hL, hp, ht⟩ := U62Pts.ls_facts
  obtain ⟨⟨g, hg0, hg1⟩, x, y, hx, hy, hxy⟩ := U62Pts.pts_facts
  exact facts_of hL hp (CertificateChecks.KernelFi23T2.lG_mem (by norm_num)) ht hg0 hg1 E X
    large_mem_E E_comm E_sq X_large card_cX card_E hx hy hxy

end CertificateChecks.U62Final
