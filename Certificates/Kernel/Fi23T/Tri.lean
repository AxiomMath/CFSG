module

public import Certificates.Kernel.Fi23T.Graph

public section

open Pointwise

namespace CertificateChecks.KernelFi23T

structure Cfg (P : Type*) where
  A : Subgroup (Equiv.Perm P)
  τ : P → Equiv.Perm P
  T : Finset P
  S : Set P
  x0 : P
  s1 : P
  f0 : P
  K : Set P
  e1 : P
  e2 : P
  e3 : P
  y2 : P
  y3 : P
  F1 : Finset P
  c1 : ℕ
  c2 : ℕ
  Kv : Set P
  d1 : P
  d2 : P
  d3 : P
  d4 : P
  z1 : P
  z2 : P
  M : Finset P
  t : P
  a1 : P
  a3 : P
  Gab : Set (Equiv.Perm P)

namespace Cfg

variable {P : Type*} [DecidableEq P] (C : Cfg P)

@[expose] def lab (e : P) : Finset P := C.τ C.f0 • C.τ e • C.T

@[expose] def v0 : Finset P := C.lab C.e1

@[expose] def Nr : Set (Finset P) := {V | ∃ f ∉ C.T, V = C.τ f • C.T}

@[expose] def N2 : Set (Finset P) := {W | W ≠ C.T ∧ W ∉ C.Nr ∧ ∃ x ∈ C.Nr, Adj C.τ x W}

@[expose] def Mu (V : Finset P) : Set (Finset P) := {x | x ∈ C.Nr ∧ Adj C.τ x V}

@[expose] def Vtx : Set (Finset P) := {V | ∃ g ∈ C.A, g • C.T = V}

@[expose] def B : Set (Finset P) := {V | V = C.T ∨ V ∈ C.Nr ∨ V ∈ C.N2}

@[expose] def H : Subgroup (Equiv.Perm P) := Subgroup.closure (C.τ '' C.S)

@[expose] def W : Subgroup (Equiv.Perm P) := Subgroup.closure (Set.range C.τ)

structure OK : Prop where
  sys : TSys C.A C.τ
  hS : ∀ s ∈ C.S, C.τ s • C.T = C.T
  h0 : C.τ C.x0 • C.T = C.T
  hcov : ∀ x ∈ C.T, x ∈ Orb C.τ C.S C.x0
  hST : C.S ⊆ C.T
  hs1 : C.s1 ∈ C.S
  hf0 : C.f0 ∉ C.T
  hTc : ∀ f ∉ C.T, f ∈ Orb C.τ C.S C.f0
  hc1 : (C.τ C.f0 • C.T ∩ C.T).card = C.c1
  hc1T : C.c1 ≠ C.T.card
  hK : C.K ⊆ C.T
  hKf : ∀ k ∈ C.K, C.τ k C.f0 = C.f0
  hF1 : ∀ e ∈ C.F1, e ∉ C.T ∧ e ∈ Orb C.τ C.K C.e1
  hKR : ∀ e ∉ C.T, e ∈ C.F1 ∨ e ∈ Orb C.τ C.K C.f0 ∨ e ∈ Orb C.τ C.K C.e2 ∨
    e ∈ Orb C.τ C.K C.e3
  hc2 : (C.lab C.e1 ∩ C.T).card = C.c2
  hc2T : C.c2 ≠ C.T.card
  hc21 : C.c2 ≠ C.c1
  hy2 : C.y2 ∉ C.T ∧ C.lab C.e2 = C.τ C.y2 • C.T
  hy3 : C.y3 ∉ C.T ∧ C.lab C.e3 = C.τ C.y3 • C.T
  hKv : ∀ k ∈ C.Kv, k ∈ C.T ∧ k ∈ C.v0
  hM : ∀ g ∈ C.M, g ∉ C.T ∧ (g ∈ Orb C.τ C.Kv C.d1 ∨ g ∈ Orb C.τ C.Kv C.d2)
  hMR : ∀ g ∉ C.T, g ∈ C.M ∨ g ∈ Orb C.τ C.Kv C.d3 ∨ g ∈ Orb C.τ C.Kv C.d4
  hd1 : C.d1 ∉ C.T ∧ C.z1 ∉ C.T ∧ C.τ C.d1 • C.v0 = C.τ C.z1 • C.T
  hd2 : C.d2 ∉ C.T ∧ C.z2 ∉ C.T ∧ C.τ C.d2 • C.v0 = C.τ C.z2 • C.T
  hd3 : (C.τ C.d3 • C.v0 ∩ C.T).card = C.c2
  hd4 : (C.τ C.d4 • C.v0 ∩ C.T).card = C.c2
  hmu : ∀ k ∈ C.Kv, k ∉ C.τ C.d1 • C.T
  ht : C.t ∉ C.τ C.d1 • C.T ∧ C.τ C.d2 • C.T = C.τ C.t • C.τ C.d1 • C.T
  hedR : ∀ h ∉ C.v0, h ∈ Orb C.τ C.Kv C.d1 ∨ h ∈ Orb C.τ C.Kv C.d2 ∨ h ∈ Orb C.τ C.Kv C.a1 ∨
    h ∈ Orb C.τ C.Kv C.a3
  hed1 : ∃ q ∉ C.T, ∃ z ∉ C.T, C.τ q • C.v0 = C.τ z • C.T ∧
    Adj C.τ (C.τ C.a1 • C.v0) (C.τ q • C.T)
  hed3 : ∃ q ∉ C.T, ∃ z ∉ C.T, C.τ q • C.v0 = C.τ z • C.T ∧
    Adj C.τ (C.τ C.a3 • C.v0) (C.τ q • C.T)
  hGab : Subgroup.closure C.Gab = C.A
  hgab : ∀ γ ∈ C.Gab, ∃ l : List P, γ • C.T = (l.map C.τ).prod • C.T

variable {C}

theorem adj_T_iff {V : Finset P} : Adj C.τ C.T V ↔ V ∈ C.Nr := Iff.rfl

namespace OK

variable (hC : C.OK)
include hC

theorem H_le : C.H ≤ C.A := hC.sys.closure_le C.S

theorem H_fix {g : Equiv.Perm P} (hg : g ∈ C.H) : g • C.T = C.T := TSys.fix_closure hC.hS hg

theorem fixT {x : P} (hx : x ∈ C.T) : C.τ x • C.T = C.T := hC.sys.fix_T hC.hS hC.h0 hC.hcov hx

theorem fixV {g : Equiv.Perm P} (hg : g ∈ C.A) {x : P} (hx : x ∈ g • C.T) :
    C.τ x • (g • C.T) = g • C.T := hC.sys.fix_mem hC.hS hC.h0 hC.hcov hg hx

theorem τ_H {x : P} (hx : x ∈ C.T) : C.τ x ∈ C.H :=
  hC.sys.τ_mem_H hC.hS hC.h0 hC.hcov hC.hST hC.hs1 hx

theorem closure_H {X : Set P} (hX : X ⊆ C.T) : Subgroup.closure (C.τ '' X) ≤ C.H := by
  rw [Subgroup.closure_le]
  rintro _ ⟨x, hx, rfl⟩
  exact hC.τ_H (hX hx)

theorem H_smul_τ {g : Equiv.Perm P} (hg : g ∈ C.H) (f : P) : g • C.τ f • C.T = C.τ (g f) • C.T :=
  hC.sys.smul_τ (hC.H_le hg) (hC.H_fix hg) f

theorem H_nr_aux {g : Equiv.Perm P} (hg : g ∈ C.H) {V : Finset P} (hV : V ∈ C.Nr) :
    g • V ∈ C.Nr := by
  obtain ⟨f, hf, rfl⟩ := hV
  exact ⟨g f, hC.sys.not_mem_smul (hC.H_fix hg) hf, hC.H_smul_τ hg f⟩

theorem H_nr {g : Equiv.Perm P} (hg : g ∈ C.H) {V : Finset P} : g • V ∈ C.Nr ↔ V ∈ C.Nr := by
  refine ⟨fun h => ?_, hC.H_nr_aux hg⟩
  have h' := hC.H_nr_aux (inv_mem hg) h
  rwa [inv_smul_smul] at h'

theorem H_T {g : Equiv.Perm P} (hg : g ∈ C.H) {V : Finset P} : g • V = C.T ↔ V = C.T := by
  constructor
  · intro h
    rw [← hC.H_fix hg] at h
    exact smul_left_cancel g h
  · rintro rfl
    exact hC.H_fix hg

theorem card_inter_H {g : Equiv.Perm P} (hg : g ∈ C.H) (X : Finset P) :
    (g • X ∩ C.T).card = (X ∩ C.T).card := by
  have e : g • X ∩ C.T = g • (X ∩ C.T) := by rw [Finset.smul_finset_inter, hC.H_fix hg]
  rw [e, Finset.card_smul_finset]

theorem nr_eq {f : P} (hf : f ∉ C.T) : ∃ g ∈ C.H, C.τ f • C.T = g • C.τ C.f0 • C.T := by
  obtain ⟨g, hg, rfl⟩ := hC.hTc f hf
  exact ⟨g, hg, (hC.H_smul_τ hg C.f0).symm⟩

theorem nr_card {V : Finset P} (hV : V ∈ C.Nr) : (V ∩ C.T).card = C.c1 := by
  obtain ⟨f, hf, rfl⟩ := hV
  obtain ⟨g, hg, e⟩ := hC.nr_eq hf
  rw [e, hC.card_inter_H hg, hC.hc1]

theorem nr_ne {V : Finset P} (hV : V ∈ C.Nr) : V ≠ C.T := by
  intro e
  have h := hC.nr_card hV
  rw [e, Finset.inter_self] at h
  exact hC.hc1T h.symm

theorem x0_nr : C.τ C.f0 • C.T ∈ C.Nr := ⟨C.f0, hC.hf0, rfl⟩

theorem KG_H : Subgroup.closure (C.τ '' C.K) ≤ C.H := hC.closure_H hC.hK

theorem KG_f0 {k : Equiv.Perm P} (hk : k ∈ Subgroup.closure (C.τ '' C.K)) : k C.f0 = C.f0 :=
  TSys.fix_closure_pt hC.hKf hk

theorem lab_eqv {k : Equiv.Perm P} (hk : k ∈ Subgroup.closure (C.τ '' C.K)) (e : P) :
    C.lab (k e) = k • C.lab e := by
  have hkH := hC.KG_H hk
  have hkA := hC.H_le hkH
  have hc : C.τ C.f0 * k = k * C.τ C.f0 := by
    have h1 := hC.sys.conj k hkA C.f0
    rw [hC.KG_f0 hk] at h1
    calc C.τ C.f0 * k = (k * C.τ C.f0 * k⁻¹) * k := by rw [← h1]
      _ = k * C.τ C.f0 := by group
  unfold lab
  rw [← hC.H_smul_τ hkH e, smul_smul, hc, mul_smul]

theorem lab_F1 {e : P} (he : e ∈ C.F1) : (C.lab e ∩ C.T).card = C.c2 := by
  obtain ⟨k, hk, rfl⟩ := (hC.hF1 e he).2
  rw [hC.lab_eqv hk, hC.card_inter_H (hC.KG_H hk), hC.hc2]

theorem lab_nr2 {e : P} (he : e ∈ Orb C.τ C.K C.e2) : C.lab e ∈ C.Nr := by
  obtain ⟨k, hk, rfl⟩ := he
  rw [hC.lab_eqv hk, hC.hy2.2]
  exact hC.H_nr_aux (hC.KG_H hk) ⟨C.y2, hC.hy2.1, rfl⟩

theorem lab_nr3 {e : P} (he : e ∈ Orb C.τ C.K C.e3) : C.lab e ∈ C.Nr := by
  obtain ⟨k, hk, rfl⟩ := he
  rw [hC.lab_eqv hk, hC.hy3.2]
  exact hC.H_nr_aux (hC.KG_H hk) ⟨C.y3, hC.hy3.1, rfl⟩

theorem lab_f0 {e : P} (he : e ∈ Orb C.τ C.K C.f0) : e = C.f0 := by
  obtain ⟨k, hk, rfl⟩ := he
  exact hC.KG_f0 hk

theorem lab_self : C.lab C.f0 = C.T := hC.sys.τ_τ _ _

theorem lab_eq_T {e : P} (he : e ∉ C.T) (h : C.lab e = C.T) : e = C.f0 := by
  rcases hC.hKR e he with h1 | h1 | h1 | h1
  · have h2 := hC.lab_F1 h1
    rw [h, Finset.inter_self] at h2
    exact absurd h2.symm hC.hc2T
  · exact hC.lab_f0 h1
  · exact absurd h (hC.nr_ne (hC.lab_nr2 h1))
  · exact absurd h (hC.nr_ne (hC.lab_nr3 h1))

theorem inj {e f : P} (he : e ∉ C.T) (hf : f ∉ C.T) (h : C.τ e • C.T = C.τ f • C.T) : e = f := by
  obtain ⟨g, hg, rfl⟩ := hC.hTc f hf
  have hgi := inv_mem hg
  have he' : g⁻¹ e ∉ C.T := hC.sys.not_mem_smul (hC.H_fix hgi) he
  have h1 : C.τ (g⁻¹ e) • C.T = C.τ C.f0 • C.T := by
    rw [← hC.H_smul_τ hgi, h, hC.H_smul_τ hgi, perm_inv_apply]
  have h2 : C.lab (g⁻¹ e) = C.T := by
    unfold lab
    rw [h1, hC.sys.τ_τ]
  rw [← hC.lab_eq_T he' h2, perm_apply_inv]

theorem lab_inj {e f : P} (he : e ∉ C.T) (hf : f ∉ C.T) (h : C.lab e = C.lab f) : e = f := by
  unfold lab at h
  exact hC.inj he hf (smul_left_cancel _ h)

theorem adj_x0 {V : Finset P} : Adj C.τ (C.τ C.f0 • C.T) V ↔ ∃ e ∉ C.T, V = C.lab e := by
  constructor
  · rintro ⟨h, hh, rfl⟩
    refine ⟨C.τ C.f0 h, fun hm => hh (hC.sys.mem_τ_smul.2 hm), ?_⟩
    unfold lab
    rw [hC.sys.conj_self, mul_smul, mul_smul, hC.sys.τ_τ]
  · rintro ⟨e, he, rfl⟩
    refine ⟨C.τ C.f0 e, fun hm => he ?_, ?_⟩
    · have h1 := hC.sys.mem_τ_smul.1 hm
      rwa [← Equiv.Perm.mul_apply, hC.sys.sq, Equiv.Perm.one_apply] at h1
    · unfold lab
      rw [hC.sys.conj_self, mul_smul, mul_smul, hC.sys.τ_τ]

theorem lab_far_iff {e : P} (he : e ∉ C.T) : (C.lab e ≠ C.T ∧ C.lab e ∉ C.Nr) ↔ e ∈ C.F1 := by
  constructor
  · rintro ⟨h1, h2⟩
    rcases hC.hKR e he with h | h | h | h
    · exact h
    · rw [hC.lab_f0 h] at h1
      exact absurd hC.lab_self h1
    · exact absurd (hC.lab_nr2 h) h2
    · exact absurd (hC.lab_nr3 h) h2
  · intro h
    have hc := hC.lab_F1 h
    refine ⟨fun e => ?_, fun hn => ?_⟩
    · rw [e, Finset.inter_self] at hc
      exact hC.hc2T hc.symm
    · rw [hC.nr_card hn] at hc
      exact hC.hc21 hc.symm

@[expose] def farNb (C : Cfg P) (V : Finset P) : Set (Finset P) :=
  {W | Adj C.τ V W ∧ W ≠ C.T ∧ W ∉ C.Nr}

omit hC in
theorem farNb_def {V W : Finset P} : W ∈ farNb C V ↔ Adj C.τ V W ∧ W ≠ C.T ∧ W ∉ C.Nr := Iff.rfl

theorem farNb_x0 : farNb C (C.τ C.f0 • C.T) = C.lab '' (C.F1 : Set P) := by
  ext W
  rw [farNb_def, hC.adj_x0]
  constructor
  · rintro ⟨⟨e, he, rfl⟩, h⟩
    exact ⟨e, (hC.lab_far_iff he).1 h, rfl⟩
  · rintro ⟨e, he, rfl⟩
    have heT := (hC.hF1 e he).1
    exact ⟨⟨e, heT, rfl⟩, (hC.lab_far_iff heT).2 he⟩

theorem farNb_H {g : Equiv.Perm P} (hg : g ∈ C.H) (V : Finset P) :
    farNb C (g • V) = g • farNb C V := by
  ext W
  constructor
  · rintro ⟨hadj, hT, hN⟩
    refine ⟨g⁻¹ • W, ⟨?_, ?_, ?_⟩, smul_inv_smul g W⟩
    · have h := hC.sys.adj_smul (hC.H_le (inv_mem hg)) hadj
      rwa [inv_smul_smul] at h
    · rwa [Ne, ← hC.H_T hg, smul_inv_smul]
    · rwa [← hC.H_nr hg, smul_inv_smul]
  · rintro ⟨W, ⟨hadj, hT, hN⟩, rfl⟩
    exact ⟨hC.sys.adj_smul (hC.H_le hg) hadj, by rwa [Ne, hC.H_T hg],
      by rwa [hC.H_nr hg]⟩

theorem far_card {V : Finset P} (hV : V ∈ C.Nr) : (farNb C V).ncard = C.F1.card := by
  obtain ⟨f, hf, rfl⟩ := hV
  obtain ⟨g, hg, e⟩ := hC.nr_eq hf
  rw [e, hC.farNb_H hg, Set.ncard_smul_set, hC.farNb_x0,
    Set.InjOn.ncard_image (fun a ha b hb h => hC.lab_inj (hC.hF1 a ha).1 (hC.hF1 b hb).1 h),
    Set.ncard_coe_finset]

theorem e1_F1 : C.lab C.e1 ≠ C.T ∧ C.lab C.e1 ∉ C.Nr := by
  refine ⟨fun e => ?_, fun hn => ?_⟩
  · have hc := hC.hc2
    rw [e, Finset.inter_self] at hc
    exact hC.hc2T hc.symm
  · have hc := hC.hc2
    rw [hC.nr_card hn] at hc
    exact hC.hc21 hc.symm

theorem e1_out : C.e1 ∉ C.T := by
  intro h
  have hn : C.lab C.e1 ∈ C.Nr := by
    unfold lab
    rw [hC.fixT h]
    exact hC.x0_nr
  exact hC.e1_F1.2 hn

theorem v0_N2 : C.v0 ∈ C.N2 :=
  ⟨hC.e1_F1.1, hC.e1_F1.2, _, hC.x0_nr, hC.adj_x0.2 ⟨C.e1, hC.e1_out, rfl⟩⟩

theorem H_N2 {g : Equiv.Perm P} (hg : g ∈ C.H) {W : Finset P} (hW : W ∈ C.N2) : g • W ∈ C.N2 := by
  obtain ⟨hT, hN, x, hx, hadj⟩ := hW
  exact ⟨by rwa [Ne, hC.H_T hg], by rwa [hC.H_nr hg], g • x, hC.H_nr_aux hg hx,
    hC.sys.adj_smul (hC.H_le hg) hadj⟩

theorem far_orbit {W : Finset P} (hW : W ∈ C.N2) : ∃ g ∈ C.H, W = g • C.v0 := by
  obtain ⟨hT, hN, x, ⟨f, hf, rfl⟩, hadj⟩ := hW
  obtain ⟨g, hg, e⟩ := hC.nr_eq hf
  rw [e] at hadj
  have h1 := hC.sys.adj_smul (hC.H_le (inv_mem hg)) hadj
  rw [inv_smul_smul] at h1
  obtain ⟨e', he', hW'⟩ := hC.adj_x0.1 h1
  have hF : e' ∈ C.F1 := by
    refine (hC.lab_far_iff he').1 ⟨?_, ?_⟩
    · rw [← hW', Ne, ← hC.H_T hg, smul_inv_smul]
      exact hT
    · rw [← hW', hC.H_nr (inv_mem hg)]
      exact hN
  obtain ⟨k, hk, rfl⟩ := (hC.hF1 e' hF).2
  refine ⟨g * k, mul_mem hg (hC.KG_H hk), ?_⟩
  rw [mul_smul, v0, ← hC.lab_eqv hk, ← hW', smul_inv_smul]

theorem N2_trans {W W' : Finset P} (hW : W ∈ C.N2) (hW' : W' ∈ C.N2) : ∃ g ∈ C.H, W' = g • W := by
  obtain ⟨g, hg, rfl⟩ := hC.far_orbit hW
  obtain ⟨g', hg', rfl⟩ := hC.far_orbit hW'
  exact ⟨g' * g⁻¹, mul_mem hg' (inv_mem hg), by rw [mul_smul, inv_smul_smul]⟩

theorem v0_eq : C.v0 = (C.τ C.f0 * C.τ C.e1) • C.T := by
  rw [mul_smul]
  rfl

theorem KvG_H : Subgroup.closure (C.τ '' C.Kv) ≤ C.H :=
  hC.closure_H fun k hk => (hC.hKv k hk).1

theorem KvG_v0 {k : Equiv.Perm P} (hk : k ∈ Subgroup.closure (C.τ '' C.Kv)) : k • C.v0 = C.v0 := by
  refine TSys.fix_closure (fun s hs => ?_) hk
  have hg : C.τ C.f0 * C.τ C.e1 ∈ C.A := mul_mem (hC.sys.mem _) (hC.sys.mem _)
  have h := (hC.hKv s hs).2
  rw [hC.v0_eq] at h ⊢
  exact hC.fixV hg h

theorem kv_act {k : Equiv.Perm P} (hk : k ∈ Subgroup.closure (C.τ '' C.Kv)) (g : P) :
    C.τ (k g) • C.v0 = k • C.τ g • C.v0 :=
  (hC.sys.smul_τ (hC.H_le (hC.KvG_H hk)) (hC.KvG_v0 hk) g).symm

theorem mu_crit {g : P} (hg : g ∉ C.T) : C.τ g • C.T ∈ C.Mu C.v0 ↔ C.τ g • C.v0 ∈ C.Nr := by
  have h : Adj C.τ (C.τ g • C.T) C.v0 ↔ Adj C.τ C.T (C.τ g • C.v0) := by
    rw [← hC.sys.adj_smul_iff (hC.sys.mem g), hC.sys.τ_τ]
  exact ⟨fun hm => h.1 hm.2, fun hn => ⟨⟨g, hg, rfl⟩, h.2 hn⟩⟩

theorem not_nr_c2 {V : Finset P} (hV : (V ∩ C.T).card = C.c2) : V ∉ C.Nr := fun hn => by
  rw [hC.nr_card hn] at hV
  exact hC.hc21 hV.symm

theorem kv_not_nr {k : Equiv.Perm P} (hk : k ∈ Subgroup.closure (C.τ '' C.Kv)) {d : P}
    (hd : (C.τ d • C.v0 ∩ C.T).card = C.c2) : C.τ (k d) • C.v0 ∉ C.Nr := by
  rw [hC.kv_act hk, hC.H_nr (hC.KvG_H hk)]
  exact hC.not_nr_c2 hd

theorem kv_nr {k : Equiv.Perm P} (hk : k ∈ Subgroup.closure (C.τ '' C.Kv)) {d z : P}
    (hz : z ∉ C.T) (hd : C.τ d • C.v0 = C.τ z • C.T) : C.τ (k d) • C.v0 ∈ C.Nr := by
  rw [hC.kv_act hk, hd]
  exact hC.H_nr_aux (hC.KvG_H hk) ⟨z, hz, rfl⟩

theorem mu_v0 : C.Mu C.v0 = (fun g => C.τ g • C.T) '' (C.M : Set P) := by
  ext x
  constructor
  · rintro ⟨⟨g, hg, rfl⟩, hadj⟩
    have hN : C.τ g • C.v0 ∈ C.Nr := (hC.mu_crit hg).1 ⟨⟨g, hg, rfl⟩, hadj⟩
    rcases hC.hMR g hg with h | ⟨k, hk, rfl⟩ | ⟨k, hk, rfl⟩
    · exact ⟨g, h, rfl⟩
    · exact absurd hN (hC.kv_not_nr hk hC.hd3)
    · exact absurd hN (hC.kv_not_nr hk hC.hd4)
  · rintro ⟨g, hg, rfl⟩
    refine (hC.mu_crit (hC.hM g hg).1).2 ?_
    rcases (hC.hM g hg).2 with ⟨k, hk, rfl⟩ | ⟨k, hk, rfl⟩
    · exact hC.kv_nr hk hC.hd1.2.1 hC.hd1.2.2
    · exact hC.kv_nr hk hC.hd2.2.1 hC.hd2.2.2

theorem mu_v0_card : (C.Mu C.v0).ncard = C.M.card := by
  rw [hC.mu_v0, Set.InjOn.ncard_image (fun a ha b hb h => hC.inj (hC.hM a ha).1 (hC.hM b hb).1
    h), Set.ncard_coe_finset]

theorem mu_H {g : Equiv.Perm P} (hg : g ∈ C.H) (V : Finset P) : C.Mu (g • V) = g • C.Mu V := by
  ext x
  constructor
  · rintro ⟨hx, hadj⟩
    refine ⟨g⁻¹ • x, ⟨by rwa [hC.H_nr (inv_mem hg)], ?_⟩, smul_inv_smul g x⟩
    have h := hC.sys.adj_smul (hC.H_le (inv_mem hg)) hadj
    rwa [inv_smul_smul] at h
  · rintro ⟨y, ⟨hy, hadj⟩, rfl⟩
    exact ⟨hC.H_nr_aux hg hy, hC.sys.adj_smul (hC.H_le hg) hadj⟩

theorem mu_card {W : Finset P} (hW : W ∈ C.N2) : (C.Mu W).ncard = C.M.card := by
  obtain ⟨g, hg, rfl⟩ := hC.far_orbit hW
  rw [hC.mu_H hg, Set.ncard_smul_set, hC.mu_v0_card]

@[expose] def MuR (C : Cfg P) (V : Finset P) (x y : Finset P) : Prop :=
  x ∈ C.Mu V ∧ y ∈ C.Mu V ∧ Adj C.τ x y

theorem kv_mu {k : Equiv.Perm P} (hk : k ∈ Subgroup.closure (C.τ '' C.Kv)) {x : Finset P}
    (hx : x ∈ C.Mu C.v0) : k • x ∈ C.Mu C.v0 := by
  have h := hC.mu_H (hC.KvG_H hk) C.v0
  rw [hC.KvG_v0 hk] at h
  rw [h]
  exact Set.smul_mem_smul_set hx

theorem m0_mu : C.τ C.d1 • C.T ∈ C.Mu C.v0 := by
  refine (hC.mu_crit hC.hd1.1).2 ?_
  rw [hC.hd1.2.2]
  exact ⟨_, hC.hd1.2.1, rfl⟩

theorem m1_mu : C.τ C.d2 • C.T ∈ C.Mu C.v0 := by
  refine (hC.mu_crit hC.hd2.1).2 ?_
  rw [hC.hd2.2.2]
  exact ⟨_, hC.hd2.2.1, rfl⟩

theorem mu_path0 : ∀ x ∈ C.Mu C.v0, Relation.ReflTransGen (MuR C C.v0) (C.τ C.d1 • C.T) x := by
  have hsym : ∀ a b, MuR C C.v0 a b → MuR C C.v0 b a :=
    fun a b h => ⟨h.2.1, h.1, hC.sys.adj_symm h.2.2⟩
  have hinv : ∀ g ∈ Subgroup.closure (C.τ '' C.Kv), ∀ a b, MuR C C.v0 a b →
      MuR C C.v0 (g • a) (g • b) := fun g hg a b h =>
    ⟨hC.kv_mu hg h.1, hC.kv_mu hg h.2.1, hC.sys.adj_smul (hC.H_le (hC.KvG_H hg)) h.2.2⟩
  have hgen : ∀ s ∈ C.τ '' C.Kv, s • (C.τ C.d1 • C.T) = C.τ C.d1 • C.T ∨
      MuR C C.v0 (C.τ C.d1 • C.T) (s • (C.τ C.d1 • C.T)) := by
    rintro _ ⟨k, hk, rfl⟩
    exact Or.inr ⟨hC.m0_mu, hC.kv_mu (Subgroup.subset_closure ⟨k, hk, rfl⟩) hC.m0_mu,
      k, hC.hmu k hk, rfl⟩
  have hp := path_closure hsym hinv hgen
  have hm01 : MuR C C.v0 (C.τ C.d1 • C.T) (C.τ C.d2 • C.T) :=
    ⟨hC.m0_mu, hC.m1_mu, C.t, hC.ht.1, hC.ht.2⟩
  rw [hC.mu_v0]
  rintro _ ⟨g, hg, rfl⟩
  have hkT : ∀ k ∈ Subgroup.closure (C.τ '' C.Kv), ∀ d, C.τ (k d) • C.T = k • C.τ d • C.T :=
    fun k hk d => (hC.H_smul_τ (hC.KvG_H hk) d).symm
  rcases (hC.hM g hg).2 with ⟨k, hk, rfl⟩ | ⟨k, hk, rfl⟩
  · beta_reduce
    rw [hkT k hk]
    exact hp k hk
  · beta_reduce
    rw [hkT k hk]
    exact (hp k hk).tail (hinv k hk _ _ hm01)

omit hC in
theorem path_symm {R : Finset P → Finset P → Prop} (hR : ∀ a b, R a b → R b a) {a b : Finset P}
    (h : Relation.ReflTransGen R a b) : Relation.ReflTransGen R b a := by
  induction h with
  | refl => exact .refl
  | tail _ hbc ih => exact (Relation.ReflTransGen.single (hR _ _ hbc)).trans ih

theorem mu_conn_v0 {x y : Finset P} (hx : x ∈ C.Mu C.v0) (hy : y ∈ C.Mu C.v0) :
    Relation.ReflTransGen (MuR C C.v0) x y :=
  (path_symm (fun a b h => ⟨h.2.1, h.1, hC.sys.adj_symm h.2.2⟩) (hC.mu_path0 x hx)).trans
    (hC.mu_path0 y hy)

theorem mu_conn {W : Finset P} (hW : W ∈ C.N2) {x y : Finset P} (hx : x ∈ C.Mu W)
    (hy : y ∈ C.Mu W) : Relation.ReflTransGen (MuR C W) x y := by
  obtain ⟨g, hg, rfl⟩ := hC.far_orbit hW
  rw [hC.mu_H hg] at hx hy
  obtain ⟨x, hx, rfl⟩ := hx
  obtain ⟨y, hy, rfl⟩ := hy
  have hR : ∀ a b, MuR C C.v0 a b → MuR C (g • C.v0) (g • a) (g • b) := fun a b h => by
    refine ⟨?_, ?_, hC.sys.adj_smul (hC.H_le hg) h.2.2⟩
    · rw [hC.mu_H hg]
      exact Set.smul_mem_smul_set h.1
    · rw [hC.mu_H hg]
      exact Set.smul_mem_smul_set h.2.1
  have h := hC.mu_conn_v0 hx hy
  clear hx hy
  induction h with
  | refl => exact .refl
  | tail _ hbc ih => exact ih.tail (hR _ _ hbc)

theorem mu_closed {W : Finset P} (hW : W ∈ C.N2) {X : Set (Finset P)} {x : Finset P}
    (hx : x ∈ X) (hX : X ⊆ C.Mu W) (hcl : ∀ a ∈ X, ∀ b ∈ C.Mu W, Adj C.τ a b → b ∈ X) :
    C.Mu W ⊆ X := by
  intro y hy
  have h := hC.mu_conn hW (hX hx) hy
  clear hy
  induction h with
  | refl => exact hx
  | tail _ hbc ih => exact hcl _ ih _ hbc.2.1 hbc.2.2

theorem ed_v0 {h : P} (hh : h ∉ C.v0) :
    C.τ h • C.v0 ∈ C.Nr ∨ ∃ m ∈ C.Mu C.v0, Adj C.τ (C.τ h • C.v0) m := by
  have hm : ∀ {k : Equiv.Perm P}, k ∈ Subgroup.closure (C.τ '' C.Kv) → ∀ {a : P},
      (∃ q ∉ C.T, ∃ z ∉ C.T, C.τ q • C.v0 = C.τ z • C.T ∧ Adj C.τ (C.τ a • C.v0) (C.τ q • C.T)) →
      ∃ m ∈ C.Mu C.v0, Adj C.τ (C.τ (k a) • C.v0) m := by
    intro k hk a ⟨q, hq, z, hz, he, hadj⟩
    refine ⟨k • C.τ q • C.T, hC.kv_mu hk ((hC.mu_crit hq).2 (he ▸ ⟨z, hz, rfl⟩)), ?_⟩
    rw [hC.kv_act hk]
    exact hC.sys.adj_smul (hC.H_le (hC.KvG_H hk)) hadj
  rcases hC.hedR h hh with ⟨k, hk, rfl⟩ | ⟨k, hk, rfl⟩ | ⟨k, hk, rfl⟩ | ⟨k, hk, rfl⟩
  · exact Or.inl (hC.kv_nr hk hC.hd1.2.1 hC.hd1.2.2)
  · exact Or.inl (hC.kv_nr hk hC.hd2.2.1 hC.hd2.2.2)
  · exact Or.inr (hm hk hC.hed1)
  · exact Or.inr (hm hk hC.hed3)

theorem ed {W U : Finset P} (hW : W ∈ C.N2) (hU : Adj C.τ W U) :
    U ∈ C.Nr ∨ ∃ m ∈ C.Mu W, Adj C.τ U m := by
  obtain ⟨g, hg, rfl⟩ := hC.far_orbit hW
  have h1 := hC.sys.adj_smul (hC.H_le (inv_mem hg)) hU
  rw [inv_smul_smul] at h1
  obtain ⟨h, hh, e⟩ := h1
  rcases hC.ed_v0 hh with hn | ⟨m, hm, hadj⟩
  · left
    rw [← hC.H_nr (inv_mem hg), e]
    exact hn
  · right
    refine ⟨g • m, by rw [hC.mu_H hg]; exact Set.smul_mem_smul_set hm, ?_⟩
    have h2 := hC.sys.adj_smul (hC.H_le hg) hadj
    rwa [← e, smul_inv_smul] at h2

theorem B_adj {V U : Finset P} (hV : V ∈ C.B) (hU : Adj C.τ V U) : U ∈ C.B := by
  have key : ∀ x ∈ C.Nr, Adj C.τ x U → U ∈ C.B := fun x hx hadj => by
    by_cases h1 : U = C.T
    · exact Or.inl h1
    by_cases h2 : U ∈ C.Nr
    · exact Or.inr (Or.inl h2)
    exact Or.inr (Or.inr ⟨h1, h2, x, hx, hadj⟩)
  rcases hV with rfl | hV | hV
  · exact Or.inr (Or.inl hU)
  · exact key V hV hU
  · rcases hC.ed hV hU with hn | ⟨m, hm, hadj⟩
    · exact Or.inr (Or.inl hn)
    · exact key m hm.1 (hC.sys.adj_symm hadj)

theorem B_word {V : Finset P} (hV : V ∈ C.B) : ∃ w ∈ C.W, V = w • C.T := by
  have hτ : ∀ x, C.τ x ∈ C.W := fun x => Subgroup.subset_closure ⟨x, rfl⟩
  rcases hV with rfl | ⟨f, -, rfl⟩ | ⟨-, -, x, ⟨f, -, rfl⟩, h, -, rfl⟩
  · exact ⟨1, one_mem _, (one_smul _ _).symm⟩
  · exact ⟨C.τ f, hτ f, rfl⟩
  · exact ⟨C.τ h * C.τ f, mul_mem (hτ h) (hτ f), (mul_smul _ _ _).symm⟩

theorem W_le : C.W ≤ C.A := by
  rw [W, Subgroup.closure_le]
  rintro _ ⟨x, rfl⟩
  exact hC.sys.mem x

theorem B_τ {V : Finset P} (hV : V ∈ C.B) (x : P) : C.τ x • V ∈ C.B := by
  obtain ⟨w, hw, rfl⟩ := hC.B_word hV
  by_cases hx : x ∈ w • C.T
  · rw [hC.fixV (hC.W_le hw) hx]
    exact hV
  · exact hC.B_adj hV ⟨x, hx, rfl⟩

theorem W_conj {γ : Equiv.Perm P} (hγ : γ ∈ C.A) {w : Equiv.Perm P} (hw : w ∈ C.W) :
    γ * w * γ⁻¹ ∈ C.W := by
  induction hw using Subgroup.closure_induction with
  | mem s hs =>
    obtain ⟨x, rfl⟩ := hs
    rw [← hC.sys.conj γ hγ x]
    exact Subgroup.subset_closure ⟨γ x, rfl⟩
  | one => rw [mul_one, mul_inv_cancel]; exact one_mem _
  | mul a b _ _ ha hb =>
    have e : γ * (a * b) * γ⁻¹ = (γ * a * γ⁻¹) * (γ * b * γ⁻¹) := by group
    rw [e]
    exact mul_mem ha hb
  | inv a _ ha =>
    have e : γ * a⁻¹ * γ⁻¹ = (γ * a * γ⁻¹)⁻¹ := by group
    rw [e]
    exact inv_mem ha

theorem list_W (l : List P) : (l.map C.τ).prod ∈ C.W :=
  C.W.list_prod_mem fun y hy => by
    obtain ⟨x, -, rfl⟩ := List.mem_map.1 hy
    exact Subgroup.subset_closure ⟨x, rfl⟩

variable [Fintype P]

theorem W_B {w : Equiv.Perm P} (hw : w ∈ C.W) : w • C.T ∈ C.B := by
  refine orbit_sub (X := C.B) (Or.inl rfl) (fun γ hγ V hV => ?_) w hw
  obtain ⟨x, rfl⟩ := hγ
  exact hC.B_τ hV x

theorem B_gab {γ : Equiv.Perm P} (hγ : γ ∈ C.Gab) {V : Finset P} (hV : V ∈ C.B) : γ • V ∈ C.B := by
  obtain ⟨w, hw, rfl⟩ := hC.B_word hV
  obtain ⟨l, hl⟩ := hC.hgab γ hγ
  have hγA : γ ∈ C.A := by
    rw [← hC.hGab]
    exact Subgroup.subset_closure hγ
  have e : γ • w • C.T = ((γ * w * γ⁻¹) * (l.map C.τ).prod) • C.T := by
    rw [mul_smul, ← hl, mul_smul, mul_smul, inv_smul_smul]
  rw [e]
  exact hC.W_B (mul_mem (hC.W_conj hγA hw) (hC.list_W l))

theorem vtx_eq : C.Vtx = C.B := by
  ext V
  constructor
  · rintro ⟨g, hg, rfl⟩
    rw [← hC.hGab] at hg
    exact orbit_sub (X := C.B) (Or.inl rfl) (fun γ hγ V hV => hC.B_gab hγ hV) g hg
  · intro hV
    obtain ⟨w, hw, rfl⟩ := hC.B_word hV
    exact ⟨w, hC.W_le hw, rfl⟩

theorem far_N2 {V : Finset P} (hV : V ∈ C.Vtx) (hT : V ≠ C.T) (hN : V ∉ C.Nr) : V ∈ C.N2 := by
  rw [hC.vtx_eq] at hV
  rcases hV with h | h | h
  · exact absurd h hT
  · exact absurd h hN
  · exact h

theorem nr_card_eq : C.Nr.ncard = C.Tᶜ.card := by
  have e : C.Nr = (fun f => C.τ f • C.T) '' ((C.Tᶜ : Finset P) : Set P) := by
    ext V
    simp only [Nr, Finset.coe_compl, Set.mem_compl_iff, Finset.mem_coe, Set.mem_image,
      Set.mem_setOf_eq]
    exact ⟨fun ⟨f, hf, e⟩ => ⟨f, hf, e.symm⟩, fun ⟨f, hf, e⟩ => ⟨f, hf, e.symm⟩⟩
  rw [e, Set.InjOn.ncard_image, Set.ncard_coe_finset]
  intro a ha b hb h
  simp only [Finset.coe_compl, Set.mem_compl_iff, Finset.mem_coe] at ha hb
  exact hC.inj ha hb h

theorem double_count : C.Nr.ncard * C.F1.card = C.N2.ncard * C.M.card := by
  classical
  have hs := Set.toFinite C.Nr
  have ht := Set.toFinite C.N2
  have h := Finset.card_mul_eq_card_mul (r := Adj C.τ) (s := hs.toFinset) (t := ht.toFinset)
    (m := C.F1.card) (n := C.M.card) ?_ ?_
  · rwa [← Set.ncard_eq_toFinset_card _ hs, ← Set.ncard_eq_toFinset_card _ ht] at h
  · intro x hx
    rw [Set.Finite.mem_toFinset] at hx
    rw [← hC.far_card hx, ← Set.ncard_coe_finset, Finset.coe_bipartiteAbove]
    congr 1
    ext W
    simp only [Set.Finite.mem_toFinset, Set.mem_setOf_eq, farNb_def]
    constructor
    · rintro ⟨⟨hT, hN, -⟩, hadj⟩
      exact ⟨hadj, hT, hN⟩
    · rintro ⟨hadj, hT, hN⟩
      exact ⟨⟨hT, hN, x, hx, hadj⟩, hadj⟩
  · intro W hW
    rw [Set.Finite.mem_toFinset] at hW
    rw [← hC.mu_card hW, ← Set.ncard_coe_finset, Finset.coe_bipartiteBelow]
    congr 1
    ext x
    simp only [Set.Finite.mem_toFinset, Set.mem_setOf_eq]
    rfl

theorem card_vtx : C.Vtx.ncard = 1 + C.Tᶜ.card + C.N2.ncard := by
  rw [hC.vtx_eq, ← hC.nr_card_eq]
  have e : C.B = ({C.T} ∪ C.Nr) ∪ C.N2 := by
    ext V
    simp only [B, Set.mem_union, Set.mem_singleton_iff, Set.mem_setOf_eq, or_assoc]
  rw [e, Set.ncard_union_eq, Set.ncard_union_eq, Set.ncard_singleton]
  · rw [Set.disjoint_singleton_left]
    exact fun h => hC.nr_ne h rfl
  · rw [Set.disjoint_union_left, Set.disjoint_singleton_left]
    refine ⟨fun h => h.1 rfl, ?_⟩
    rw [Set.disjoint_left]
    exact fun V hV hV' => hV'.2.1 hV

end OK

end Cfg

end CertificateChecks.KernelFi23T

end
