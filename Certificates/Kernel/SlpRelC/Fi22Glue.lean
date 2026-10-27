module

public import Certificates.Kernel.SlpRelC.Fi22
public import CFSG.Certificates.Kernel.SlpRelSound
public import Certificates.Kernel.Fi22Core.Conj
public import CFSG.HardMathSupport.Cooperstein.Coordinator.FFSporadic.Fi22CoverDefs
public import CFSG.Sporadic.Fi22.Class

public section

namespace CertificateChecks.KernelSlpRel

open CFSG.F3.Native CFSG.KC.Enum CFSG.KC.SlpRel CFSG.KS.SlpRel CFSG.KS.F3L CFSG.Sporadic.Fi22
open CertificateChecks.KernelFi22C
open CFSG.HardMathSupport.Cooperstein.Coordinator.FFSporadic
open CFSG.HardMathSupport.Meierfrankenfeld.FFToolkit

theorem frcV_eq (x : V) (k : V → Bool) : frcV x k = k x := by
  unfold frcV
  rw [strictB_eq, strictB_eq]

theorem fi22_cfg_of_rels {G : Type*} [Group G] (r : ℕ → G)
    (hr : ∀ p ∈ fi22HeisRels, (p.1.map r).prod = (p.2.map r).prod) (hz : r fi22HeisZ ≠ 1) :
    ∃ (x y : Fin 3 → G) (z : G), HeisCfg 3 3 x y z ∧ ∀ i, y i ^ 3 = 1 := by
  simp only [fi22HeisRels, List.forall_mem_cons, List.map_cons, List.map_nil, List.prod_cons,
    List.prod_nil, mul_one] at hr
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19,
    h20, h21, h22, h23, h24, h25, h26, h27, h28, -⟩ := hr
  refine ⟨_, _, _, heisCfg_three_three (pow_three_of_word h1) (pow_three_of_word h2)
    (pow_three_of_word h3) (pow_three_of_word h7) h8 h9 h10 h11 h12 h13 h14 h15 h16 h17 h18 h19
    h20 h21 h22 h23 h24 h25 h26 h27 h28 hz, fun i => ?_⟩
  fin_cases i
  · exact pow_three_of_word h4
  · exact pow_three_of_word h5
  · exact pow_three_of_word h6

theorem fi22_cover_of_rels {G : Type*} [Group G] (r : ℕ → G)
    (hr : ∀ p ∈ fi22CoverRels, (p.1.map r).prod = (p.2.map r).prod) (hz : r 41 ≠ 1) :
    Fi22CoverData (r 35) (r 31) (r 47) (r 45) (r 48) (r 46) (r 41) (r 49) (r 50) (r 28) := by
  simp only [fi22CoverRels, List.forall_mem_cons, List.map_cons, List.map_nil, List.prod_cons,
    List.prod_nil, mul_one] at hr
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19,
    h20, h21, h22, h23, h24, h25, h26, h27, h28, dBp0, dBp1, dBp2, dBq0, dBq1, dBq2, dBz, dAp0,
    dAp1, dAp2, dAq0, dAq1, dAq2, dAz, np0, nq0, np1, nq1, nz, -⟩ := hr
  exact ⟨heisCfg_three_three (pow_three_of_word h1) (pow_three_of_word h2)
    (pow_three_of_word h3) (pow_three_of_word h7) h8 h9 h10 h11 h12 h13 h14 h15 h16 h17 h18 h19
    h20 h21 h22 h23 h24 h25 h26 h27 h28 hz,
    pow_three_of_word h4, pow_three_of_word h5, pow_three_of_word h6,
    dBp0, dBp1, dBp2, dBq0, dBq1, dBq2, dBz, dAp0, dAp1, dAp2, dAq0, dAq1, dAq2, dAz,
    np0, nq0, np1, nq1, nz⟩

theorem fi22_cfg_exists_of_rels {G H : Type*} [Group G] [Group H] (f : G →* H)
    (hf : Function.Injective f) (r : ℕ → G)
    (hr : ∀ p ∈ fi22HeisRels, (p.1.map r).prod = (p.2.map r).prod) (hz : r fi22HeisZ ≠ 1) :
    ∃ (x y : Fin 3 → H) (z : H), HeisCfg 3 3 x y z ∧ ∀ i, y i ^ 3 = 1 := by
  obtain ⟨x, y, z, hc, hy⟩ := fi22_cfg_of_rels r hr hz
  have hfz : f z ≠ 1 := fun h1 => hc.z1 (hf (by rw [map_one]; exact h1))
  exact ⟨_, _, _, hc.map f hfz, fun i => by rw [← map_pow, hy i, map_one]⟩

theorem fi22_cover_exists_of_rels {G H : Type*} [Group G] [Group H] (f : G →* H)
    (hf : Function.Injective f) (r : ℕ → G)
    (hr : ∀ p ∈ fi22CoverRels, (p.1.map r).prod = (p.2.map r).prod) (hz : r 41 ≠ 1) :
    ∃ p₀ p₁ p₂ q₀ q₁ q₂ z dA dB n : H, Fi22CoverData p₀ p₁ p₂ q₀ q₁ q₂ z dA dB n := by
  have h := fi22_cover_of_rels r hr hz
  exact ⟨_, _, _, _, _, _, _, _, _, _,
    h.map f (fun h1 => h.heis.z1 (hf (by rw [map_one]; exact h1)))⟩

theorem fi22SlpK_conj {ml : Nat → Nat → V → V → V} {sp₀ : Nat} {la lb li : V} {nz : V → Bool}
    {prog : List (List Nat)} {ps : List (List Nat × List Nat)} {ne : List Nat}
    (h : (strictB sp₀ fun sp => frcV la fun a => frcV lb fun b => frcV li fun one =>
      slpRelK frcV (ml (nat_lit 77) sp) one eqF nz [a, b] prog ps ne) = true) :
    slpRelK frcV (ml (nat_lit 77) sp₀) li eqF nz [la, lb] prog ps ne = true := by
  simp only [strictB_eq, frcV_eq] at h
  exact h

section Model

variable {G : Type*} [Group G] (φ : G →* Matrix (Fin 77) (Fin 77) (ZMod 3))

@[expose] def Fi22Rep (X : V) (g : G) : Prop := RowsWF (unlane 77 X) ∧ toMat 77 (unlane 77 X) = φ g

variable {φ}

theorem fi22Rep_mul {X Y : V} {g h : G} (hX : Fi22Rep φ X g) (hY : Fi22Rep φ Y h) :
    Fi22Rep φ (mulLane (nat_lit 77) SP X Y) (g * h) := by
  have e : unlane 77 (mulLane (nat_lit 77) SP X Y) = mul 77 (unlane 77 X) (unlane 77 Y) :=
    (mul_eq' X Y).symm
  refine ⟨by rw [e]; exact RowsWF.mul _ 77 hX.1 hY.1, ?_⟩
  rw [e, toMat_mul (unlane_size' X) hX.1 hY.1, hX.2, hY.2, map_mul] <;> rfl

theorem fi22Rep_one : Fi22Rep φ LI 1 := by
  refine ⟨by rw [← idM_eq]; exact RowsWF.idM 77, ?_⟩
  rw [← idM_eq, toMat_idM, map_one] <;> rfl

theorem fi22Rep_eq (hφ : Function.Injective φ) {X Y : V} {g h : G} (hX : Fi22Rep φ X g)
    (hY : Fi22Rep φ Y h) (e : eqF X Y = true) : g = h :=
  hφ (by rw [← hX.2, ← hY.2, eqF_iff.1 e])

theorem fi22NZ_spec {X : V} {g : G} (hX : Fi22Rep φ X g) (h : fi22NZ X = true) : g ≠ 1 := by
  rintro rfl
  have hm := congrFun (congrFun hX.2 0) 0
  rw [map_one, Matrix.one_apply_eq, toMat_apply] at hm
  have hb : (unlane 77 X)[(0 : Fin 77).val]! = blk 77 X 0 := unlane_get X (by norm_num)
  rw [hb] at hm
  have hp : X.p % 2 = 0 := by
    have e := Nat.eq_of_beq_eq_true h
    rw [← Nat.and_one_is_mod]
    exact e
  have hpb : (blk 77 X 0).p.testBit 0 = false := by
    rw [blk_p]
    simp [Nat.testBit_zero, hp]
  have hv : (blk 77 X 0).get 0 = 0 ∨ (blk 77 X 0).get 0 = 2 := by
    unfold V.get
    rw [hpb]
    by_cases hm' : (blk 77 X 0).m.testBit 0 <;> simp [hm']
  unfold V.val at hm
  simp only [Fin.val_zero] at hm
  rcases hv with e | e <;> rw [e] at hm <;> exact absurd hm (by decide)

theorem fi22_hinit {gA gB : G} (hA : toMat 77 (unlane 77 LA) = φ gA)
    (hB : toMat 77 (unlane 77 LB) = φ gB) : RepL (Fi22Rep φ) LI [LA, LB] [gA, gB] := by
  have cs := canons
  refine ⟨rfl, fun i => ?_⟩
  match i with
  | 0 =>
    simp only [List.getD_cons_zero]
    exact ⟨rowsWF_unlane cs.1.wf, hA⟩
  | 1 =>
    simp only [List.getD_cons_succ, List.getD_cons_zero]
    exact ⟨rowsWF_unlane cs.2.1.wf, hB⟩
  | i + 2 =>
    simp only [List.getD_cons_succ, List.getD_nil]
    exact fi22Rep_one

theorem fi22Slp_rels (hφ : Function.Injective φ) {gA gB : G}
    (hA : toMat 77 (unlane 77 LA) = φ gA) (hB : toMat 77 (unlane 77 LB) = φ gB)
    {prog : List (List Nat)} {ps : List (List Nat × List Nat)} {ne : List Nat}
    (h : fi22SlpK prog ps ne = true) :
    (∀ p ∈ ps, (p.1.map fun l => (slpG prog [gA, gB]).getD (l - 1) 1).prod =
      (p.2.map fun l => (slpG prog [gA, gB]).getD (l - 1) 1).prod) ∧
      ∀ l ∈ ne, (slpG prog [gA, gB]).getD (l - 1) 1 ≠ 1 := by
  unfold fi22SlpK at h
  have hc := fi22SlpK_conj (ml := mulLane) (sp₀ := SP) (la := LA) (lb := LB) (li := LI)
    (nz := fi22NZ) h
  exact slpRelK_sound (Rep := Fi22Rep φ) (frc := frcV) (mul := mulLane (nat_lit 77) SP)
    (one := LI) (eq := eqF) (nz := fi22NZ) (init := [LA, LB]) (gens := [gA, gB])
    (fun _ _ _ _ hX hY => fi22Rep_mul hX hY) fi22Rep_one frcV_eq
    (fun _ _ _ _ hX hY e => fi22Rep_eq hφ hX hY e) (fun _ _ hX hz => fi22NZ_spec hX hz)
    (fi22_hinit hA hB) hc

theorem fi22_heis_of_seeds {H : Type*} [Group H] (hφ : Function.Injective φ) {gA gB : G}
    (hA : toMat 77 (unlane 77 LA) = φ gA) (hB : toMat 77 (unlane 77 LB) = φ gB) (f : G →* H)
    (hf : Function.Injective f) :
    ∃ (x y : Fin 3 → H) (z : H), HeisCfg 3 3 x y z ∧ ∀ i, y i ^ 3 = 1 :=
  fi22_cfg_exists_of_rels f hf _ (fi22Slp_rels hφ hA hB ch129040_ok).1
    ((fi22Slp_rels hφ hA hB ch129040_ok).2 _ List.mem_cons_self)

theorem fi22_cover_of_seeds {H : Type*} [Group H] (hφ : Function.Injective φ) {gA gB : G}
    (hA : toMat 77 (unlane 77 LA) = φ gA) (hB : toMat 77 (unlane 77 LB) = φ gB) (f : G →* H)
    (hf : Function.Injective f) :
    ∃ p₀ p₁ p₂ q₀ q₁ q₂ z dA dB n : H, Fi22CoverData p₀ p₁ p₂ q₀ q₁ q₂ z dA dB n :=
  fi22_cover_exists_of_rels f hf _ (fi22Slp_rels hφ hA hB ch129041_ok).1
    ((fi22Slp_rels hφ hA hB ch129041_ok).2 _ List.mem_cons_self)

end Model

section Concrete


@[expose] noncomputable def fi22Hom : J →* Matrix (Fin 77) (Fin 77) (ZMod 3) :=
  (Units.coeHom _).comp J.subtype

theorem fi22Hom_injective : Function.Injective fi22Hom :=
  fun _ _ e => Subtype.ext (Units.ext e)

theorem fi22Hom_a : toMat 77 (unlane 77 LA) = fi22Hom a := by
  rw [← matA_eq, ← mat_a]
  rfl

theorem fi22Hom_b : toMat 77 (unlane 77 LB) = fi22Hom b := by
  rw [← matB_eq, ← mat_b]
  rfl

theorem fi22_heisCfg_exists :
    ∃ (x y : Fin 3 → CFSG.Blueprint.NativeSporadic.Fi22) (z : CFSG.Blueprint.NativeSporadic.Fi22),
      HeisCfg 3 3 x y z ∧ ∀ i, y i ^ 3 = 1 :=
  fi22_heis_of_seeds fi22Hom_injective fi22Hom_a fi22Hom_b
    (fi22EquivJ.symm : J →* CFSG.Blueprint.NativeSporadic.Fi22) fi22EquivJ.symm.injective

theorem fi22_coverData_exists :
    ∃ p₀ p₁ p₂ q₀ q₁ q₂ z dA dB n : CFSG.Blueprint.NativeSporadic.Fi22,
      Fi22CoverData p₀ p₁ p₂ q₀ q₁ q₂ z dA dB n :=
  fi22_cover_of_seeds fi22Hom_injective fi22Hom_a fi22Hom_b
    (fi22EquivJ.symm : J →* CFSG.Blueprint.NativeSporadic.Fi22) fi22EquivJ.symm.injective

end Concrete

end CertificateChecks.KernelSlpRel

end
