module

public import Certificates.Kernel.SlpRelC.Fi23
public import CFSG.Certificates.Kernel.SlpRelSound
public import Certificates.Kernel.Fi23M.Facts
public import CFSG.HardMathSupport.Meierfrankenfeld.FFToolkit.HeisLift
public import CFSG.Sporadic.Fi23.Setup
public import Certificates.Kernel.Fi23M.Keys
public import CFSG.Assembly.OrderReductions.InvertedSubgroup
public import CFSG.Assembly.OrderReductions.OddInversion
public import CFSG.LocalAnalysis.AGLEmbedding.CaseThreeFamilies
public import CFSG.LocalAnalysis.AGLEmbedding.OneSmallGEVL34FFDefs
public import CFSG.LocalAnalysis.AGLEmbedding.ResidualTools
public import CFSG.LocalAnalysis.ComponentClassification.LBalanceComponentLifts
public import CFSG.LocalAnalysis.ComponentInitial.CommutingBlock
public import CFSG.LocalAnalysis.SectionRank.Framework.SylowRank
public import CFSG.Quasithin.Background.B15P4LayerDict
public import CFSG.Quasithin.Background.B1MoreNineG
public import CFSG.Sporadic.M23.M23Group
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFchapter1section1.proposition_4_c
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Proposition82

public section

namespace CertificateChecks.KernelSlpRel

open CFSG.KC.Enum CFSG.KS.SlpRel CFSG.KS.Mat3 CFSG.KD.Fi23M CFSG.Sporadic.Fi23
open CFSG.HardMathSupport.Cooperstein.Coordinator.FFSporadic
open CFSG.HardMathSupport.Meierfrankenfeld.FFToolkit

theorem pow_three_of_word' {G : Type*} [Monoid G] {g : G} (h : g * (g * g) = 1) :
    g ^ 3 = 1 := by
  rw [← h]
  simp only [pow_succ, pow_zero, one_mul, mul_assoc]

theorem mem_fiRelsK_I {i : ℕ} (hi : i < 4) {q : List ℕ × List ℕ} (hq : q ∈ fiRelsI i) :
    q ∈ fiRelsK := by
  simp only [fiRelsK, List.mem_append, List.mem_flatMap, List.mem_range]
  exact Or.inl ⟨i, hi, Or.inl hq⟩

theorem mem_fiRelsK_IJ {i j : ℕ} (hi : i < 4) (hj : j < 4) {q : List ℕ × List ℕ}
    (hq : q ∈ fiRelsIJ i j) : q ∈ fiRelsK := by
  simp only [fiRelsK, List.mem_append, List.mem_flatMap, List.mem_range]
  exact Or.inl ⟨i, hi, Or.inr ⟨j, hj, hq⟩⟩

theorem fi23_cfg_of_rels {G : Type*} [Group G] (r : ℕ → G)
    (hr : ∀ p ∈ fiRelsK, (p.1.map r).prod = (p.2.map r).prod) (hz : r fiHeisZ ≠ 1) :
    HeisCfg 3 4 (fun i : Fin 4 => r (fiHeisX i)) (fun i : Fin 4 => r (fiHeisY i)) (r fiHeisZ) ∧
      ∀ i : Fin 4, r (fiHeisY i) ^ 3 = 1 := by
  have hI : ∀ i : Fin 4, ∀ {u v : List ℕ}, (u, v) ∈ fiRelsI i →
      (u.map r).prod = (v.map r).prod := fun i _ _ hq => hr _ (mem_fiRelsK_I i.isLt hq)
  have hIJ : ∀ i j : Fin 4, ∀ {u v : List ℕ}, (u, v) ∈ fiRelsIJ i j →
      (u.map r).prod = (v.map r).prod := fun i j _ _ hq =>
    hr _ (mem_fiRelsK_IJ i.isLt j.isLt hq)
  have hz3 := hr ([fiHeisZ, fiHeisZ, fiHeisZ], []) (by
    simp only [fiRelsK, List.mem_append, List.mem_singleton, or_true])
  simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one] at hz3
  have hyp : ∀ i : Fin 4, r (fiHeisY i) ^ 3 = 1 := fun i => by
    have := hI i (u := [fiHeisY i, fiHeisY i, fiHeisY i]) (v := []) (by simp [fiRelsI])
    simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one] at this
    exact pow_three_of_word' this
  refine ⟨⟨fun i => ?_, pow_three_of_word' hz3, fun i => ?_, fun i => ?_, fun i => ?_,
    fun i j => ?_, fun i j hij => ?_, fun i j hij => ?_, hz⟩, hyp⟩
  · have := hI i (u := [fiHeisX i, fiHeisX i, fiHeisX i]) (v := []) (by simp [fiRelsI])
    simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one] at this
    exact pow_three_of_word' this
  · have := hI i (u := [fiHeisX i, fiHeisZ]) (v := [fiHeisZ, fiHeisX i]) (by simp [fiRelsI])
    simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one] at this
    exact this
  · have := hI i (u := [fiHeisY i, fiHeisZ]) (v := [fiHeisZ, fiHeisY i]) (by simp [fiRelsI])
    simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one] at this
    exact this
  · have h1 := hI i (u := [fiHeisX i, fiHeisY i]) (v := [fiHeisY i, fiHeisX i, fiHeisZ])
      (by simp [fiRelsI])
    simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one] at h1
    calc (r (fiHeisY i))⁻¹ * r (fiHeisX i) * r (fiHeisY i)
        = (r (fiHeisY i))⁻¹ * (r (fiHeisX i) * r (fiHeisY i)) := by rw [mul_assoc]
      _ = (r (fiHeisY i))⁻¹ * (r (fiHeisY i) * (r (fiHeisX i) * r fiHeisZ)) := by rw [h1]
      _ = r (fiHeisX i) * r fiHeisZ := inv_mul_cancel_left _ _
  · have := hIJ i j (u := [fiHeisX i, fiHeisX j]) (v := [fiHeisX j, fiHeisX i]) (by simp [fiRelsIJ])
    simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one] at this
    exact this
  · have hij' : (i : ℕ) ≠ j := fun e => hij (Fin.ext e)
    have := hIJ i j (u := [fiHeisY i, fiHeisY j]) (v := [fiHeisY j, fiHeisY i])
      (by simp [fiRelsIJ, hij'])
    simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one] at this
    exact this
  · have hij' : (i : ℕ) ≠ j := fun e => hij (Fin.ext e)
    have := hIJ i j (u := [fiHeisX i, fiHeisY j]) (v := [fiHeisY j, fiHeisX i])
      (by simp [fiRelsIJ, hij'])
    simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one] at this
    exact this

theorem fi23_cfg_exists_of_rels {G H : Type*} [Group G] [Group H] (f : G →* H)
    (hf : Function.Injective f) (r : ℕ → G)
    (hr : ∀ p ∈ fiRelsK, (p.1.map r).prod = (p.2.map r).prod) (hz : r fiHeisZ ≠ 1) :
    ∃ (x y : Fin 4 → H) (z : H), HeisCfg 3 4 x y z ∧ ∀ i, y i ^ 3 = 1 := by
  obtain ⟨hc, hy⟩ := fi23_cfg_of_rels r hr hz
  have hfz : f (r fiHeisZ) ≠ 1 := fun h1 => hc.z1 (hf (by rw [map_one]; exact h1))
  exact ⟨_, _, _, hc.map f hfz, fun i => by rw [← map_pow, hy i, map_one]⟩

theorem fi23RepL_two {α : Type} {G : Type*} [Monoid G] {Rep : α → G → Prop} {one x y : α}
    {g h : G} (hx : Rep x g) (hy : Rep y h) (h1 : Rep one 1) : RepL Rep one [x, y] [g, h] := by
  refine ⟨rfl, fun i => ?_⟩
  match i with
  | 0 => exact hx
  | 1 => exact hy
  | i + 2 => exact h1

theorem fiSlpK_conj {m3 : Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat} {mt : Nat → Nat}
    {lo₀ ci₀ rm₀ one₀ : Nat} {nz : Nat → Bool} {prog : List (List Nat)}
    {ps : List (List Nat × List Nat)} {ne : List Nat}
    (h : (strictB lo₀ fun lo => strictB ci₀ fun ci => strictB rm₀ fun rm => strictB one₀ fun one =>
      strictB (mt (nat_lit 0)) fun a => strictB (mt (nat_lit 1)) fun b =>
        CFSG.KC.SlpRel.slpRelK strictB (m3 (nat_lit 253) (nat_lit 64009) lo ci rm) one Nat.beq nz
          [a, b] prog ps ne) = true) :
    CFSG.KC.SlpRel.slpRelK strictB (m3 (nat_lit 253) (nat_lit 64009) lo₀ ci₀ rm₀) one₀ Nat.beq nz
      [mt (nat_lit 0), mt (nat_lit 1)] prog ps ne = true := by
  simp only [strictB_eq] at h
  exact h

section Model

variable {G : Type*} [Group G] (φ : G →* Matrix (Fin 253) (Fin 253) (ZMod 3))

@[expose] def Fi23Rep (X : Nat) (g : G) : Prop := Canon3 64009 X ∧ mat3 253 64009 X = φ g

variable {φ}

theorem fi23Rep_mul {X Y : Nat} {g h : G} (hX : Fi23Rep φ X g) (hY : Fi23Rep φ Y h) :
    Fi23Rep φ (CFSG.KC.Ord.mul3s (nat_lit 253) (nat_lit 64009) LO CI RM X Y) (g * h) := by
  obtain ⟨c, e⟩ := CertificateChecks.KernelFi23M.hs.mul_sound X Y hX.1 hY.1
  refine ⟨c, ?_⟩
  rw [MUL] at e
  rw [e, hX.2, hY.2, map_mul] <;> rfl

theorem fi23Rep_one : Fi23Rep φ ONE 1 := by
  refine ⟨CertificateChecks.KernelFi23M.hs.one_q, ?_⟩
  rw [CertificateChecks.KernelFi23M.hs.one_mt, map_one] <;> rfl

theorem fiNZ_spec {X : Nat} {g : G} (hX : Fi23Rep φ X g) (h : fiNZ X = true) : g ≠ 1 := by
  rintro rfl
  have hm := congrFun (congrFun hX.2 0) 0
  rw [map_one, Matrix.one_apply_eq] at hm
  have hp : X % 2 = 0 := by
    have e := Nat.eq_of_beq_eq_true h
    rw [← Nat.and_one_is_mod]
    exact e
  have hb : X.testBit 0 = false := by simp [Nat.testBit_zero, hp]
  unfold mat3 bv at hm
  simp only [Fin.val_zero, Nat.mul_zero, Nat.add_zero, hb] at hm
  by_cases hm' : X.testBit 64009
  · rw [if_neg (by simp), if_pos hm'] at hm
    exact absurd hm (by decide)
  · rw [if_neg (by simp), if_neg hm'] at hm
    exact absurd hm (by decide)

theorem fi23_hinit {gA gB : G} (hA : mat3 253 64009 (RB 1) = φ gA)
    (hB : mat3 253 64009 (RB 2) = φ gB) : RepL (Fi23Rep φ) ONE [MT 0, MT 1] [gA, gB] := by
  have e1 : RB 1 = MT 0 := by
    unfold RB
    rw [List.getD_cons_succ, List.getD_cons_zero]
  have e2 : RB 2 = MT 1 := by
    unfold RB
    rw [List.getD_cons_succ, List.getD_cons_succ, List.getD_cons_zero]
  have hA' : Fi23Rep φ (MT 0) gA := by
    rw [← e1]
    exact ⟨CertificateChecks.KernelFi23M.canon_RB1, hA⟩
  have hB' : Fi23Rep φ (MT 1) gB := by
    rw [← e2]
    exact ⟨CertificateChecks.KernelFi23M.canon_RB2, hB⟩
  exact fi23RepL_two hA' hB' fi23Rep_one

theorem fi23_heis_of_seeds {H : Type*} [Group H] (hφ : Function.Injective φ) {gA gB : G}
    (hA : mat3 253 64009 (RB 1) = φ gA) (hB : mat3 253 64009 (RB 2) = φ gB) (f : G →* H)
    (hf : Function.Injective f) :
    ∃ (x y : Fin 4 → H) (z : H), HeisCfg 3 4 x y z ∧ ∀ i, y i ^ 3 = 1 := by
  have h := ch129030_ok
  unfold fiSlpK at h
  have hc := fiSlpK_conj (m3 := CFSG.KC.Ord.mul3s) (mt := MT) (lo₀ := LO) (ci₀ := CI) (rm₀ := RM)
    (one₀ := ONE) (nz := fiNZ) h
  have hs := slpRelK_sound (Rep := Fi23Rep φ) (frc := strictB)
    (mul := CFSG.KC.Ord.mul3s (nat_lit 253) (nat_lit 64009) LO CI RM) (one := ONE) (eq := Nat.beq)
    (nz := fiNZ) (init := [MT 0, MT 1]) (gens := [gA, gB])
    (fun _ _ _ _ hX hY => fi23Rep_mul hX hY) fi23Rep_one strictB_eq
    (fun _ _ _ _ hX hY e => hφ (by rw [← hX.2, ← hY.2, Nat.eq_of_beq_eq_true e]))
    (fun _ _ hX hz => fiNZ_spec hX hz) (fi23_hinit hA hB) hc
  exact fi23_cfg_exists_of_rels f hf _ hs.1 (hs.2 _ List.mem_cons_self)

end Model

section Concrete


@[expose] noncomputable def fi23Hom : J →* Matrix (Fin 253) (Fin 253) (ZMod 3) :=
  (Units.coeHom _).comp J.subtype

theorem fi23Hom_injective : Function.Injective fi23Hom :=
  fun _ _ e => Subtype.ext (Units.ext e)

theorem fi23Hom_a : mat3 253 64009 (RB 1) = fi23Hom a := by
  rw [← CertificateChecks.KernelFi23M.mA_eq, ← mat_a]
  rfl

theorem fi23Hom_b : mat3 253 64009 (RB 2) = fi23Hom b := by
  rw [← CertificateChecks.KernelFi23M.mB_eq, ← mat_b]
  rfl

theorem fi23_heisCfg_exists :
    ∃ (x y : Fin 4 → CFSG.Blueprint.NativeSporadic.Fi23) (z : CFSG.Blueprint.NativeSporadic.Fi23),
      HeisCfg 3 4 x y z ∧ ∀ i, y i ^ 3 = 1 :=
  fi23_heis_of_seeds fi23Hom_injective fi23Hom_a fi23Hom_b
    (fi23EquivJ.symm : J →* CFSG.Blueprint.NativeSporadic.Fi23) fi23EquivJ.symm.injective

end Concrete

end CertificateChecks.KernelSlpRel

end
