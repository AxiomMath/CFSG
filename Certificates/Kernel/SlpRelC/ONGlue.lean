module

public import Certificates.Kernel.SlpRelC.ON
public import CFSG.Certificates.Kernel.SlpRelSound
public import Certificates.Kernel.Sporadic.ONC.TauGlue
public import CFSG.HardMathSupport.Meierfrankenfeld.FFToolkit.HeisLift
import Certificates.Kernel.Sporadic.ONC.ChainBase

public section

namespace CertificateChecks.KernelSlpRel

open CFSG.KC.Enum CFSG.KS CFSG.KS.ON CFSG.KS.Ord CFSG.KS.SlpRel CFSG.KS.ONC CFSG.Sporadic.ON
open CFSG.HardMathSupport.Cooperstein.Coordinator.FFSporadic
open CFSG.HardMathSupport.Meierfrankenfeld.FFToolkit
open CertificateChecks.KernelSpor
open CertificateChecks.KernelSpor.ONC (matJ matJ_injective FA FB colA colB)

theorem heisCfg_seven_one' {G : Type*} [Group G] {x y z : G} (hx : x ^ 7 = 1)
    (hz : z ^ 7 = 1) (hzx : x * z = z * x) (hzy : y * z = z * y) (hyx : x * y = y * (x * z))
    (hz1 : z ≠ 1) : HeisCfg 7 1 (fun _ => x) (fun _ => y) z where
  xp _ := hx
  zp := hz
  zx _ := hzx
  zy _ := hzy
  yx _ := by
    rw [mul_assoc, hyx]
    group
  xx _ _ := rfl
  yy i j hij := absurd (Subsingleton.elim (α := Fin 1) i j) hij
  xy i j hij := absurd (Subsingleton.elim (α := Fin 1) i j) hij
  z1 := hz1

theorem pow_seven_of_word' {G : Type*} [Monoid G] {g : G}
    (h : g * (g * (g * (g * (g * (g * g))))) = 1) : g ^ 7 = 1 := by
  rw [← h]
  simp only [pow_succ, pow_zero, one_mul, mul_assoc]

theorem on_cfg_of_rels {G : Type*} [Group G] (r : ℕ → G)
    (hr : ∀ p ∈ onRelsK, (p.1.map r).prod = (p.2.map r).prod) (hz : r onHeisZ ≠ 1) :
    ∃ x y z g : G, HeisCfg 7 1 (fun _ => x) (fun _ => y) z ∧ y ^ 7 = 1 ∧ g * z * g⁻¹ = z⁻¹ := by
  simp only [onRelsK, List.forall_mem_cons, List.map_cons, List.map_nil, List.prod_cons,
    List.prod_nil, mul_one] at hr
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, -⟩ := hr
  have hz7 : r onHeisZ ^ 7 = 1 := pow_seven_of_word' h3
  refine ⟨r onHeisX, r onHeisY, r onHeisZ, r onHeisG,
    heisCfg_seven_one' (pow_seven_of_word' h1) hz7 h4 h5 h6 hz, pow_seven_of_word' h2, ?_⟩
  have hz6 : r onHeisZ * (r onHeisZ * (r onHeisZ * (r onHeisZ * (r onHeisZ * r onHeisZ)))) =
      (r onHeisZ)⁻¹ := by
    rw [eq_inv_iff_mul_eq_one, ← hz7]
    simp only [pow_succ, pow_zero, one_mul, mul_assoc]
  rw [hz6] at h7
  calc r onHeisG * r onHeisZ * (r onHeisG)⁻¹
      = (r onHeisG * (r onHeisZ)⁻¹ * (r onHeisG)⁻¹)⁻¹ := by group
    _ = (r onHeisZ * r onHeisG * (r onHeisG)⁻¹)⁻¹ := by rw [h7]
    _ = (r onHeisZ)⁻¹ := by group

theorem on_cfg_map {G H : Type*} [Group G] [Group H] (f : G →* H) (hf : Function.Injective f)
    (h : ∃ x y z g : G, HeisCfg 7 1 (fun _ => x) (fun _ => y) z ∧ y ^ 7 = 1 ∧ g * z * g⁻¹ = z⁻¹) :
    ∃ x y z g : H, HeisCfg 7 1 (fun _ => x) (fun _ => y) z ∧ y ^ 7 = 1 ∧ g * z * g⁻¹ = z⁻¹ := by
  obtain ⟨x, y, z, g, hc, hy, hg⟩ := h
  have hz : f z ≠ 1 := fun h1 => hc.z1 (hf (by rw [map_one]; exact h1))
  refine ⟨f x, f y, f z, f g, hc.map f hz, by rw [← map_pow, hy, map_one], ?_⟩
  rw [← map_inv, ← map_mul, ← map_mul, hg, map_inv]

theorem onSlpK_conj {mul : Nat → Nat → Nat → Nat → Nat → Nat → Nat}
    {bat : Nat → Nat → (Nat → Nat) → Nat → Nat → Nat} {cs₀ ds₀ L₀ H₀ cm₀ rm₀ one₀ : Nat}
    {nz : Nat → Bool} {FA FB : Nat → Nat} {prog : List (List Nat)}
    {ps : List (List Nat × List Nat)} {ne : List Nat}
    (h : (strictB cs₀ fun cs => strictB ds₀ fun ds => strictB L₀ fun L => strictB H₀ fun H =>
      strictB cm₀ fun cm => strictB rm₀ fun rm => strictB one₀ fun one =>
      strictB (bat cs ds FA (nat_lit 0) (nat_lit 154)) fun a =>
      strictB (bat cs ds FB (nat_lit 0) (nat_lit 154)) fun b =>
        CFSG.KC.SlpRel.slpRelK strictB (mul L H cm rm) one Nat.beq nz [a, b] prog ps ne) = true) :
    CFSG.KC.SlpRel.slpRelK strictB (mul L₀ H₀ cm₀ rm₀) one₀ Nat.beq nz
      [bat cs₀ ds₀ FA (nat_lit 0) (nat_lit 154), bat cs₀ ds₀ FB (nat_lit 0) (nat_lit 154)]
      prog ps ne = true := by
  simp only [strictB_eq] at h
  exact h

theorem on_hFA : ∀ c < 154, PV (FA c) := fun c hc =>
  pv_of_canon (CertificateChecks.KernelSpor.ON.canon_of CertificateChecks.KernelSpor.ON2.colsAK2
    (CertificateChecks.KernelSpor.ON.list_eq ONW.LA ONW.CA
      (CFSG.KS.allN_spec CertificateChecks.KernelSpor.ON2.listA2)) c hc)

theorem on_hFB : ∀ c < 154, PV (FB c) := fun c hc =>
  pv_of_canon (CertificateChecks.KernelSpor.ON.canon_of CertificateChecks.KernelSpor.ON2.colsBK2
    (CertificateChecks.KernelSpor.ON.list_eq ONW.LB ONW.CB
      (CFSG.KS.allN_spec CertificateChecks.KernelSpor.ON2.listB2)) c hc)

theorem onRepL_two {α : Type} {G : Type*} [Monoid G] {Rep : α → G → Prop} {one x y : α}
    {g h : G} (hx : Rep x g) (hy : Rep y h) (h1 : Rep one 1) : RepL Rep one [x, y] [g, h] := by
  refine ⟨rfl, fun i => ?_⟩
  match i with
  | 0 => exact hx
  | 1 => exact hy
  | i + 2 => exact h1

section Generic

variable {G : Type*} [Group G] {φ : G →* Matrix (Fin 154) (Fin 154) (ZMod 3)}

theorem onNZ_spec {X : Nat} {g : G} (hX : Reps φ X g) (h : onNZ X = true) : g ≠ 1 := by
  rintro rfl
  have hm := congrFun (congrFun hX.2 0) 0
  rw [map_one, Matrix.one_apply_eq] at hm
  have hl := hX.1.2 0 (by norm_num)
  have e1 : omat X 0 0 = ((X % 2048 : ℕ) : ZMod 3) := by
    unfold omat ordMat
    simp
  have e2 : lane 11 X 0 = X % 2048 := by
    unfold lane
    simp
  rw [e1] at hm
  rw [e2] at hl
  have hne : X % 2048 ≠ 1 := by
    change Bool.not (Nat.beq (X % 2048) 1) = true at h
    cases hb : Nat.beq (X % 2048) 1
    · exact Nat.ne_of_beq_eq_false hb
    · rw [hb] at h
      exact absurd h (by decide)
  have h02 : X % 2048 = 0 ∨ X % 2048 = 2 := by omega
  rcases h02 with e | e <;> rw [e] at hm <;> exact absurd hm (by decide)

theorem on_exists_of_seeds {H : Type*} [Group H] (hφ : Function.Injective φ) {gA gB : G}
    (hAc : ∀ r c : Fin 154, φ gA r c = vecK (FA c.val) r)
    (hBc : ∀ r c : Fin 154, φ gB r c = vecK (FB c.val) r) (f : G →* H)
    (hf : Function.Injective f) :
    ∃ x y z g : H, HeisCfg 7 1 (fun _ => x) (fun _ => y) z ∧ y ^ 7 = 1 ∧ g * z * g⁻¹ = z⁻¹ := by
  have h := ch129009_ok
  unfold onSlpK at h
  have hc := onSlpK_conj (mul := mul3) (bat := batK) (cs₀ := CS) (ds₀ := DS) (L₀ := LL)
    (H₀ := HH) (cm₀ := CM) (rm₀ := RM) (one₀ := ONE) (nz := onNZ) (FA := FA) (FB := FB) h
  have hinit := onRepL_two (batK_reps (φ := φ) on_hFA hAc) (batK_reps (φ := φ) on_hFB hBc)
    (reps_one (φ := φ))
  have hs := slpRelK_sound (Rep := Reps φ) (frc := strictB) (mul := mul3 LL HH CM RM) (one := ONE)
    (eq := Nat.beq) (nz := onNZ) (init := [batK CS DS FA 0 154, batK CS DS FB 0 154])
    (gens := [gA, gB]) (fun _ _ _ _ hX hY => reps_mul hX hY) reps_one strictB_eq
    (fun _ _ _ _ hX hY e => hφ (by rw [← hX.2, ← hY.2, Nat.eq_of_beq_eq_true e]))
    (fun _ _ hX hz => onNZ_spec hX hz) hinit hc
  exact on_cfg_map f hf (on_cfg_of_rels _ hs.1 (hs.2 _ List.mem_cons_self))

end Generic

theorem on_heisCfg_exists :
    ∃ x y z g : CFSG.Blueprint.NativeSporadic.ON,
      HeisCfg 7 1 (fun _ => x) (fun _ => y) z ∧ y ^ 7 = 1 ∧ g * z * g⁻¹ = z⁻¹ :=
  on_exists_of_seeds matJ_injective (fun r c => colA r c) (fun r c => colB r c)
    (onEquivJ.symm : J →* CFSG.Blueprint.NativeSporadic.ON) onEquivJ.symm.injective

end CertificateChecks.KernelSlpRel

end
