module

public import Certificates.Kernel.Fi23Q.SubClsGlue
import Certificates.Kernel.Fi23Q.SubClsChk
import Mathlib
public import Certificates.Kernel.SporSch.Co2M.ThirdBound
public import CFSG.Certificates.Kernel.Fi23Q.SubClsSound
public import CFSG.LocalAnalysis.ComponentClassification.PSL3FourInvolutions
public import CFSG.Sporadic.Co2Schreier.ThirdE

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelFi23Q

attribute [local irreducible] sE

open CFSG.Sporadic.Fi23 CFSG.KC.Fi23K CFSG.KC.Fi23Q CFSG.KC.Pc3 CFSG.KS.Pc3 CFSG.KS.Fi23Q
  CFSG.Perm CFSG.KD.Fi23K
open CFSG.Sporadic.Th hiding J a b closure_ab gA gB rows_B_cube

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

noncomputable def inv4 (c : ℕ) : ℕ := dg c 0 + 3 * dg c 1 + 9 * dg c 2 + 27 * dg c 3

noncomputable def inv5 (c : ℕ) : ℕ := dg c 0 + 3 * dg c 1 + 9 * dg c 2 + 27 * dg c 3 + 81 * dg c 4

theorem inv4_ok : ∀ c < 256, (∀ k < 4, dg c k < 3) → inv4 c < 81 ∧ vec3 4 (inv4 c) = c := by
  decide +kernel

theorem inv5_ok : ∀ c < 1024, (∀ k < 5, dg c k < 3) → inv5 c < 243 ∧ vec3 5 (inv5 c) = c := by
  decide +kernel

theorem vec3_vecOK : ∀ i < 81, vecOK 9 (vec3 4 i) = true := by decide +kernel

theorem ok4_vec3 {a : ℕ} (ha : Ok4 a) : ∃ i < 81, vec3 4 i = a := by
  have := inv4_ok a (by have := ha.1; norm_num at this; omega) ha.2
  exact ⟨_, this.1, this.2⟩

theorem ok5_vec3 {w : ℕ} (hw : Ok5 w) : ∃ i < 243, vec3 5 i = w := by
  have := inv5_ok w (by have := hw.1; norm_num at this; omega) hw.2
  exact ⟨_, this.1, this.2⟩

@[expose] noncomputable def foldC (col : ℕ → ℕ) (w n : ℕ) : ℕ :=
  Nat.rec (motive := fun _ => ℕ) 0 (fun c acc => add3 acc (smul3 (dg w c) (col c))) n

theorem foldC_zero (col : ℕ → ℕ) (w : ℕ) : foldC col w 0 = 0 := rfl

theorem foldC_succ (col : ℕ → ℕ) (w n : ℕ) :
    foldC col w (n + 1) = add3 (foldC col w n) (smul3 (dg w n) (col n)) := rfl

theorem mE_eq (CJ k w : ℕ) : mE CJ k w = foldC (colE CJ k) w 5 := rfl

theorem mC_eq (Mt a w : ℕ) : mC Mt a w = foldC (colM Mt a) w 5 := rfl

theorem mT_eq (CJ a w : ℕ) : mT CJ a w = rep (dg a 3) (mE CJ 3) (rep (dg a 2) (mE CJ 2)
    (rep (dg a 1) (mE CJ 1) (rep (dg a 0) (mE CJ 0) w))) := rfl

theorem muT_eq (R a b : ℕ) : muT R a b = rep (dg b 3) (fun y => rT R y 3)
    (rep (dg b 2) (fun y => rT R y 2) (rep (dg b 1) (fun y => rT R y 1)
      (rep (dg b 0) (fun y => rT R y 0) a))) := rfl

theorem rep_zero (g : ℕ → ℕ) (s : ℕ) : rep 0 g s = s := rfl

theorem rep_one (g : ℕ → ℕ) (s : ℕ) : rep 1 g s = g s := by
  unfold rep
  rw [CFSG.KS.PK.strictN_eq]
  rfl

theorem rep_two (g : ℕ → ℕ) (s : ℕ) : rep 2 g s = g (g s) := by
  unfold rep
  rw [CFSG.KS.PK.strictN_eq]
  rfl

theorem muT_zero (R a : ℕ) : muT R a 0 = a := rfl

section GenE

variable {G : Type*} [Group G]

structure EAlg (x : ℕ → G) (CJ : ℕ) : Prop where
  comm : ∀ i < 5, ∀ j < 5, Commute (x (4 + i)) (x (4 + j))
  cube : ∀ i < 5, x (4 + i) ^ 3 = 1
  ok : ∀ k < 4, ∀ c < 5, Ok5 (colE CJ k c)
  conj : ∀ k < 4, ∀ c < 5, (x k)⁻¹ * x (4 + c) * x k = epsG x (colE CJ k c)

theorem eAlg_of {x : ℕ → G}
    (hP : PcRel x 9 CFSG.KD.Fi23Q.SubPW CFSG.KD.Fi23Q.SubCJ) : EAlg x CFSG.KD.Fi23Q.SubCJ := by
  have hE := clsEK_sound CFSG.KD.Fi23Q.clsE_ok
  have hcomm : ∀ i j, 4 ≤ i → i < j → j < 9 → x j * x i = x i * x j := by
    intro i j hi hij hj
    have h := hP.conj i j hij hj
    rw [hE.1 i j hi hij hj, nv_unit9 x hj] at h
    calc x j * x i = x i * ((x i)⁻¹ * x j * x i) := by group
      _ = x i * x j := by rw [h]
  refine ⟨fun i hi j hj => ?_, fun i hi => ?_, fun k hk c hc => ?_, fun k hk c hc => ?_⟩
  · rcases lt_trichotomy i j with h | rfl | h
    · exact (hcomm _ _ (by omega) (by omega) (by omega)).symm
    · exact Commute.refl _
    · exact hcomm _ _ (by omega) (by omega) (by omega)
  · rw [hP.cube (4 + i) (by omega)]
    change nv x 9 (f32 0 (4 + i)) = 1
    rw [f32_zero, nv_zero9]
  · have h9 := ok9_of_vecOK (cj_vec (i := k) (j := 4 + c) (by omega) (by omega))
    rw [colE_eq]
    refine ⟨?_, fun d hd => ?_⟩
    · rw [shr8_eq]
      have := h9.1
      norm_num at *
      omega
    · rw [dg_shr8]
      exact h9.2 _ (by omega)
  · have hl := hE.2 k hk (4 + c) (by omega) (by omega)
    rw [colE_eq, hP.conj k (4 + c) (by omega) (by omega), nvG_split, hl, tauG_zero, one_mul]

variable {x : ℕ → G} {CJ : ℕ}

theorem epsG_add' (h : EAlg x CJ) {u v : ℕ} (hu : Ok5 u) (hv : Ok5 v) :
    epsG x (add3 u v) = epsG x u * epsG x v := epsG_add x h.comm h.cube hu.2 hv.2

theorem epsG_neg (h : EAlg x CJ) {u : ℕ} (hu : Ok5 u) : epsG x (neg3 u) = (epsG x u)⁻¹ := by
  apply eq_inv_of_mul_eq_one_left
  rw [← epsG_add' h (ok5_neg3 hu) hu, ← epsG_zero x]
  refine epsG_congr x fun c hc => ?_
  rw [dg_add3 hc ((ok5_neg3 hu).2 c hc) (hu.2 c hc), dg_neg3 hc (hu.2 c hc), dg_eq 0]
  simp
  omega

theorem epsG_cube (h : EAlg x CJ) {u : ℕ} (hu : Ok5 u) : epsG x u ^ 3 = 1 := by
  have e : epsG x u ^ 3 = epsG x (add3 (add3 u u) u) := by
    rw [epsG_add' h (ok5_add3 hu hu) hu, epsG_add' h hu hu, pow_succ, pow_two]
  rw [e, ← epsG_zero x]
  refine epsG_congr x fun c hc => ?_
  rw [dg_add3 hc ((ok5_add3 hu hu).2 c hc) (hu.2 c hc), dg_add3 hc (hu.2 c hc) (hu.2 c hc),
    dg_eq 0]
  simp
  omega

theorem epsG_smul (h : EAlg x CJ) {e u : ℕ} (he : e < 3) (hu : Ok5 u) :
    epsG x (smul3 e u) = epsG x u ^ e := by
  unfold smul3
  simp only [CFSG.KS.PK.nIf_eq]
  interval_cases e
  · simp [epsG_zero]
  · simp
  · have e1 : Nat.beq 2 0 = false := rfl
    have e2 : Nat.beq 2 1 = false := rfl
    simp only [e1, e2, Bool.false_eq_true, ↓reduceIte]
    rw [epsG_neg h hu]
    have h3 := epsG_cube h hu
    rw [eq_comm, ← mul_left_cancel_iff (a := epsG x u), ← pow_succ', h3, mul_inv_cancel]

theorem epsG_comm (h : EAlg x CJ) {u v : ℕ} (hu : Ok5 u) (hv : Ok5 v) :
    epsG x u * epsG x v = epsG x v * epsG x u := by
  rw [← epsG_add' h hu hv, ← epsG_add' h hv hu]
  refine epsG_congr x fun c hc => ?_
  rw [dg_add3 hc (hu.2 c hc) (hv.2 c hc), dg_add3 hc (hv.2 c hc) (hu.2 c hc), Nat.add_comm]

theorem fold_eps (h : EAlg x CJ) (col : ℕ → ℕ) (hcol : ∀ c < 5, Ok5 (col c)) {w : ℕ}
    (hw : ∀ c < 5, dg w c < 3) : ∀ n ≤ 5, Ok5 (foldC col w n) ∧
      epsG x (foldC col w n) = ((List.range n).map fun c => epsG x (col c) ^ dg w c).prod
  | 0, _ => ⟨ok5_zero, by rw [foldC_zero, epsG_zero]; rfl⟩
  | n + 1, hn => by
    obtain ⟨ih1, ih2⟩ := fold_eps h col hcol hw n (by omega)
    have hs := ok5_smul3 (e := dg w n) (hcol n (by omega))
    rw [foldC_succ]
    refine ⟨ok5_add3 ih1 hs, ?_⟩
    rw [epsG_add' h ih1 hs, ih2, epsG_smul h (hw n (by omega)) (hcol n (by omega)),
      List.range_succ, List.map_append, List.prod_append]
    simp

theorem conj_epsG (g : G) (w : ℕ) :
    g⁻¹ * epsG x w * g = ((List.range 5).map fun c => (g⁻¹ * x (4 + c) * g) ^ dg w c).prod := by
  unfold epsG
  rw [conj_prod, List.map_map]
  apply congrArg
  apply List.map_congr_left
  intro c _
  simp only [Function.comp_apply]
  rw [conj_pow']

theorem conj_sk (h : EAlg x CJ) {k w : ℕ} (hk : k < 4) (hw : Ok5 w) :
    Ok5 (mE CJ k w) ∧ (x k)⁻¹ * epsG x w * x k = epsG x (mE CJ k w) := by
  obtain ⟨h1, h2⟩ := fold_eps h (colE CJ k) (fun c hc => h.ok k hk c hc) hw.2 5 le_rfl
  rw [mE_eq]
  refine ⟨h1, ?_⟩
  rw [h2, conj_epsG]
  apply congrArg
  apply List.map_congr_left
  intro c hc
  rw [h.conj k hk c (List.mem_range.1 hc)]

theorem conj_rep (h : EAlg x CJ) {k e w : ℕ} (hk : k < 4) (he : e < 3) (hw : Ok5 w) :
    Ok5 (rep e (mE CJ k) w) ∧
      (x k ^ e)⁻¹ * epsG x w * x k ^ e = epsG x (rep e (mE CJ k) w) := by
  interval_cases e
  · rw [rep_zero]
    exact ⟨hw, by group⟩
  · rw [rep_one, pow_one]
    exact conj_sk h hk hw
  · rw [rep_two]
    obtain ⟨a1, a2⟩ := conj_sk h hk hw
    obtain ⟨b1, b2⟩ := conj_sk h hk a1
    refine ⟨b1, ?_⟩
    rw [← b2, ← a2, pow_two, mul_inv_rev]
    simp only [mul_assoc]

theorem conj_tau (h : EAlg x CJ) {a w : ℕ} (ha : ∀ k < 4, dg a k < 3) (hw : Ok5 w) :
    Ok5 (mT CJ a w) ∧ (tauG x a)⁻¹ * epsG x w * tauG x a = epsG x (mT CJ a w) := by
  obtain ⟨o0, e0⟩ := conj_rep h (k := 0) (by omega) (ha 0 (by omega)) hw
  obtain ⟨o1, e1⟩ := conj_rep h (k := 1) (by omega) (ha 1 (by omega)) o0
  obtain ⟨o2, e2⟩ := conj_rep h (k := 2) (by omega) (ha 2 (by omega)) o1
  obtain ⟨o3, e3⟩ := conj_rep h (k := 3) (by omega) (ha 3 (by omega)) o2
  rw [mT_eq]
  refine ⟨o3, ?_⟩
  rw [← e3, ← e2, ← e1, ← e0, tauG_eq]
  group

theorem conj_mC_gen (h : EAlg x CJ) {Mt a w : ℕ} (ha : ∀ k < 4, dg a k < 3)
    (hM : ∀ c < 5, colM Mt a c = mT CJ a (4 ^ c)) (hw : Ok5 w) :
    Ok5 (mC Mt a w) ∧ (tauG x a)⁻¹ * epsG x w * tauG x a = epsG x (mC Mt a w) := by
  have hcol : ∀ c < 5, Ok5 (colM Mt a c) := fun c hc => by
    rw [hM c hc]
    exact (conj_tau h ha (ok5_unit hc)).1
  obtain ⟨h1, h2⟩ := fold_eps h (colM Mt a) hcol hw.2 5 le_rfl
  rw [mC_eq]
  refine ⟨h1, ?_⟩
  rw [h2, conj_epsG]
  apply congrArg
  apply List.map_congr_left
  intro c hc
  have hc5 := List.mem_range.1 hc
  rw [hM c hc5, ← (conj_tau h ha (ok5_unit hc5)).2, epsG_unit x hc5]

end GenE

section OnJ

theorem eAlgS : EAlg sE CFSG.KD.Fi23Q.SubCJ := eAlg_of pcRelS

theorem eps_add {u v : ℕ} (hu : Ok5 u) (hv : Ok5 v) : eps (add3 u v) = eps u * eps v :=
  epsG_add' eAlgS hu hv

theorem eps_neg {u : ℕ} (hu : Ok5 u) : eps (neg3 u) = (eps u)⁻¹ := epsG_neg eAlgS hu

theorem clsM_cols {a : ℕ} (ha : Ok4 a) :
    ∀ c < 5, colM CFSG.KD.Fi23Q.clsMt a c = mT CFSG.KD.Fi23Q.SubCJ a (4 ^ c) := by
  obtain ⟨i, hi, rfl⟩ := ok4_vec3 ha
  intro c hc
  rw [clsMK_sound CFSG.KD.Fi23Q.clsM_ok i hi c hc, one_shiftLeft2]

theorem conj_mC {a w : ℕ} (ha : Ok4 a) (hw : Ok5 w) :
    Ok5 (mC CFSG.KD.Fi23Q.clsMt a w) ∧
      (tau a)⁻¹ * eps w * tau a = eps (mC CFSG.KD.Fi23Q.clsMt a w) :=
  conj_mC_gen eAlgS ha.2 (clsM_cols ha) hw

theorem conj_skS {k w : ℕ} (hk : k < 4) (hw : Ok5 w) :
    Ok5 (mE CFSG.KD.Fi23Q.SubCJ k w) ∧
      (sE k)⁻¹ * eps w * sE k = eps (mE CFSG.KD.Fi23Q.SubCJ k w) :=
  conj_sk eAlgS hk hw

@[expose] noncomputable def topS (x : CFSG.Sporadic.Fi23.J) : ℕ := lowV (vS x) 4

theorem te_mem {a w : ℕ} (ha : a < 4 ^ 4) : tau a * eps w ∈ SubS := by
  rw [te_nv ha]
  exact nvS_mem _

theorem vS_te {a w : ℕ} (ha : Ok4 a) (hw : Ok5 w) : vS (tau a * eps w) = a + 256 * w := by
  obtain ⟨h1, h2⟩ := vS_spec (te_mem (w := w) ha.1)
  exact nvS_inj (ok9_of_vecOK h1) (ok9_te ha hw) (by rw [h2, te_nv ha.1])

theorem topS_te {a w : ℕ} (ha : Ok4 a) (hw : Ok5 w) : topS (tau a * eps w) = a := by
  unfold topS
  rw [vS_te ha hw, lowV_te a w ha.1]

theorem tau_nv {a : ℕ} (ha : a < 4 ^ 4) : tau a = nv sE 9 a := by
  have := te_nv (w := 0) ha
  rwa [eps_zero, mul_one, Nat.mul_zero, Nat.add_zero] at this

theorem tau_mem {a : ℕ} (ha : a < 4 ^ 4) : tau a ∈ SubS := by
  rw [tau_nv ha]
  exact nvS_mem _

theorem sE_mem {k : ℕ} (hk : k < 9) : sE k ∈ SubS := Subgroup.subset_closure ⟨k, hk, rfl⟩

theorem ok4_zero : Ok4 0 := ⟨by norm_num, fun k _ => by rw [dg_eq]; simp⟩

theorem ok4_topS {x : CFSG.Sporadic.Fi23.J} (hx : x ∈ SubS) : Ok4 (topS x) := by
  obtain ⟨a, w, ha, hw, rfl⟩ := te_of_mem hx
  rw [topS_te ha hw]
  exact ha

theorem topS_one : topS (1 : CFSG.Sporadic.Fi23.J) = 0 := by
  have := topS_te ok4_zero ok5_zero
  rwa [tau_zero, eps_zero, one_mul] at this

theorem topS_mulE {z : CFSG.Sporadic.Fi23.J} {u : ℕ} (hz : z ∈ SubS) (hu : Ok5 u) : topS (z * eps u) = topS z := by
  obtain ⟨a, w, ha, hw, rfl⟩ := te_of_mem hz
  rw [mul_assoc, ← eps_add hw hu, topS_te ha (ok5_add3 hw hu), topS_te ha hw]

theorem topS_eq_zero {z : CFSG.Sporadic.Fi23.J} (hz : z ∈ SubS) : topS z = 0 ↔ ∃ w, Ok5 w ∧ z = eps w := by
  obtain ⟨a, w, ha, hw, rfl⟩ := te_of_mem hz
  rw [topS_te ha hw]
  constructor
  · rintro rfl
    exact ⟨w, hw, by rw [tau_zero, one_mul]⟩
  · rintro ⟨u, hu, e⟩
    have e' : tau a * eps w = tau 0 * eps u := by rw [tau_zero, one_mul, e]
    exact (te_inj ha ok4_zero hw hu e').1

theorem topS_eq {x y : CFSG.Sporadic.Fi23.J} (hx : x ∈ SubS) (hy : y ∈ SubS) (h : topS x = topS y) :
    ∃ u, Ok5 u ∧ x⁻¹ * y = eps u := by
  obtain ⟨a, w, ha, hw, rfl⟩ := te_of_mem hx
  obtain ⟨b, v, hb, hv, rfl⟩ := te_of_mem hy
  rw [topS_te ha hw, topS_te hb hv] at h
  subst h
  refine ⟨add3 (neg3 w) v, ok5_add3 (ok5_neg3 hw) hv, ?_⟩
  rw [eps_add (ok5_neg3 hw) hv, eps_neg hw]
  group

theorem tau_sk {a k : ℕ} (ha : Ok4 a) (hk : k < 4) :
    ∃ e, Ok5 e ∧ tau a * sE k = tau (rT CFSG.KD.Fi23Q.clsR a k) * eps e ∧
      Ok4 (rT CFSG.KD.Fi23Q.clsR a k) := by
  obtain ⟨i, hi, rfl⟩ := ok4_vec3 ha
  obtain ⟨m1, m2⟩ := mulV_sound (x := sE) relS_parts.1 pcRelS (vec3_vecOK i hi)
    (unit9_ok k (by omega))
  have h9 := ok9_of_vecOK m1
  rw [clsRK_sound CFSG.KD.Fi23Q.clsRt_ok i hi k hk, one_shiftLeft2]
  refine ⟨Nat.shiftRight (mulV CFSG.KD.Fi23Q.SubPW CFSG.KD.Fi23Q.SubCJ 9 (vec3 4 i) (4 ^ k)) 8,
    ⟨?_, fun c hc => ?_⟩, ?_, ⟨?_, fun j hj => ?_⟩⟩
  · rw [shr8_eq]
    have := h9.1
    norm_num at *
    omega
  · rw [dg_shr8]
    exact h9.2 _ (by omega)
  · rw [← nv_split, m2, nv_unit9 sE (by omega : k < 9), tau_nv ha.1]
  · rw [lowV_eq]
    exact Nat.mod_lt _ (by norm_num)
  · rw [dg_lowV4 _ hj]
    exact h9.2 j (by omega)

theorem topS_mul_sk {z : CFSG.Sporadic.Fi23.J} {k : ℕ} (hz : z ∈ SubS) (hk : k < 4) :
    topS (z * sE k) = rT CFSG.KD.Fi23Q.clsR (topS z) k := by
  obtain ⟨a, w, ha, hw, rfl⟩ := te_of_mem hz
  obtain ⟨o, c⟩ := conj_skS hk hw
  obtain ⟨e, he, et, ht⟩ := tau_sk ha hk
  have key : tau a * eps w * sE k =
      tau (rT CFSG.KD.Fi23Q.clsR a k) * eps (add3 e (mE CFSG.KD.Fi23Q.SubCJ k w)) := by
    rw [eps_add he o, ← mul_assoc, ← et, ← c]
    group
  rw [key, topS_te ht (ok5_add3 he o), topS_te ha hw]

theorem topS_mul_pow {z : CFSG.Sporadic.Fi23.J} {k e : ℕ} (hz : z ∈ SubS) (hk : k < 4) (he : e < 3) :
    topS (z * sE k ^ e) = rep e (fun y => rT CFSG.KD.Fi23Q.clsR y k) (topS z) := by
  interval_cases e
  · rw [pow_zero, mul_one, rep_zero]
  · rw [pow_one, rep_one, topS_mul_sk hz hk]
  · rw [rep_two, pow_two, ← mul_assoc, topS_mul_sk (mul_mem hz (sE_mem (by omega))) hk,
      topS_mul_sk hz hk]

theorem topS_mul_tau {z : CFSG.Sporadic.Fi23.J} {b : ℕ} (hz : z ∈ SubS) (hb : Ok4 b) :
    topS (z * tau b) = muT CFSG.KD.Fi23Q.clsR (topS z) b := by
  have m : ∀ {y : J} (k e : ℕ), y ∈ SubS → k < 9 → y * sE k ^ e ∈ SubS :=
    fun k e hy hk => mul_mem hy (pow_mem (sE_mem hk) e)
  have e : z * tau b = z * sE 0 ^ dg b 0 * sE 1 ^ dg b 1 * sE 2 ^ dg b 2 * sE 3 ^ dg b 3 := by
    rw [tau_eq]
    simp only [mul_assoc]
  have h0 := m 0 (dg b 0) hz (by omega)
  have h1 := m 1 (dg b 1) h0 (by omega)
  have h2 := m 2 (dg b 2) h1 (by omega)
  rw [e, muT_eq, topS_mul_pow h2 (by omega) (hb.2 3 (by omega)),
    topS_mul_pow h1 (by omega) (hb.2 2 (by omega)), topS_mul_pow h0 (by omega) (hb.2 1 (by omega)),
    topS_mul_pow hz (by omega) (hb.2 0 (by omega))]

theorem topS_mul {x y : CFSG.Sporadic.Fi23.J} (hx : x ∈ SubS) (hy : y ∈ SubS) :
    topS (x * y) = muT CFSG.KD.Fi23Q.clsR (topS x) (topS y) := by
  obtain ⟨b, w, hb, hw, rfl⟩ := te_of_mem hy
  rw [← mul_assoc, topS_mulE (mul_mem hx (tau_mem hb.1)) hw, topS_mul_tau hx hb, topS_te hb hw]

theorem bitM_iff (m a : ℕ) : bitM m a = true ↔ m.testBit a = true := by
  have e : Nat.land (Nat.shiftRight m a) 1 = m / 2 ^ a % 2 := by
    change (m >>> a) &&& 1 = _
    rw [Nat.and_one_is_mod, Nat.shiftRight_eq_div_pow]
  unfold bitM
  rw [e, Nat.testBit_eq_decide_div_mod_eq, decide_eq_true_iff]
  constructor
  · exact Nat.eq_of_beq_eq_true
  · intro h
    rw [h]
    rfl

theorem inv4_vec3 : ∀ i < 81, inv4 (vec3 4 i) = i := by decide +kernel

theorem top_mask {D : Subgroup CFSG.Sporadic.Fi23.J} (hDS : D ≤ SubS) (hc : ∀ x ∈ D, ∀ y ∈ D, x * y = y * x)
    (h3 : ∀ x ∈ D, x ^ 3 = 1) : ∃ i < CFSG.KD.Fi23Q.clsL.length,
      ∀ a, bitM (CFSG.KD.Fi23Q.clsL.getD i 0) a = true ↔ ∃ x ∈ D, topS x = a := by
  classical
  have hL := clsLK_sound CFSG.KD.Fi23Q.clsLt_ok
  let F : ℕ → Finset ℕ := fun m => (Finset.range 81).filter fun j => bitM m (vec3 4 j) = true
  let P : Finset ℕ := (Finset.range CFSG.KD.Fi23Q.clsL.length).filter fun i =>
    ∀ a, bitM (CFSG.KD.Fi23Q.clsL.getD i 0) a = true → ∃ x ∈ D, topS x = a
  have hP0 : 0 ∈ P := by
    simp only [P, Finset.mem_filter, Finset.mem_range]
    refine ⟨?_, fun a ha => ?_⟩
    · rcases Nat.eq_zero_or_pos CFSG.KD.Fi23Q.clsL.length with h | h
      · have h1 := hL.1
        rw [List.length_eq_zero_iff.1 h] at h1
        simp at h1
      · exact h
    · rw [hL.1, bitM_iff] at ha
      have ha0 : a = 0 := (testBit_one_shiftLeft 0 a).1 ha
      exact ⟨1, D.one_mem, by rw [topS_one, ha0]⟩
  obtain ⟨i, hiP, hmax⟩ := Finset.exists_max_image P (fun i => (F (CFSG.KD.Fi23Q.clsL.getD i 0)).card)
    ⟨0, hP0⟩
  simp only [P, Finset.mem_filter, Finset.mem_range] at hiP
  refine ⟨i, hiP.1, fun a => ⟨hiP.2 a, fun ha => ?_⟩⟩
  by_contra hb
  obtain ⟨x, hx, rfl⟩ := ha
  have hxS := hDS hx
  obtain ⟨ia, hia, hva⟩ := ok4_vec3 (ok4_topS hxS)
  have hb' : bitM (CFSG.KD.Fi23Q.clsL.getD i 0) (vec3 4 ia) = false := by
    rw [hva]
    simpa using hb
  have h3' : muT CFSG.KD.Fi23Q.clsR (muT CFSG.KD.Fi23Q.clsR (vec3 4 ia) (vec3 4 ia))
      (vec3 4 ia) = 0 := by
    rw [hva, ← topS_mul hxS hxS, ← topS_mul (mul_mem hxS hxS) hxS, ← pow_three', h3 x hx,
      topS_one]
  have hcm : commH CFSG.KD.Fi23Q.clsR (CFSG.KD.Fi23Q.clsL.getD i 0) (vec3 4 ia) = true := by
    rw [commH_iff]
    intro j _ hbj
    obtain ⟨y, hy, hyt⟩ := hiP.2 _ hbj
    rw [hva, ← hyt, ← topS_mul hxS (hDS hy), ← topS_mul (hDS hy) hxS, hc x hx y hy]
  obtain ⟨j, hj, hLj⟩ := (hL.2 i hiP.1).2 ia hia hb' h3' hcm
  have hPj : j ∈ P := by
    simp only [P, Finset.mem_filter, Finset.mem_range]
    refine ⟨hj, fun b hbj => ?_⟩
    rw [hLj, bitM_iff, testBit_closM] at hbj
    obtain ⟨i', _, hbi', hbe⟩ := hbj
    obtain ⟨y, hy, hyt⟩ := hiP.2 _ hbi'
    rcases hbe with rfl | rfl | rfl
    · exact ⟨y, hy, hyt⟩
    · exact ⟨x * y, D.mul_mem hx hy, by rw [topS_mul hxS (hDS hy), hyt, hva]⟩
    · exact ⟨x * x * y, D.mul_mem (D.mul_mem hx hx) hy, by
        rw [topS_mul (mul_mem hxS hxS) (hDS hy), topS_mul hxS hxS, hyt, hva]⟩
  have hlt : (F (CFSG.KD.Fi23Q.clsL.getD i 0)).card < (F (CFSG.KD.Fi23Q.clsL.getD j 0)).card := by
    apply Finset.card_lt_card
    rw [Finset.ssubset_iff_of_subset]
    · refine ⟨ia, ?_, ?_⟩
      · simp only [F, Finset.mem_filter, Finset.mem_range]
        refine ⟨hia, ?_⟩
        rw [hLj, bitM_iff, testBit_closM]
        exact ⟨0, by norm_num, (hL.2 i hiP.1).1, Or.inr (Or.inl (muT_zero _ _).symm)⟩
      · simp only [F, Finset.mem_filter, Finset.mem_range, hb']
        simp
    · intro j' hj'
      simp only [F, Finset.mem_filter, Finset.mem_range] at hj' ⊢
      refine ⟨hj'.1, ?_⟩
      rw [hLj, bitM_iff, testBit_closM]
      exact ⟨j', hj'.1, hj'.2, Or.inl rfl⟩
  exact absurd (hmax j hPj) (not_le.2 hlt)

@[expose] noncomputable def SubE : Subgroup CFSG.Sporadic.Fi23.J where
  carrier := {z | ∃ w, Ok5 w ∧ z = eps w}
  mul_mem' := by
    rintro _ _ ⟨u, hu, rfl⟩ ⟨v, hv, rfl⟩
    exact ⟨add3 u v, ok5_add3 hu hv, (eps_add hu hv).symm⟩
  one_mem' := ⟨0, ok5_zero, eps_zero.symm⟩
  inv_mem' := by
    rintro _ ⟨u, hu, rfl⟩
    exact ⟨neg3 u, ok5_neg3 hu, (eps_neg hu).symm⟩

theorem card_filter_range (n : ℕ) (p : ℕ → Bool) :
    ((Finset.range n).filter fun j => p j = true).card = ((List.range n).filter p).length := by
  rw [Finset.card_def, Finset.filter_val, Finset.range_val, Multiset.range, Multiset.filter_coe,
    Multiset.coe_card]
  simp

theorem card_D {D : Subgroup CFSG.Sporadic.Fi23.J} (hDS : D ≤ SubS) {m : ℕ}
    (hT : ∀ a, bitM m a = true ↔ ∃ x ∈ D, topS x = a) :
    Nat.card D = popc m * Nat.card (SubE.subgroupOf D) := by
  classical
  rw [Subgroup.card_eq_card_quotient_mul_card_subgroup (SubE.subgroupOf D)]
  congr 1
  let f : D ⧸ SubE.subgroupOf D → ℕ := Quotient.lift (fun x : D => topS (x : J)) (by
    intro a b hab
    have hab' : a⁻¹ * b ∈ SubE.subgroupOf D := QuotientGroup.leftRel_apply.1 hab
    rw [Subgroup.mem_subgroupOf] at hab'
    obtain ⟨u, hu, e⟩ := hab'
    have eb : (b : J) = a * eps u := by
      rw [← e]
      simp
    change topS (a : J) = topS (b : J)
    rw [eb, topS_mulE (hDS a.2) hu])
  have hf : Function.Injective f := by
    intro p q hpq
    induction p using QuotientGroup.induction_on with | H a => ?_
    induction q using QuotientGroup.induction_on with | H b => ?_
    apply QuotientGroup.eq.2
    rw [Subgroup.mem_subgroupOf]
    obtain ⟨u, hu, e⟩ := topS_eq (hDS a.2) (hDS b.2) hpq
    exact ⟨u, hu, by simpa using e⟩
  have hR : Set.range f = ↑(((Finset.range 81).filter fun j => bitM m (vec3 4 j) = true).image
      (vec3 4)) := by
    ext a
    simp only [Set.mem_range, Finset.coe_image, Finset.coe_filter, Finset.mem_range,
      Set.mem_image, Set.mem_setOf_eq]
    constructor
    · rintro ⟨q, rfl⟩
      induction q using QuotientGroup.induction_on with | H x => ?_
      obtain ⟨i, hi, hv⟩ := ok4_vec3 (ok4_topS (hDS x.2))
      refine ⟨i, ⟨hi, ?_⟩, hv⟩
      rw [hv]
      exact (hT _).2 ⟨x, x.2, rfl⟩
    · rintro ⟨i, ⟨_, hb⟩, rfl⟩
      obtain ⟨x, hx, hxt⟩ := (hT _).1 hb
      exact ⟨(⟨x, hx⟩ : D), hxt⟩
  rw [← Nat.card_range_of_injective hf, hR, Nat.card_coe_set_eq, Set.ncard_coe_finset,
    Finset.card_image_of_injOn, card_filter_range, popc_eq]
  intro i hi j hj e
  simp only [Finset.coe_filter, Finset.mem_range, Set.mem_setOf_eq] at hi hj
  rw [← inv4_vec3 i hi.1, ← inv4_vec3 j hj.1, e]

theorem inter_fix {D : Subgroup CFSG.Sporadic.Fi23.J} (hDS : D ≤ SubS) (hc : ∀ x ∈ D, ∀ y ∈ D, x * y = y * x)
    {m bd : ℕ} (hT : ∀ a, bitM m a = true ↔ ∃ x ∈ D, topS x = a)
    (hB : ∀ j < f8 bd 0, bitM m (f8 bd (j + 1)) = true) {w : ℕ} (hw : Ok5 w) (hwD : eps w ∈ D) :
    fixB CFSG.KD.Fi23Q.clsMt bd w = true := by
  rw [fixB_iff]
  intro j hj
  obtain ⟨x, hx, hxt⟩ := (hT _).1 (hB j hj)
  obtain ⟨a, u, ha, hu, rfl⟩ := te_of_mem (hDS hx)
  rw [topS_te ha hu] at hxt
  rw [← hxt]
  have hcomm := hc _ hx _ hwD
  have e2 : eps u * eps w = eps w * eps u := epsG_comm eAlgS hu hw
  have h1 : (tau a)⁻¹ * eps w * tau a = eps w := by
    calc (tau a)⁻¹ * eps w * tau a = (tau a)⁻¹ * (eps w * (tau a * eps u)) * (eps u)⁻¹ := by
          group
      _ = (tau a)⁻¹ * (tau a * eps u * eps w) * (eps u)⁻¹ := by rw [hcomm]
      _ = eps u * eps w * (eps u)⁻¹ := by group
      _ = eps w := by rw [e2]; group
  obtain ⟨o, hcm⟩ := conj_mC ha hw
  rw [hcm] at h1
  exact eps_inj o hw h1

theorem vS_eps {u : ℕ} (hu : Ok5 u) : Nat.shiftRight (vS (eps u)) 8 = u := by
  have := vS_te ok4_zero hu
  rw [tau_zero, one_mul] at this
  rw [this, shr8_te 0 u (by norm_num)]

theorem inter_E {D : Subgroup CFSG.Sporadic.Fi23.J} (hDS : D ≤ SubS) (hc : ∀ x ∈ D, ∀ y ∈ D, x * y = y * x)
    (hD : Nat.card D = 81) {i : ℕ} (hi1 : 1 ≤ i) (hi : i < CFSG.KD.Fi23Q.clsL.length)
    (hT : ∀ a, bitM (CFSG.KD.Fi23Q.clsL.getD i 0) a = true ↔ ∃ x ∈ D, topS x = a) {w : ℕ}
    (hw : Ok5 w) : eps w ∈ D ↔ fixB CFSG.KD.Fi23Q.clsMt (CFSG.KD.Fi23Q.clsB.getD i 0) w = true := by
  classical
  obtain ⟨hB, hle⟩ := clsCK_sound CFSG.KD.Fi23Q.clsC_ok i hi1 hi
  refine ⟨inter_fix hDS hc hT hB hw, fun hf => ?_⟩
  by_contra hwD
  have hcard := card_D hDS hT
  let C : Finset ℕ := (Finset.range 243).filter fun j =>
    fixB CFSG.KD.Fi23Q.clsMt (CFSG.KD.Fi23Q.clsB.getD i 0) (vec3 5 j) = true
  have hCc : C.card = cntC CFSG.KD.Fi23Q.clsMt (CFSG.KD.Fi23Q.clsB.getD i 0) := by
    rw [card_filter_range, cntC_eq]
  obtain ⟨iw, hiw, hvw⟩ := ok5_vec3 hw
  have hwC : iw ∈ C := by
    simp only [C, Finset.mem_filter, Finset.mem_range]
    rw [hvw]
    exact ⟨hiw, hf⟩
  have hK : ∀ k : SubE.subgroupOf D, ∃ u, Ok5 u ∧ ((k : D) : J) = eps u :=
    fun k => Subgroup.mem_subgroupOf.1 k.2
  let g : SubE.subgroupOf D → C.erase iw := fun k =>
    ⟨inv5 (Nat.shiftRight (vS ((k : D) : J)) 8), by
      obtain ⟨u, hu, e⟩ := hK k
      have hiu := inv5_ok u (by have := hu.1; norm_num at this; omega) hu.2
      rw [e, vS_eps hu]
      simp only [C, Finset.mem_erase, Finset.mem_filter, Finset.mem_range]
      refine ⟨fun h => hwD ?_, hiu.1, ?_⟩
      · have : u = w := by rw [← hiu.2, h, hvw]
        rw [← this, ← e]
        exact (k : D).2
      · rw [hiu.2]
        exact inter_fix hDS hc hT hB hu (by rw [← e]; exact (k : D).2)⟩
  have hg : Function.Injective g := by
    intro k1 k2 e
    obtain ⟨u1, hu1, e1⟩ := hK k1
    obtain ⟨u2, hu2, e2⟩ := hK k2
    have e' := congrArg Subtype.val e
    simp only [g, e1, e2, vS_eps hu1, vS_eps hu2] at e'
    have h1 := inv5_ok u1 (by have := hu1.1; norm_num at this; omega) hu1.2
    have h2 := inv5_ok u2 (by have := hu2.1; norm_num at this; omega) hu2.2
    have : u1 = u2 := by rw [← h1.2, ← h2.2, e']
    apply Subtype.ext
    apply Subtype.ext
    rw [e1, e2, this]
  have hle2 := Nat.card_le_card_of_injective g hg
  rw [Nat.card_eq_finsetCard, Finset.card_erase_of_mem hwC, hCc] at hle2
  have hpos : 0 < popc (CFSG.KD.Fi23Q.clsL.getD i 0) := by
    rcases Nat.eq_zero_or_pos (popc (CFSG.KD.Fi23Q.clsL.getD i 0)) with h | h
    · rw [h, zero_mul] at hcard
      omega
    · exact h
  have hc1 : 1 ≤ cntC CFSG.KD.Fi23Q.clsMt (CFSG.KD.Fi23Q.clsB.getD i 0) := by
    rw [← hCc]
    exact Finset.card_pos.2 ⟨iw, hwC⟩
  have := Nat.mul_le_mul_left (popc (CFSG.KD.Fi23Q.clsL.getD i 0)) hle2
  rw [Nat.mul_sub, mul_one, ← hcard, hD] at this
  omega

end OnJ

end CertificateChecks.KernelFi23Q

end
