module

public import Certificates.Kernel.Fi23Q.SubClsTop
import Certificates.Kernel.Fi23Q.SubClsChk

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelFi23Q

attribute [local irreducible] sE

open CFSG.Sporadic.Fi23 CFSG.KC.Fi23K CFSG.KC.Fi23Q CFSG.KC.Pc3 CFSG.KS.Pc3 CFSG.KS.Fi23Q
  CFSG.Perm CFSG.KD.Fi23K
open CFSG.Sporadic.Th hiding J a b closure_ab gA gB rows_B_cube
open CFSG.HardMathSupport.Timmesfeld.SporadicBalance.BThreeFi23 (t3)

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

section Gen

variable {G : Type*} [Group G]

theorem cls_cube_conj (t y : G) :
    (t * y) ^ 3 = t ^ 3 * ((t⁻¹ * (t⁻¹ * y * t) * t) * (t⁻¹ * y * t) * y) := by
  rw [pow_three, pow_three]
  group

theorem cls_comm_of {D : Subgroup G} (h : IsMulCommutative D) :
    ∀ x ∈ D, ∀ y ∈ D, x * y = y * x :=
  fun x hx y hy => congrArg Subtype.val (h.is_comm.comm (⟨x, hx⟩ : D) ⟨y, hy⟩)

end Gen

theorem dg_sub3 {u v c : ℕ} (hc : c < 5) (hu : dg u c < 3) (hv : dg v c < 3) :
    dg (sub3 u v) c = (dg u c + 2 * dg v c % 3) % 3 := by
  have hn : dg (neg3 v) c < 3 := by rw [dg_neg3 hc hv]; omega
  unfold sub3
  rw [dg_add3 hc hu hn, dg_neg3 hc hv]

theorem dg_smul3 {e c p : ℕ} (hp : p < 5) (hc : dg c p = 1) (he : e < 3) :
    dg (smul3 e c) p = e := by
  unfold smul3
  simp only [CFSG.KS.PK.nIf_eq]
  interval_cases e
  · simp [dg_eq]
  · simpa using hc
  · have e1 : Nat.beq 2 0 = false := rfl
    have e2 : Nat.beq 2 1 = false := rfl
    simp only [e1, e2, Bool.false_eq_true, ↓reduceIte]
    rw [dg_neg3 hp (by omega), hc]

theorem dot3_eq (u v : ℕ) : dot3 u v = (0 + dg u 0 * dg v 0 + dg u 1 * dg v 1 + dg u 2 * dg v 2 +
    dg u 3 * dg v 3 + dg u 4 * dg v 4) % 3 := rfl

theorem cubeV_eq (PW CJ x : ℕ) : cubeV PW CJ x = mulV PW CJ 9 (mulV PW CJ 9 x x) x := rfl

noncomputable def dgv (u : ℕ) : Fin 5 → ZMod 3 := fun c => ((dg u c : ℕ) : ZMod 3)

theorem dgv_add {u v : ℕ} (hu : Ok5 u) (hv : Ok5 v) : dgv (add3 u v) = dgv u + dgv v := by
  funext c
  simp only [dgv, Pi.add_apply]
  rw [dg_add3 c.2 (hu.2 c c.2) (hv.2 c c.2), ZMod.natCast_mod, Nat.cast_add]

theorem dgv_neg {u : ℕ} (hu : Ok5 u) : dgv (neg3 u) = -dgv u := by
  funext c
  simp only [dgv, Pi.neg_apply]
  rw [dg_neg3 c.2 (hu.2 c c.2), ZMod.natCast_mod, Nat.cast_mul]
  have h2 : ((2 : ℕ) : ZMod 3) = -1 := by decide
  rw [h2, neg_one_mul]

theorem dgv_zero : dgv 0 = 0 := by
  funext c
  simp [dgv, dg_eq]

theorem dgv_inj {u v : ℕ} (hu : Ok5 u) (hv : Ok5 v) (h : dgv u = dgv v) : u = v := by
  refine eq_of_dg hu.1 hv.1 fun c hc => ?_
  have e := congrFun h ⟨c, hc⟩
  simp only [dgv] at e
  rw [ZMod.natCast_eq_natCast_iff', Nat.mod_eq_of_lt (hu.2 c hc),
    Nat.mod_eq_of_lt (hv.2 c hc)] at e
  exact e

section OnJ


theorem npV_len : CFSG.KD.Fi23Q.npV.length = 131 := by decide +kernel

theorem ok5_shr8 {v : ℕ} (h : vecOK 9 v = true) : Ok5 (Nat.shiftRight v 8) := by
  have h9 := ok9_of_vecOK h
  refine ⟨?_, fun c hc => ?_⟩
  · rw [shr8_eq]
    have := h9.1
    norm_num at *
    omega
  · rw [dg_shr8]
    exact h9.2 _ (by omega)

theorem vecOK_of_ok4 {a : ℕ} (ha : Ok4 a) : vecOK 9 a = true := by
  obtain ⟨i, hi, rfl⟩ := ok4_vec3 ha
  exact vec3_vecOK i hi

theorem eps_smul' {e u : ℕ} (he : e < 3) (hu : Ok5 u) : eps (smul3 e u) = eps u ^ e :=
  epsG_smul eAlgS he hu

theorem cert_split {k : ℕ} (hk : k < 131) :
    Ok5 (Nat.shiftRight (CFSG.KD.Fi23Q.npV.getD k 0) 8) ∧
      nv sE 9 (CFSG.KD.Fi23Q.npV.getD k 0) = tau (lowV (CFSG.KD.Fi23Q.npV.getD k 0) 4) *
        eps (Nat.shiftRight (CFSG.KD.Fi23Q.npV.getD k 0) 8) :=
  ⟨ok5_shr8 (np_conj hk).1, nv_split _⟩

theorem cls_mem_cover {D : Subgroup CFSG.Sporadic.Fi23.J} {b w u : ℕ} (hw : Ok5 w) (hu : Ok5 u)
    (hx : tau b * eps w ∈ D) (hd : eps (sub3 u w) ∈ D) : tau b * eps u ∈ D := by
  have e : eps u = eps w * eps (sub3 u w) := by
    rw [← eps_add hw (ok5_sub3 hu hw)]
    refine eps_congr fun c hc => ?_
    rw [dg_add3 hc (hw.2 c hc) ((ok5_sub3 hu hw).2 c hc), dg_sub3 hc (hu.2 c hc) (hw.2 c hc)]
    have := hu.2 c hc
    have := hw.2 c hc
    omega
  rw [e, ← mul_assoc]
  exact D.mul_mem hx hd

theorem cls_cube {a w : ℕ} (ha : Ok4 a) (hw : Ok5 w)
    (hl : lowV (cubeV CFSG.KD.Fi23Q.SubPW CFSG.KD.Fi23Q.SubCJ a) 4 = 0)
    (h3 : (tau a * eps w) ^ 3 = 1) :
    cubeE CFSG.KD.Fi23Q.clsMt a
      (Nat.shiftRight (cubeV CFSG.KD.Fi23Q.SubPW CFSG.KD.Fi23Q.SubCJ a) 8) w = true := by
  have hv := vecOK_of_ok4 ha
  obtain ⟨m1, m2⟩ := mulV_sound (x := sE) relS_parts.1 pcRelS hv hv
  obtain ⟨c1, c2⟩ := mulV_sound (x := sE) relS_parts.1 pcRelS m1 hv
  have ht5 := ok5_shr8 (v := cubeV CFSG.KD.Fi23Q.SubPW CFSG.KD.Fi23Q.SubCJ a) c1
  have hcube : tau a ^ 3 =
      eps (Nat.shiftRight (cubeV CFSG.KD.Fi23Q.SubPW CFSG.KD.Fi23Q.SubCJ a) 8) := by
    have e := nv_split (cubeV CFSG.KD.Fi23Q.SubPW CFSG.KD.Fi23Q.SubCJ a)
    rw [hl, tau_zero, one_mul] at e
    rw [← e, cubeV_eq, c2, m2, ← tau_nv ha.1, pow_three']
  obtain ⟨o1, e1⟩ := conj_mC ha hw
  obtain ⟨o2, e2⟩ := conj_mC ha o1
  have hV := ok5_add3 ht5 (ok5_add3 hw (ok5_add3 o1 o2))
  have key : eps (add3 (Nat.shiftRight (cubeV CFSG.KD.Fi23Q.SubPW CFSG.KD.Fi23Q.SubCJ a) 8)
      (add3 w (add3 (mC CFSG.KD.Fi23Q.clsMt a w)
        (mC CFSG.KD.Fi23Q.clsMt a (mC CFSG.KD.Fi23Q.clsMt a w))))) = eps 0 := by
    have e3 := ok5_add3 o2 (ok5_add3 o1 hw)
    rw [eps_zero, eps_congr (v := add3 (Nat.shiftRight (cubeV CFSG.KD.Fi23Q.SubPW
        CFSG.KD.Fi23Q.SubCJ a) 8) (add3 (mC CFSG.KD.Fi23Q.clsMt a (mC CFSG.KD.Fi23Q.clsMt a w))
        (add3 (mC CFSG.KD.Fi23Q.clsMt a w) w))) fun c hc => by
      rw [dg_add3 hc (ht5.2 c hc) ((ok5_add3 hw (ok5_add3 o1 o2)).2 c hc),
        dg_add3 hc (hw.2 c hc) ((ok5_add3 o1 o2).2 c hc), dg_add3 hc (o1.2 c hc) (o2.2 c hc),
        dg_add3 hc (ht5.2 c hc) (e3.2 c hc), dg_add3 hc (o2.2 c hc) ((ok5_add3 o1 hw).2 c hc),
        dg_add3 hc (o1.2 c hc) (hw.2 c hc)]
      omega]
    rw [eps_add ht5 e3, eps_add o2 (ok5_add3 o1 hw), eps_add o1 hw, ← h3, cls_cube_conj, e1, e2,
      hcube]
    simp only [mul_assoc]
  have h0 := eps_inj hV ok5_zero key
  unfold cubeE
  rw [h0]
  rfl

theorem cls_comm {ai aj wi wj : ℕ} (hai : Ok4 ai) (haj : Ok4 aj) (hwi : Ok5 wi) (hwj : Ok5 wj)
    (hl : lowV (mulV CFSG.KD.Fi23Q.SubPW CFSG.KD.Fi23Q.SubCJ 9 ai aj) 4 =
      lowV (mulV CFSG.KD.Fi23Q.SubPW CFSG.KD.Fi23Q.SubCJ 9 aj ai) 4)
    (hc : tau ai * eps wi * (tau aj * eps wj) = tau aj * eps wj * (tau ai * eps wi)) :
    commE CFSG.KD.Fi23Q.clsMt ai aj
      (sub3 (Nat.shiftRight (mulV CFSG.KD.Fi23Q.SubPW CFSG.KD.Fi23Q.SubCJ 9 ai aj) 8)
        (Nat.shiftRight (mulV CFSG.KD.Fi23Q.SubPW CFSG.KD.Fi23Q.SubCJ 9 aj ai) 8)) wi wj = true := by
  obtain ⟨p1, p2⟩ := mulV_sound (x := sE) relS_parts.1 pcRelS (vecOK_of_ok4 hai) (vecOK_of_ok4 haj)
  obtain ⟨q1, q2⟩ := mulV_sound (x := sE) relS_parts.1 pcRelS (vecOK_of_ok4 haj) (vecOK_of_ok4 hai)
  have hP5 := ok5_shr8 p1
  have hQ5 := ok5_shr8 q1
  have hP : tau ai * tau aj =
      tau (lowV (mulV CFSG.KD.Fi23Q.SubPW CFSG.KD.Fi23Q.SubCJ 9 ai aj) 4) *
        eps (Nat.shiftRight (mulV CFSG.KD.Fi23Q.SubPW CFSG.KD.Fi23Q.SubCJ 9 ai aj) 8) := by
    rw [← nv_split, p2, ← tau_nv hai.1, ← tau_nv haj.1]
  have hQ : tau aj * tau ai =
      tau (lowV (mulV CFSG.KD.Fi23Q.SubPW CFSG.KD.Fi23Q.SubCJ 9 ai aj) 4) *
        eps (Nat.shiftRight (mulV CFSG.KD.Fi23Q.SubPW CFSG.KD.Fi23Q.SubCJ 9 aj ai) 8) := by
    rw [hl, ← nv_split, q2, ← tau_nv hai.1, ← tau_nv haj.1]
  obtain ⟨oi, ei⟩ := conj_mC haj hwi
  obtain ⟨oj, ej⟩ := conj_mC hai hwj
  have k : eps (Nat.shiftRight (mulV CFSG.KD.Fi23Q.SubPW CFSG.KD.Fi23Q.SubCJ 9 ai aj) 8) *
      ((tau aj)⁻¹ * eps wi * tau aj * eps wj) =
      eps (Nat.shiftRight (mulV CFSG.KD.Fi23Q.SubPW CFSG.KD.Fi23Q.SubCJ 9 aj ai) 8) *
      ((tau ai)⁻¹ * eps wj * tau ai * eps wi) := by
    have hp : eps (Nat.shiftRight (mulV CFSG.KD.Fi23Q.SubPW CFSG.KD.Fi23Q.SubCJ 9 ai aj) 8) =
        (tau (lowV (mulV CFSG.KD.Fi23Q.SubPW CFSG.KD.Fi23Q.SubCJ 9 ai aj) 4))⁻¹ *
          (tau ai * tau aj) := by
      rw [hP]
      group
    have hq : eps (Nat.shiftRight (mulV CFSG.KD.Fi23Q.SubPW CFSG.KD.Fi23Q.SubCJ 9 aj ai) 8) =
        (tau (lowV (mulV CFSG.KD.Fi23Q.SubPW CFSG.KD.Fi23Q.SubCJ 9 ai aj) 4))⁻¹ *
          (tau aj * tau ai) := by
      rw [hQ]
      group
    rw [hp, hq]
    calc _ = (tau (lowV (mulV CFSG.KD.Fi23Q.SubPW CFSG.KD.Fi23Q.SubCJ 9 ai aj) 4))⁻¹ *
          (tau ai * eps wi * (tau aj * eps wj)) := by group
      _ = (tau (lowV (mulV CFSG.KD.Fi23Q.SubPW CFSG.KD.Fi23Q.SubCJ 9 ai aj) 4))⁻¹ *
          (tau aj * eps wj * (tau ai * eps wi)) := by rw [hc]
      _ = _ := by group
  rw [ei, ej, ← eps_add oi hwj, ← eps_add hP5 (ok5_add3 oi hwj), ← eps_add oj hwi,
    ← eps_add hQ5 (ok5_add3 oj hwi)] at k
  have k2 := eps_inj (ok5_add3 hP5 (ok5_add3 oi hwj)) (ok5_add3 hQ5 (ok5_add3 oj hwi)) k
  have hs := ok5_sub3 hP5 hQ5
  have e : add3 (sub3 (Nat.shiftRight (mulV CFSG.KD.Fi23Q.SubPW CFSG.KD.Fi23Q.SubCJ 9 ai aj) 8)
      (Nat.shiftRight (mulV CFSG.KD.Fi23Q.SubPW CFSG.KD.Fi23Q.SubCJ 9 aj ai) 8))
      (add3 (mC CFSG.KD.Fi23Q.clsMt aj wi) wj) = add3 (mC CFSG.KD.Fi23Q.clsMt ai wj) wi := by
    refine eq_of_dg (add3_lt _ _) (add3_lt _ _) fun c hc => ?_
    have kc := congrArg (fun z => dg z c) k2
    rw [dg_add3 hc (hP5.2 c hc) ((ok5_add3 oi hwj).2 c hc), dg_add3 hc (oi.2 c hc) (hwj.2 c hc),
      dg_add3 hc (hQ5.2 c hc) ((ok5_add3 oj hwi).2 c hc), dg_add3 hc (oj.2 c hc) (hwi.2 c hc)] at kc
    rw [dg_add3 hc (hs.2 c hc) ((ok5_add3 oi hwj).2 c hc), dg_add3 hc (oi.2 c hc) (hwj.2 c hc),
      dg_add3 hc (oj.2 c hc) (hwi.2 c hc), dg_sub3 hc (hP5.2 c hc) (hQ5.2 c hc)]
    have := hP5.2 c hc
    have := hQ5.2 c hc
    have := oi.2 c hc
    have := oj.2 c hc
    have := hwi.2 c hc
    have := hwj.2 c hc
    omega
  unfold commE
  rw [e, Nat.beq_refl]

theorem cls_pivot {D : Subgroup CFSG.Sporadic.Fi23.J} {a w c p : ℕ} (hw : Ok5 w) (hc5 : Ok5 c) (hp : p < 5)
    (hcp : dg c p = 1) (hx : tau a * eps w ∈ D) (hcD : eps c ∈ D) :
    ∃ w', Ok5 w' ∧ dg w' p = 0 ∧ tau a * eps w' ∈ D := by
  have he : (3 - dg w p) % 3 < 3 := Nat.mod_lt _ (by norm_num)
  have hs := ok5_smul3 (e := (3 - dg w p) % 3) hc5
  refine ⟨add3 w (smul3 ((3 - dg w p) % 3) c), ok5_add3 hw hs, ?_, ?_⟩
  · rw [dg_add3 hp (hw.2 p hp) (hs.2 p hp), dg_smul3 hp hcp he]
    have := hw.2 p hp
    omega
  · rw [eps_add hw hs, eps_smul' he hc5, ← mul_assoc]
    exact D.mul_mem hx (D.pow_mem hcD _)

theorem cls_inC1 {D : Subgroup CFSG.Sporadic.Fi23.J} {c d : ℕ} (hc5 : Ok5 c) (hcD : eps c ∈ D)
    (h : inC1 c d = true) : eps d ∈ D := by
  simp only [inC1, CFSG.KS.PK.bIf_eq] at h
  by_cases h0 : Nat.beq d 0 = true
  · rw [Nat.eq_of_beq_eq_true h0, eps_zero]
    exact D.one_mem
  rw [if_neg h0] at h
  by_cases h1 : Nat.beq d c = true
  · rw [Nat.eq_of_beq_eq_true h1]
    exact hcD
  rw [if_neg h1] at h
  rw [Nat.eq_of_beq_eq_true h, eps_add hc5 hc5]
  exact D.mul_mem hcD hcD

theorem cls_cover {D : Subgroup CFSG.Sporadic.Fi23.J} {a w c : ℕ} (hw : Ok5 w) (hc5 : Ok5 c) (hcD : eps c ∈ D)
    (hx : tau a * eps w ∈ D) (h : covE CFSG.KD.Fi23Q.npV (inC1 c) a w = true) :
    ∃ k < 131, nv sE 9 (CFSG.KD.Fi23Q.npV.getD k 0) ∈ D := by
  obtain ⟨k, hk, hkl, hkc⟩ := covE_iff.1 h
  rw [npV_len] at hk
  obtain ⟨u5, e⟩ := cert_split hk
  refine ⟨k, hk, ?_⟩
  rw [e, hkl]
  exact cls_mem_cover hw u5 hx (cls_inC1 hc5 hcD hkc)

theorem mem_E_of_top {x : CFSG.Sporadic.Fi23.J} (hx : x ∈ SubS) (h : topS x = 0) :
    Ok5 (Nat.shiftRight (vS x) 8) ∧ x = eps (Nat.shiftRight (vS x) 8) := by
  obtain ⟨w, hw, rfl⟩ := (topS_eq_zero hx).1 h
  rw [vS_eps hw]
  exact ⟨hw, rfl⟩

theorem card_F35 : Nat.card (Fin 5 → ZMod 3) = 243 := by
  rw [Nat.card_eq_fintype_card]
  simp [ZMod.card]

theorem cls_hyper {D : Subgroup CFSG.Sporadic.Fi23.J} (hDS : D ≤ SubS) (hE : ∀ x ∈ D, topS x = 0)
    (hD : Nat.card D = 81) : ∃ k < 131, nv sE 9 (CFSG.KD.Fi23Q.npV.getD k 0) ∈ D := by
  classical
  have hP3 : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hx : ∀ x ∈ D, Ok5 (Nat.shiftRight (vS x) 8) ∧ x = eps (Nat.shiftRight (vS x) 8) :=
    fun x h => mem_E_of_top (hDS h) (hE x h)
  obtain ⟨f, hfd⟩ : ∃ f : D → (Fin 5 → ZMod 3),
      ∀ x, f x = dgv (Nat.shiftRight (vS (x : J)) 8) := ⟨_, fun _ => rfl⟩
  have hf : Function.Injective f := by
    intro x y e
    obtain ⟨ox, ex⟩ := hx x x.2
    obtain ⟨oy, ey⟩ := hx y y.2
    rw [hfd, hfd] at e
    apply Subtype.ext
    rw [ex, ey, dgv_inj ox oy e]
  have hfm : ∀ x y : D, f (x * y) = f x + f y := by
    intro x y
    obtain ⟨ox, ex⟩ := hx x x.2
    obtain ⟨oy, ey⟩ := hx y y.2
    have e : ((x * y : D) : J) =
        eps (add3 (Nat.shiftRight (vS (x : J)) 8) (Nat.shiftRight (vS (y : J)) 8)) := by
      rw [Subgroup.coe_mul, eps_add ox oy, ← ex, ← ey]
    simp only [hfd]
    rw [e, vS_eps (ok5_add3 ox oy), dgv_add ox oy]
  have hf1 : f 1 = 0 := by
    have e : ((1 : D) : J) = eps 0 := by
      rw [eps_zero]
      rfl
    rw [hfd, e, vS_eps ok5_zero, dgv_zero]
  have hfi : ∀ x : D, f x⁻¹ = -f x := by
    intro x
    obtain ⟨ox, ex⟩ := hx x x.2
    have e : ((x⁻¹ : D) : J) = eps (neg3 (Nat.shiftRight (vS (x : J)) 8)) := by
      rw [Subgroup.coe_inv, eps_neg ox, ← ex]
    simp only [hfd]
    rw [e, vS_eps (ok5_neg3 ox), dgv_neg ox]
  let W : AddSubgroup (Fin 5 → ZMod 3) :=
    { carrier := Set.range f
      add_mem' := by
        rintro _ _ ⟨x, rfl⟩ ⟨y, rfl⟩
        exact ⟨x * y, hfm x y⟩
      zero_mem' := ⟨1, hf1⟩
      neg_mem' := by
        rintro _ ⟨x, rfl⟩
        exact ⟨x⁻¹, hfi x⟩ }
  have hWm : ∀ v, v ∈ W ↔ ∃ x, f x = v := fun v => Iff.rfl
  have hWc : Nat.card W = 81 := by
    rw [← hD, ← Nat.card_range_of_injective hf]
    rfl
  have hne : AddSubgroup.toZModSubmodule 3 W ≠ ⊤ := by
    intro h
    have htop : W = ⊤ := (AddSubgroup.eq_top_iff' W).2 fun v => by
      have : v ∈ AddSubgroup.toZModSubmodule 3 W := by
        rw [h]
        exact Submodule.mem_top
      exact this
    have hc := AddSubgroup.card_top (G := Fin 5 → ZMod 3)
    rw [← htop, hWc, card_F35] at hc
    omega
  obtain ⟨φ, hφ0, hle⟩ := Submodule.exists_le_ker_of_lt_top _ (lt_top_iff_ne_top.2 hne)
  obtain ⟨fv, hfv⟩ : ∃ fv : Fin 5 → ZMod 3, ∀ v, φ v = ∑ c, v c * fv c :=
    ⟨fun c => φ fun j => if c = j then 1 else 0, fun v => by
      rw [LinearMap.pi_apply_eq_sum_univ φ v]
      simp only [smul_eq_mul]⟩
  have hb : ∀ c, (fv c).val < 3 := fun c => ZMod.val_lt _
  have b0 := hb 0
  have b1 := hb 1
  have b2 := hb 2
  have b3 := hb 3
  have b4 := hb 4
  obtain ⟨F, hF⟩ : ∃ F : ℕ, F = (fv 0).val + 4 * ((fv 1).val + 4 * ((fv 2).val +
      4 * ((fv 3).val + 4 * (fv 4).val))) := ⟨_, rfl⟩
  have d0 : dg F 0 = (fv 0).val := by rw [dg_eq, hF]; norm_num <;> omega
  have d1 : dg F 1 = (fv 1).val := by rw [dg_eq, hF]; norm_num <;> omega
  have d2 : dg F 2 = (fv 2).val := by rw [dg_eq, hF]; norm_num <;> omega
  have d3 : dg F 3 = (fv 3).val := by rw [dg_eq, hF]; norm_num <;> omega
  have d4 : dg F 4 = (fv 4).val := by rw [dg_eq, hF]; norm_num <;> omega
  have hFd : ∀ c : Fin 5, dg F c = (fv c).val := by
    intro c
    fin_cases c
    exacts [d0, d1, d2, d3, d4]
  have hF5 : Ok5 F := ⟨by rw [hF]; norm_num; omega, fun c hc => by
    have := hFd ⟨c, hc⟩
    simp only at this
    rw [this]
    exact hb _⟩
  have hF0 : F ≠ 0 := by
    intro h0
    apply hφ0
    have z0 : (fv 0).val = 0 := by omega
    have z1 : (fv 1).val = 0 := by omega
    have z2 : (fv 2).val = 0 := by omega
    have z3 : (fv 3).val = 0 := by omega
    have z4 : (fv 4).val = 0 := by omega
    have hz : ∀ c, fv c = 0 := by
      intro c
      rw [← ZMod.val_eq_zero]
      fin_cases c
      exacts [z0, z1, z2, z3, z4]
    refine LinearMap.ext fun v => ?_
    rw [hfv, LinearMap.zero_apply]
    exact Finset.sum_eq_zero fun c _ => by rw [hz c, mul_zero]
  obtain ⟨iF, hiF, hvF⟩ := ok5_vec3 hF5
  obtain ⟨k, hk, hkl, hdot⟩ := clsHK_sound CFSG.KD.Fi23Q.clsH_ok iF hiF (by rw [hvF]; exact hF0)
  rw [hvF, dot3_eq] at hdot
  rw [npV_len] at hk
  obtain ⟨u5, e⟩ := cert_split hk
  have hφu : φ (dgv (Nat.shiftRight (CFSG.KD.Fi23Q.npV.getD k 0) 8)) = 0 := by
    have hc := congrArg (fun n : ℕ => (n : ZMod 3)) hdot
    simp only [ZMod.natCast_mod, Nat.cast_add, Nat.cast_mul, Nat.cast_zero, zero_add] at hc
    have hfvF : ∀ c : Fin 5, fv c = ((dg F c : ℕ) : ZMod 3) := fun c => by
      rw [hFd c, ZMod.natCast_zmod_val]
    have v0 : ((0 : Fin 5) : ℕ) = 0 := rfl
    have v1 : ((1 : Fin 5) : ℕ) = 1 := rfl
    have v2 : ((2 : Fin 5) : ℕ) = 2 := rfl
    have v3 : ((3 : Fin 5) : ℕ) = 3 := rfl
    have v4 : ((4 : Fin 5) : ℕ) = 4 := rfl
    rw [hfv, Fin.sum_univ_five]
    simp only [dgv, hfvF, v0, v1, v2, v3, v4]
    linear_combination hc
  have hWK : W ≤ (LinearMap.ker φ).toAddSubgroup := fun v hv => hle hv
  have hKc : Nat.card (LinearMap.ker φ).toAddSubgroup = 81 := by
    have h1 := AddSubgroup.card_dvd_of_le hWK
    have h2 := AddSubgroup.card_addSubgroup_dvd_card (LinearMap.ker φ).toAddSubgroup
    rw [card_F35] at h2
    rw [hWc] at h1
    have h3 : Nat.card (LinearMap.ker φ).toAddSubgroup ≠ 243 := by
      intro h
      apply hφ0
      have ht := AddSubgroup.eq_top_of_card_eq _ (h.trans card_F35.symm)
      refine LinearMap.ext fun v => ?_
      have hv : v ∈ (LinearMap.ker φ).toAddSubgroup := by
        rw [ht]
        exact AddSubgroup.mem_top v
      exact LinearMap.mem_ker.1 hv
    obtain ⟨m, hm⟩ := h1
    rw [hm] at h2 h3 ⊢
    have hm3 : m ≤ 3 := by
      have := Nat.le_of_dvd (by norm_num) h2
      omega
    interval_cases m <;> first | omega | norm_num at h2
  have hWeq : W = (LinearMap.ker φ).toAddSubgroup :=
    AddSubgroup.eq_of_le_of_card_ge hWK (by rw [hKc, hWc])
  have hu : dgv (Nat.shiftRight (CFSG.KD.Fi23Q.npV.getD k 0) 8) ∈ W := by
    rw [hWeq]
    exact hφu
  obtain ⟨x, hxu⟩ := (hWm _).1 hu
  obtain ⟨ox, ex⟩ := hx x x.2
  rw [hfd] at hxu
  have hux := dgv_inj ox u5 hxu
  refine ⟨k, hk, ?_⟩
  rw [e, hkl, tau_zero, one_mul, ← hux, ← ex]
  exact x.2

theorem cls_cert {D : Subgroup CFSG.Sporadic.Fi23.J} (hDS : D ≤ SubS) (hc : ∀ x ∈ D, ∀ y ∈ D, x * y = y * x)
    (h3 : ∀ x ∈ D, x ^ 3 = 1) (hD : Nat.card D = 81) :
    ∃ k < 131, nv sE 9 (CFSG.KD.Fi23Q.npV.getD k 0) ∈ D := by
  by_cases h0 : ∀ x ∈ D, topS x = 0
  · exact cls_hyper hDS h0 hD
  push Not at h0
  obtain ⟨x0, hx0, hx0t⟩ := h0
  obtain ⟨i, hi, hT⟩ := top_mask hDS hc h3
  have hL := clsLK_sound CFSG.KD.Fi23Q.clsLt_ok
  have hi1 : 1 ≤ i := by
    rcases Nat.eq_zero_or_pos i with rfl | h
    · exfalso
      have ha := (hT (topS x0)).2 ⟨x0, hx0, rfl⟩
      rw [hL.1, bitM_iff] at ha
      exact hx0t ((testBit_one_shiftLeft 0 _).1 ha)
    · exact h
  obtain ⟨hKL, -, hK⟩ := clsKK_sound CFSG.KD.Fi23Q.clsKd_ok
  have hiK : i < CFSG.KD.Fi23Q.clsK.length := by rw [hKL]; exact hi
  have hmem : ∀ {a}, bitM (CFSG.KD.Fi23Q.clsL.getD i 0) a = true →
      ∃ w, Ok4 a ∧ Ok5 w ∧ tau a * eps w ∈ D := by
    intro a ha
    obtain ⟨x, hx, rfl⟩ := (hT a).1 ha
    obtain ⟨b, w, hb, hw, ex⟩ := te_of_mem (hDS hx)
    have hxt : topS x = b := by rw [ex, topS_te hb hw]
    refine ⟨w, hxt ▸ hb, hw, ?_⟩
    rw [hxt, ← ex]
    exact hx
  have hE : ∀ {w}, Ok5 w → fixB CFSG.KD.Fi23Q.clsMt (CFSG.KD.Fi23Q.clsB.getD i 0) w = true →
      eps w ∈ D := fun hw hf => (inter_E hDS hc hD hi1 hi hT hw).2 hf
  obtain ⟨k1, k3⟩ := hK i hi1 hiK
  have hcase : CFSG.KD.Fi23Q.clsK.getD i 0 = 1 ∨ CFSG.KD.Fi23Q.clsK.getD i 0 = 2 ∨
      CFSG.KD.Fi23Q.clsK.getD i 0 = 3 := by omega
  rcases hcase with h | h | h
  ·
    obtain ⟨hg, hl, hf⟩ := clsGK_sound CFSG.KD.Fi23Q.clsG_ok i hiK h
    rw [npV_len] at hg
    obtain ⟨u5, e⟩ := cert_split hg
    refine ⟨_, hg, ?_⟩
    rw [e, hl, tau_zero, one_mul]
    exact hE u5 hf
  ·
    obtain ⟨hb, hl3, hcov⟩ := bad2_sound (clsAK_sound CFSG.KD.Fi23Q.clsA_ok i hiK h)
    obtain ⟨w, ha, hw, hx⟩ := hmem hb
    have hcu := cls_cube ha hw hl3 (h3 _ hx)
    obtain ⟨iw, hiw, rfl⟩ := ok5_vec3 hw
    obtain ⟨k, hk, hkl, hkf⟩ := hcov iw hiw hcu
    rw [npV_len] at hk
    obtain ⟨u5, e⟩ := cert_split hk
    refine ⟨k, hk, ?_⟩
    rw [e, hkl]
    exact cls_mem_cover hw u5 hx (hE (ok5_sub3 u5 hw) hkf)
  ·
    obtain ⟨b1, b2, b3, -, hcp, hp, hcf, l1, l2, l3, m12, m13, m23, hL3⟩ :=
      bad3_sound (clsBK_sound CFSG.KD.Fi23Q.clsBt_ok i hiK h)
    have hc5 : Ok5 (CFSG.KD.Fi23Q.clsD3.getD 3 0) := by
      unfold Ok5
      decide +kernel
    have hcD := hE hc5 hcf
    obtain ⟨w1, a1, hw1, hx1⟩ := hmem b1
    obtain ⟨w2, a2, hw2, hx2⟩ := hmem b2
    obtain ⟨w3, a3, hw3, hx3⟩ := hmem b3
    obtain ⟨v1, hv1, hp1, hy1⟩ := cls_pivot hw1 hc5 hp hcp hx1 hcD
    obtain ⟨v2, hv2, hp2, hy2⟩ := cls_pivot hw2 hc5 hp hcp hx2 hcD
    obtain ⟨v3, hv3, hp3, hy3⟩ := cls_pivot hw3 hc5 hp hcp hx3 hcD
    have c1 := cls_cube a1 hv1 l1 (h3 _ hy1)
    have c2 := cls_cube a2 hv2 l2 (h3 _ hy2)
    have c3 := cls_cube a3 hv3 l3 (h3 _ hy3)
    have g12 := cls_comm a1 a2 hv1 hv2 m12 (hc _ hy1 _ hy2)
    have g13 := cls_comm a1 a3 hv1 hv3 m13 (hc _ hy1 _ hy3)
    have g23 := cls_comm a2 a3 hv2 hv3 m23 (hc _ hy2 _ hy3)
    obtain ⟨i1, hi1', rfl⟩ := ok5_vec3 hv1
    obtain ⟨i2, hi2', rfl⟩ := ok5_vec3 hv2
    obtain ⟨i3, hi3', rfl⟩ := ok5_vec3 hv3
    rcases bad3L_sound hL3 i1 hi1' i2 hi2' i3 hi3' hp1 hp2 hp3 c1 c2 c3 g12 g13 g23 with
      hv | hv | hv
    · exact cls_cover hv1 hc5 hcD hy1 hv
    · exact cls_cover hv2 hc5 hcD hy2 hv
    · exact cls_cover hv3 hc5 hcD hy3 hv

theorem sub_pure :
    ∃ S : Subgroup CFSG.Sporadic.Fi23.J, S ≤ Subgroup.centralizer ({conjPt 770} : Set CFSG.Sporadic.Fi23.J) ∧ Nat.card S = 3 ^ 9 ∧
      ∀ D ≤ S, CFSG.Open.IsElemAbelian 3 D → Nat.card D = 3 ^ 4 →
        ∃ x ∈ D, x ≠ 1 ∧ (IsConj x (t3 0) ∨ IsConj x (t3 2)) := by
  refine ⟨SubS, S_le_centralizer, card_S, fun D hDS hD hcard => ?_⟩
  have hc := cls_comm_of hD.1
  obtain ⟨k, hk, hmem⟩ := cls_cert hDS hc hD.2 (by rw [hcard]; norm_num)
  exact ⟨_, hmem, (np_conj hk).2⟩

end OnJ

end CertificateChecks.KernelFi23Q

end
