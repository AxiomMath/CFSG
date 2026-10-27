
module

public import Certificates.Kernel.L34Cov.AlphaClChecks
public import Certificates.Kernel.L34Cov.AlphaGenGlue

public section

namespace CertificateChecks.KernelL34Cov

open CFSG.KC CFSG.KC.L34Cov CFSG.KC.L34W CFSG.LieType.Multipliers CFSG.LieType.Multipliers.L34
open CFSG.Certificates.CosetEnumeration CFSG.Certificates.L34Cov CFSG.CosetTable Subgroup
open CFSG.ComponentClassification.GrSLit.L34Facts CFSG.ComponentClassification.GrSLit.L34Facts.Real
open CertificateChecks.KernelL34W

#kc_forall_tree ch22219acl_all (fun i => alClOK VT CFSG.KD.L34F4a.Tab CFSG.KD.L34F4b.Tab T1X.F
  FW AlX.F (UAC.codes.getD i []) (UBC.codes.getD i []) i = true) 36
  CertificateChecks.KernelL34Cov.ch22219acl.a

noncomputable abbrev zw (e : ℕ) : Cover :=
  z₁ ^ (e % 48 / 12) * z₂ ^ (e % 12 / 3) * z₃ ^ (e % 3)

theorem comp_add {n : ℕ} (hn : n ∣ 12) {t x y z eA eB : ℕ} {E₀ E₁ : ℤ}
    (h₀ : (eA : ℤ) ≡ E₀ [ZMOD 12]) (h₁ : (eB : ℤ) ≡ E₁ [ZMOD 12])
    (ht : (t : ZMod n) = (x : ZMod n) + (eA : ZMod n) * y + (eB : ZMod n) * z) :
    Multiplicative.ofAdd (x : ZMod n) * (Multiplicative.ofAdd (y : ZMod n)) ^ E₀ *
      (Multiplicative.ofAdd (z : ZMod n)) ^ E₁ = Multiplicative.ofAdd (t : ZMod n) := by
  rw [← ofAdd_zsmul, ← ofAdd_zsmul, ← ofAdd_add, ← ofAdd_add]
  congr 1
  obtain ⟨a, ha⟩ := Int.ModEq.dvd h₀
  obtain ⟨b, hb⟩ := Int.ModEq.dvd h₁
  have eE₀ : E₀ = eA + 12 * a := by linarith
  have eE₁ : E₁ = eB + 12 * b := by linarith
  have h12 : (12 : ZMod n) = 0 := by
    have := (ZMod.natCast_eq_zero_iff 12 n).2 hn
    exact_mod_cast this
  rw [ht, eE₀, eE₁, zsmul_eq_mul, zsmul_eq_mul]
  push_cast
  linear_combination ((a : ZMod n) * y + b * z) * h12

theorem zadd_spec {v vA vB eA eB : ℕ} {E₀ E₁ : ℤ}
    (h₀ : (eA : ℤ) ≡ E₀ [ZMOD 12]) (h₁ : (eB : ℤ) ≡ E₁ [ZMOD 12]) :
    zc v * zc vA ^ E₀ * zc vB ^ E₁ = zc (zaddC v vA vB eA eB) := by
  set t₁ := (v % 4 + eA * (vA % 4) + eB * (vB % 4)) % 4 with ht₁
  set t₂ := (v / 4 % 4 + eA * (vA / 4 % 4) + eB * (vB / 4 % 4)) % 4 with ht₂
  set t₃ := (v / 16 + eA * (vA / 16) + eB * (vB / 16)) % 3 with ht₃
  have hc : zaddC v vA vB eA eB = t₁ + 4 * t₂ + 16 * t₃ := rfl
  have l₁ : t₁ < 4 := Nat.mod_lt _ (by norm_num)
  have l₂ : t₂ < 4 := Nat.mod_lt _ (by norm_num)
  have l₃ : t₃ < 3 := Nat.mod_lt _ (by norm_num)
  have c₁ : (t₁ + 4 * t₂ + 16 * t₃) % 4 = t₁ := by omega
  have c₂ : (t₁ + 4 * t₂ + 16 * t₃) / 4 % 4 = t₂ := by omega
  have c₃ : (t₁ + 4 * t₂ + 16 * t₃) / 16 = t₃ := by omega
  have hz : zc (t₁ + 4 * t₂ + 16 * t₃) = z₁ ^ t₁ * z₂ ^ t₂ * z₃ ^ t₃ := by
    rw [zc, c₁, c₂, c₃]
  rw [hc, hz, zc_eq_zHom v, zc_eq_zHom vA, zc_eq_zHom vB, zpow3_eq_zHom, ← map_zpow,
    ← map_zpow, ← map_mul, ← map_mul]
  congr 1
  refine Prod.ext ?_ (Prod.ext ?_ ?_)
  · refine comp_add (by norm_num) h₀ h₁ ?_
    rw [ht₁, ZMod.natCast_mod]
    push_cast [ZMod.natCast_mod]
    rfl
  · refine comp_add (by norm_num) h₀ h₁ ?_
    rw [ht₂, ZMod.natCast_mod]
    push_cast [ZMod.natCast_mod]
    rfl
  · refine comp_add (by norm_num) h₀ h₁ ?_
    rw [ht₃, ZMod.natCast_mod]
    push_cast
    rfl

theorem comp_lab {n : ℕ} {d n' a b c₁ c₂ c₃ x₁ x₂ x₃ : ℕ}
    (h : (d + c₁ * (x₁ % n) + c₂ * (x₂ % n) + c₃ * (x₃ % n)) % n = (n' + a + b) % n) :
    Multiplicative.ofAdd (d : ZMod n) * ((Multiplicative.ofAdd (x₁ : ZMod n)) ^ c₁ *
      (Multiplicative.ofAdd (x₂ : ZMod n)) ^ c₂ * (Multiplicative.ofAdd (x₃ : ZMod n)) ^ c₃) =
      Multiplicative.ofAdd (n' : ZMod n) * Multiplicative.ofAdd (a : ZMod n) *
        Multiplicative.ofAdd (b : ZMod n) := by
  rw [← ofAdd_nsmul, ← ofAdd_nsmul, ← ofAdd_nsmul, ← ofAdd_add, ← ofAdd_add, ← ofAdd_add,
    ← ofAdd_add, ← ofAdd_add]
  congr 1
  have e := (ZMod.natCast_eq_natCast_iff' _ _ n).2 h
  push_cast [ZMod.natCast_mod] at e
  rw [nsmul_eq_mul, nsmul_eq_mul, nsmul_eq_mul]
  linear_combination e

theorem zlab_eq {d n a b c α₁ α₂ α₃ : ℕ}
    (h : zlabOK d n a b c α₁ α₂ α₃ = true) :
    zw d * (zc α₁ ^ (c % 48 / 12) * zc α₂ ^ (c % 12 / 3) * zc α₃ ^ (c % 3)) =
      zw n * zw a * zw b := by
  unfold zlabOK at h
  simp only [andB_eq, Bool.and_eq_true] at h
  obtain ⟨h1, h2, h3⟩ := h
  have e1 := Nat.eq_of_beq_eq_true h1
  have e2 := Nat.eq_of_beq_eq_true h2
  have e3 := Nat.eq_of_beq_eq_true h3
  rw [zw, zw, zw, zw, zpow3_eq_zHom, zpow3_eq_zHom, zpow3_eq_zHom, zpow3_eq_zHom, zc_eq_zHom,
    zc_eq_zHom, zc_eq_zHom, ← map_pow, ← map_pow, ← map_pow, ← map_mul, ← map_mul, ← map_mul,
    ← map_mul, ← map_mul]
  congr 1
  refine Prod.ext ?_ (Prod.ext ?_ ?_)
  · exact comp_lab (n := 4) e1
  · exact comp_lab (n := 4) e2
  · have e3' : (d % 3 + c % 48 / 12 * (α₁ / 16 % 3) + c % 12 / 3 * (α₂ / 16 % 3) +
        c % 3 * (α₃ / 16 % 3)) % 3 = (n % 3 + a % 3 + b % 3) % 3 := by
      rw [← e3]
      simp [Nat.add_mod, Nat.mul_mod]
    have := comp_lab (n := 3) e3'
    simpa [ZMod.natCast_mod] using this

theorem rearr2 {G : Type*} [Group G] (x y za zb w : G) (hza : za ∈ center G) :
    x * za * (y * zb) * w = x * y * (za * zb * w) := by
  have e : za * y = y * za := (mem_center_iff.1 hza y).symm
  calc x * za * (y * zb) * w = x * (za * y) * zb * w := by group
    _ = x * (y * za) * zb * w := by rw [e]
    _ = _ := by group

theorem zEnt_spec {α : ℕ} (h : α < 48) :
    (quad (zEnt α)).1 = 0 ∧ cv (zOf (quad (zEnt α))) = zc α := by
  have hz : zEnt α = 12 * (α % 4) + 3 * (α / 4 % 4) + α / 16 := rfl
  have lp : α % 4 < 4 := Nat.mod_lt _ (by norm_num)
  have lq : α / 4 % 4 < 4 := Nat.mod_lt _ (by norm_num)
  have lr : α / 16 < 3 := by omega
  have hzc : zc α = z₁ ^ (α % 4) * z₂ ^ (α / 4 % 4) * z₃ ^ (α / 16) := rfl
  rw [hzc]
  generalize α % 4 = p at hz lp ⊢
  generalize α / 4 % 4 = q at hz lq ⊢
  generalize α / 16 = r at hz lr ⊢
  have e1 : zEnt α / 48 = 0 := by rw [hz]; omega
  have e2 : zEnt α % 48 / 12 = p := by rw [hz]; omega
  have e3 : zEnt α % 12 / 3 = q := by rw [hz]; omega
  have e4 : zEnt α % 3 = r := by rw [hz]; omega
  refine ⟨e1, ?_⟩
  rw [cv_zOf]
  simp only [quad, e2, e3, e4]

theorem alpha_spec_k {i : ℕ} (hi : i < 36) :
    (∀ k < 64, cv (substWord (aut i) (tw k)) =
      cv (tw (alphaEntry i k).1) * cv (zOf (alphaEntry i k))) ∧
    ∀ j < 2, (alphaEntry i (64 + j)).1 = 0 ∧
      cv (substWord (aut i) (zGen j)) = cv (zOf (alphaEntry i (64 + j))) := by
  obtain ⟨α, hα, hα'⟩ := exists_alphaLift hi
  have h := ch22219acl_all i hi
  have hcA : (uA i).map letterCode = UAC.codes.getD i [] := by
    rw [(uA_eq i).1]
    exact map_letterCode_decL (uA_eq i).2
  have hcB : (uB i).map letterCode = UBC.codes.getD i [] := by
    rw [(uB_eq i).1]
    exact map_letterCode_decL (uB_eq i).2
  rw [← hcA, ← hcB] at h
  unfold alClOK at h
  rw [bindB_eq, bindB_eq, bindB_eq, bindB_eq, bindB_eq] at h
  generalize zvC VT CFSG.KD.L34F4a.Tab CFSG.KD.L34F4b.Tab (invW ((uA i).map letterCode) ++
    substC [(uA i).map letterCode, (uB i).map letterCode] (FW.getD 0 [])) = vA at h
  generalize zvC VT CFSG.KD.L34F4a.Tab CFSG.KD.L34F4b.Tab (invW ((uB i).map letterCode) ++
    substC [(uA i).map letterCode, (uB i).map letterCode] (FW.getD 1 [])) = vB at h
  generalize zvC VT CFSG.KD.L34F4a.Tab CFSG.KD.L34F4b.Tab
    (substC [(uA i).map letterCode, (uB i).map letterCode] (FW.getD 10 [])) = v₁ at h
  generalize zvC VT CFSG.KD.L34F4a.Tab CFSG.KD.L34F4b.Tab
    (substC [(uA i).map letterCode, (uB i).map letterCode] (FW.getD 11 [])) = v₂ at h
  generalize zvC VT CFSG.KD.L34F4a.Tab CFSG.KD.L34F4b.Tab
    (substC [(uA i).map letterCode, (uB i).map letterCode] (FW.getD 12 [])) = v₃ at h
  simp only [andB_eq, Bool.and_eq_true] at h
  obtain ⟨hzA, hzB, hz₁, hz₂, hz₃, h0, hcl⟩ := h
  rw [bindB_eq, bindB_eq, bindB_eq] at hcl
  have zA : (cv (uA i))⁻¹ * cv ((aut i).getD 0 []) = zc vA :=
    zeta_eq (uA i) (uB i) 0 (by norm_num) hzA
  have zB : (cv (uB i))⁻¹ * cv ((aut i).getD 1 []) = zc vB :=
    zeta_eq (uA i) (uB i) 1 (by norm_num) hzB
  have hU : [(uA i).map letterCode, (uB i).map letterCode] =
      [uA i, uB i].map (List.map letterCode) := rfl
  have hαz : ∀ (u : List (Fin 2 × Bool)) (k : ℕ) {v : ℕ}, FW.getD k [] = u.map letterCode →
      zvOK VT CFSG.KD.L34F4a.Tab CFSG.KD.L34F4b.Tab
        (substC [(uA i).map letterCode, (uB i).map letterCode] (FW.getD k [])) v = true →
      α (cv u) = zc (zaddC v vA vB (eN 0 (FW.getD k [])) (eN 1 (FW.getD k []))) := by
    intro u k v hk hz
    rw [hk, hU, ← map_letterCode_substWord] at hz
    have e0 := eN_modEq 0 u
    have e1 := eN_modEq 1 u
    rw [Fin.val_zero] at e0
    rw [Fin.val_one] at e1
    rw [hα', zA, zB, cv_of_zvOK vt_k modelA modelB hz, hk]
    exact zadd_spec e0 e1
  have az₁ := hαz zOne 10 rfl hz₁
  have az₂ := hαz zTwo 11 rfl hz₂
  have az₃ := hαz zThree 12 rfl hz₃
  generalize zaddC v₁ vA vB (eN 0 (FW.getD 10 [])) (eN 1 (FW.getD 10 [])) = α₁ at hcl az₁
  generalize zaddC v₂ vA vB (eN 0 (FW.getD 11 [])) (eN 1 (FW.getD 11 [])) = α₂ at hcl az₂
  generalize zaddC v₃ vA vB (eN 0 (FW.getD 12 [])) (eN 1 (FW.getD 12 [])) = α₃ at hcl az₃
  simp only [andB_eq, Bool.and_eq_true, Nat.blt_eq] at hcl
  obtain ⟨⟨l₁, h64⟩, ⟨l₂, h65⟩, hcl⟩ := hcl
  have hb : ∀ l < 64, ent AlX.F i l / 48 < 64 := fun l hl => by
    have := bounds_A bounds_k hi (show l < 66 by omega)
    omega
  have key : ∀ l < 64, α (cv (tw l)) = cv (tw (ent AlX.F i l / 48)) * zw (ent AlX.F i l) := by
    refine reach_all reach_k _ ?_ ?_
    · have e0 : ent AlX.F i 0 = 0 := Nat.eq_of_beq_eq_true h0
      have t0 : cv (tw 0) = 1 := by rw [(tw_eq 0).1]; rfl
      rw [e0, t0, map_one]
      simp [zw]
    · intro l hl hS g hg
      have hg64 := gens_lt g hg
      have t1 : cv (tw l) * cv (tw g) = cv (tw (ent T1X.F l g / 48)) * zw (ent T1X.F l g) := by
        have := (t1_spec_k l hl g hg64).2
        rw [t1_quad hl hg64, cv_zOf] at this
        exact this
      have gen : α (cv (tw g)) = cv (tw (ent AlX.F i g / 48)) * zw (ent AlX.F i g) := by
        rw [hα, alpha_gen_spec hi hg, alOf i g hi (by omega), cv_zOf]
        rfl
      have αzc : α (zw (ent T1X.F l g)) = zc α₁ ^ (ent T1X.F l g % 48 / 12) *
          zc α₂ ^ (ent T1X.F l g % 12 / 3) * zc α₃ ^ (ent T1X.F l g % 3) := by
        simp only [zw, map_mul, map_pow, az₁, az₂, az₃]
      have htw : cv (tw (ent T1X.F l g / 48)) = cv (tw l) * cv (tw g) * (zw (ent T1X.F l g))⁻¹ := by
        rw [t1]
        group
      have hs := CFSG.Certificates.Mono.allR_spec hcl l (Nat.zero_le _) hl
      unfold clStepsOK at hs
      simp only [andB_eq, Bool.and_eq_true] at hs
      have hg' : clStepOK T1X.F AlX.F i l g α₁ α₂ α₃ = true := by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
        rcases hg with rfl | rfl | rfl | rfl
        · exact hs.1
        · exact hs.2.1
        · exact hs.2.2.1
        · exact hs.2.2.2
      unfold clStepOK at hg'
      simp only [bindB_eq, andB_eq, Bool.and_eq_true] at hg'
      obtain ⟨hidx, hlab⟩ := hg'
      have hlab' := zlab_eq hlab
      have hab := (t1_spec_k _ (hb l hl) _ (hb g hg64)).2
      rw [t1_quad (hb l hl) (hb g hg64), cv_zOf] at hab
      have hid : ent AlX.F i (ent T1X.F l g / 48) / 48 =
          ent T1X.F (ent AlX.F i l / 48) (ent AlX.F i g / 48) / 48 := Nat.eq_of_beq_eq_true hidx
      rw [htw, map_mul, map_mul, map_inv, hS, gen, αzc,
        rearr2 _ _ _ _ _ (zw_mem_center _ _ _), hab, hid]
      rw [mul_assoc]
      congr 1
      rw [show zw (ent AlX.F i (ent T1X.F l g / 48)) = zw (ent T1X.F (ent AlX.F i l / 48)
          (ent AlX.F i g / 48)) * zw (ent AlX.F i l) * zw (ent AlX.F i g) *
          (zc α₁ ^ (ent T1X.F l g % 48 / 12) * zc α₂ ^ (ent T1X.F l g % 12 / 3) *
            zc α₃ ^ (ent T1X.F l g % 3))⁻¹ by rw [← hlab']; group]
      simp only [zw]
      group
  refine ⟨fun k hk => ?_, fun j hj => ?_⟩
  · rw [← hα, key k hk, alOf i k hi (by omega), cv_zOf]
    rfl
  · have hzj : ∀ (u : List (Fin 2 × Bool)) (α' : ℕ) (k : ℕ), k < 66 → α' < 48 →
        ent AlX.F i k = zEnt α' → α (cv u) = zc α' →
        (alphaEntry i k).1 = 0 ∧ cv (substWord (aut i) u) = cv (zOf (alphaEntry i k)) := by
      intro u α' k hk hl he hu
      rw [alOf i k hi hk, he, ← hα, hu]
      exact ⟨(zEnt_spec hl).1, (zEnt_spec hl).2.symm⟩
    interval_cases j
    · exact hzj zOne α₁ 64 (by norm_num) l₁ (Nat.eq_of_beq_eq_true h64) az₁
    · exact hzj zTwo α₂ 65 (by norm_num) l₂ (Nat.eq_of_beq_eq_true h65) az₂

end CertificateChecks.KernelL34Cov

end
