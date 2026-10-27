
module

public import Certificates.Kernel.LyModel.CoverGlue
public import Certificates.Kernel.LyModel.StructChk
public import Certificates.Kernel.LyModel.Cp1Chk
public import Certificates.Kernel.LyModel.InvChk
public import Certificates.Kernel.LyModel.MarkChk

public section

namespace CertificateChecks.KernelLyModel

open Equiv CFSG.KC CFSG.KC.Benes CFSG.KC.YModel.Sem CFSG.KC.LyBenes CFSG.KC.LyModel
  CFSG.KC.LyBase CFSG.KC.LyGlue CFSG.KC.MonsterConv.Perm CertificateChecks.KernelLy
  CertificateChecks.KernelLyB CertificateChecks.KernelLyBase CFSG.Sporadic.Recognition.LyonsSims
  CFSG.Sporadic.Recognition.LyonsSims.LyFinal CFSG.Sporadic.Recognition.McLMultiplier
  CFSG.Sporadic.Th CFSG.Sporadic.Th.Native

abbrev CdW (w : List ℤ) : Prop := ∀ l ∈ w, l ≠ 0 ∧ l.natAbs ≤ 2

theorem cdW_append {u v : List ℤ} (hu : CdW u) (hv : CdW v) : CdW (u ++ v) := by
  intro l hl
  rcases List.mem_append.1 hl with hl | hl
  · exact hu l hl
  · exact hv l hl

theorem cdW_dec (s : String) : CdW (Ly0.decodeWord s) := Ly0.decodeWord_mem s

theorem cdW_one : CdW [1] := by decide

theorem cdW_neg_one : CdW [-1] := by decide

theorem mem0 {w : List ℤ} (hw : CdW w) : Ly0.wG Ly0.gens0 w ∈ Ly0.B0 :=
  Ly0.wG_mem Ly0.B0 Ly0.gens0 2 Ly0.gens0_mem w hw

theorem wG_one : Ly0.wG Ly0.gens0 [1] = Ly0.cG := by
  simp [Ly0.letterG_pos, Ly0.gens0_zero]

theorem wG_neg_one : Ly0.wG Ly0.gens0 [-1] = Ly0.cG⁻¹ := by
  simp [Ly0.letterG_neg_of, Ly0.gens0_zero]

theorem wG_two : Ly0.wG Ly0.gens0 [2] = Ly0.dG := by
  simp [Ly0.letterG_pos, Ly0.gens0_one]

theorem wG1_one : Ly0.wG Ly0.gens1 [1] = Ly0.AG := by
  simp [Ly0.letterG_pos, Ly0.gens1_zero]

theorem wG1_two : Ly0.wG Ly0.gens1 [2] = Ly0.BG := by
  simp [Ly0.letterG_pos, Ly0.gens1_one]

theorem wG_inv {w : List ℤ} (hw : CdW w) : Ly0.wG Ly0.gens0 (invW w) = (Ly0.wG Ly0.gens0 w)⁻¹ :=
  Ly0.wG_invW Ly0.gens0 fun l hl => (hw l hl).1

section Cd

variable (hbc : RB5Bound)
include hbc

theorem cdPt (w : List ℤ) (hw : CdW w) (a : Fin Ly0.deg) :
    cdPtC cL dL (w.map lcode) a = (Ly0.wG Ly0.gens0 w a : Nat) :=
  cdPtC_wG cL_eq_cG dL_eq_dG (cG_mul_cG cL_eq_cG dL_eq_dG) (dG_pow_three cL_eq_cG dL_eq_dG) w hw a

omit hbc in
theorem cdEq_parts {u v : List ℤ} (h : cdEq u v = true) :
    ∀ b : Fin Ly0.deg, (b : Nat) = 0 ∨ (b : Nat) = 3 ∨ (b : Nat) = 1 →
      cdPtC cL dL (u.map lcode) b = cdPtC cL dL (v.map lcode) b := by
  obtain ⟨h0, h31⟩ := andB_true h
  obtain ⟨h3, h1⟩ := andB_true h31
  intro b hb
  rcases hb with hb | hb | hb <;> rw [hb]
  · exact Nat.eq_of_beq_eq_true h0
  · exact Nat.eq_of_beq_eq_true h3
  · exact Nat.eq_of_beq_eq_true h1

theorem cdEq_eq {u v : List ℤ} (hu : CdW u) (hv : CdW v) (h : cdEq u v = true) :
    Ly0.wG Ly0.gens0 u = Ly0.wG Ly0.gens0 v := by
  have key : ∀ b : Fin Ly0.deg, (b : Nat) = 0 ∨ (b : Nat) = 3 ∨ (b : Nat) = 1 →
      ((Ly0.wG Ly0.gens0 v)⁻¹ * Ly0.wG Ly0.gens0 u) b = b := by
    intro b hb
    have e := cdEq_parts h b hb
    rw [cdPt hbc u hu b, cdPt hbc v hv b] at e
    rw [Perm.mul_apply, Fin.ext e, ← Perm.mul_apply, inv_mul_cancel, Perm.one_apply]
  have h1 := eq_one_of_fix_base cL_eq_cG dL_eq_dG hbc (mul_mem (inv_mem (mem0 hv)) (mem0 hu))
    (key p0 (Or.inl rfl)) (key p3 (Or.inr (Or.inl rfl))) (key p1 (Or.inr (Or.inr rfl)))
  exact (inv_mul_eq_one.1 h1).symm

theorem cdEq_ne {u v : List ℤ} (hu : CdW u) (hv : CdW v) (h : notB (cdEq u v) = true) :
    Ly0.wG Ly0.gens0 u ≠ Ly0.wG Ly0.gens0 v := by
  intro e
  have e' : ∀ b : Fin Ly0.deg,
      cdPtC cL dL (u.map lcode) b = cdPtC cL dL (v.map lcode) b := fun b => by
    rw [cdPt hbc u hu b, cdPt hbc v hv b, e]
  have e0 : cdPtC cL dL (u.map lcode) 0 = cdPtC cL dL (v.map lcode) 0 := e' p0
  have e3 : cdPtC cL dL (u.map lcode) 3 = cdPtC cL dL (v.map lcode) 3 := e' p3
  have e1 : cdPtC cL dL (u.map lcode) 1 = cdPtC cL dL (v.map lcode) 1 := e' p1
  have hc : cdEq u v = true := by
    unfold cdEq
    rw [e0, e3, e1, Nat.beq_refl, Nat.beq_refl, Nat.beq_refl]
    rfl
  rw [hc] at h
  exact absurd h (by decide)

end Cd

@[expose] def NR (Ns : List Nat) (g : Perm (Fin Ly0.deg)) : Prop :=
  ∀ a : Fin Ly0.deg, compN 17 Ns a = (g a : Nat)

theorem compN_append (Ns Ms : List Nat) (r : Nat) :
    compN 17 (Ns ++ Ms) r = compN 17 Ns (compN 17 Ms r) := by
  induction Ns with
  | nil => rfl
  | cons N Ns ih =>
    change benesPerm 17 N (compN 17 (Ns ++ Ms) r) = benesPerm 17 N (compN 17 Ns (compN 17 Ms r))
    rw [ih]

theorem NR.append {Ns Ms : List Nat} {g h : Perm (Fin Ly0.deg)} (hg : NR Ns g) (hh : NR Ms h) :
    NR (Ns ++ Ms) (g * h) := fun a => by
  rw [compN_append, hh a, hg (h a), Perm.mul_apply]

theorem nr_cd {w : List ℤ} (hw : CdW w) : NR (genNets NS w) (Ly0.wG Ly0.gens0 w) := by
  intro a
  have e : genNets NS w = w.map fun z => NS (zIdx z) := rfl
  rw [e, compN_map (fun z => NS (zIdx z)) (Ly0.letterG Ly0.gens0) w
    (fun z hz => nrep_z cL_eq_cG dL_eq_dG z (hw z hz)) a, wG_eq_prod]

theorem nr_ab {w : List ℤ} (hw : CdW w) : NR (genNets MS w) (Ly0.wG Ly0.gens1 w) := by
  intro a
  have e : genNets MS w = w.map fun z => MS (zIdx z) := rfl
  rw [e, compN_map (fun z => MS (zIdx z)) (Ly0.letterG Ly0.gens1) w
    (fun z hz => nrep_z1 z (hw z hz)) a, wG_eq_prod]

theorem memY (r : List (Fin 6 × Bool)) : Ly0.wG Ly0.yG (r.map letterZ) ∈ Ly0.B0 :=
  Ly0.wG_mem Ly0.B0 Ly0.yG 6 Ly0.yG_mem_B0 _ fun l hl => by
    obtain ⟨l', -, rfl⟩ := List.mem_map.1 hl
    exact Ly0.letterZ_mem l'

theorem mem1 {w : List ℤ} (hw : CdW w) : Ly0.wG Ly0.gens1 w ∈ Ly0.B0 :=
  Ly0.wG_mem Ly0.B0 Ly0.gens1 2 Ly0.gens1_mem_B0 w hw

theorem eq_of_baseEq (hbc : RB5Bound) {g h : Perm (Fin Ly0.deg)} (hg : g ∈ Ly0.B0)
    (hh : h ∈ Ly0.B0) {Ns Ms : List Nat} (rg : NR Ns g) (rh : NR Ms h)
    (e : baseEq Ns Ms = true) : g = h := by
  obtain ⟨h0, h31⟩ := andB_true e
  obtain ⟨h3, h1⟩ := andB_true h31
  have key : ∀ b : Fin Ly0.deg, compN 17 Ns b = compN 17 Ms b → (h⁻¹ * g) b = b := by
    intro b hb
    rw [rg b, rh b] at hb
    rw [Perm.mul_apply, Fin.ext hb, ← Perm.mul_apply, inv_mul_cancel, Perm.one_apply]
  have h1' := eq_one_of_fix_base cL_eq_cG dL_eq_dG hbc (mul_mem (inv_mem hh) hg)
    (key p0 (Nat.eq_of_beq_eq_true h0)) (key p3 (Nat.eq_of_beq_eq_true h3))
    (key p1 (Nat.eq_of_beq_eq_true h1))
  exact (inv_mul_eq_one.1 h1').symm

theorem tab_eq {T₁ T₂ : Table} {g₁ g₂ : Perm (Fin Ly0.deg)} (h₁ : T₁.size = Ly0.deg)
    (h₂ : T₂.size = Ly0.deg) (r₁ : Rep Ly0.deg T₁ g₁) (r₂ : Rep Ly0.deg T₂ g₂) (e : g₁ = g₂) :
    T₁ = T₂ := by
  subst e
  exact Ly0.tab_eq_of_rep h₁ h₂ r₁ r₂

theorem tab_ne {T₁ T₂ : Table} {g₁ g₂ : Perm (Fin Ly0.deg)} (r₁ : Rep Ly0.deg T₁ g₁)
    (r₂ : Rep Ly0.deg T₂ g₂) (ne : g₁ ≠ g₂) : T₁ ≠ T₂ := by
  rintro rfl
  exact ne (Ly0.eq_of_rep r₁ r₂)

theorem powT_size (e : ℕ) (P : Table) : (powT Ly0.deg e P).size = Ly0.deg := by
  cases e with
  | zero =>
    rw [powT]
    exact Ly0.idT_size
  | succ e =>
    rw [powT]
    exact Ly0.compT_size _ _

theorem tabA_size : Ly0.tabA.size = Ly0.deg := by
  unfold Ly0.tabA
  rw [Ly0.tabs1_zero]
  exact Ly0.wT_size _ _ _

theorem tabB_size : Ly0.tabB.size = Ly0.deg := by
  unfold Ly0.tabB
  rw [Ly0.tabs1_one]
  exact Ly0.wT_size _ _ _

theorem tabX_size : Ly0.tabX.size = Ly0.deg := by
  unfold Ly0.tabX
  exact CFSG.KS.Tbl.invT_size _ _

theorem rep_X' : Rep Ly0.deg Ly0.tabX Ly0.R0G⁻¹ := by
  unfold Ly0.tabX
  exact CFSG.KS.Tbl.invT_rep Ly0.deg_lt (Ly0.rep_R0 tabCheck_true)

theorem cdW_X : CdW Ly0.wordX := cdW_dec _

theorem cdW_nil : CdW [] := fun _ h => absurd h List.not_mem_nil

theorem cdW_W : CdW Ly0.wordW := fun _ hl => Ly0.mem_wordW hl

section Facts

variable (hbc : RB5Bound)
include hbc

theorem xw : Ly0.wG Ly0.gens0 Ly0.wordX = Ly0.R0G⁻¹ := by
  have e := eq_of_baseEq hbc (mul_mem (memY mclR0) (mem0 cdW_X)) (one_mem _)
    (NR.append (compN_yNets mclR0) (nr_cd cdW_X)) (fun _ => rfl) ly6110_sX
  rw [← Ly0.R0G_def] at e
  exact eq_inv_of_mul_eq_one_right e

theorem R0_cube : Ly0.R0G * (Ly0.R0G * Ly0.R0G) = 1 := by
  have e := cdEq_eq hbc (cdW_append cdW_X (cdW_append cdW_X cdW_X)) (fun _ h => absurd h
    List.not_mem_nil) ly6110_sX3
  rw [Ly0.wG_append, Ly0.wG_append, xw hbc, Ly0.wG_nil] at e
  have e2 : (Ly0.R0G⁻¹ * (Ly0.R0G⁻¹ * Ly0.R0G⁻¹))⁻¹ = Ly0.R0G * (Ly0.R0G * Ly0.R0G) := by
    simp only [mul_inv_rev, inv_inv, mul_assoc]
  rw [← e2, e, inv_one]

theorem R0_ne_one : Ly0.R0G ≠ 1 := by
  intro h1
  have e := cdEq_ne hbc cdW_X (fun _ h => absurd h List.not_mem_nil) ly6110_sX1
  rw [xw hbc, h1, inv_one, Ly0.wG_nil] at e
  exact e rfl

theorem BG_eq' : Ly0.BG = Ly0.wG Ly0.yG (mclSurjB.map letterZ) * (Ly0.R0G⁻¹ * Ly0.R0G⁻¹) := by
  have e := eq_of_baseEq hbc (mem1 (by decide)) (mul_mem (memY mclSurjB)
    (mem0 (cdW_append cdW_X cdW_X))) (nr_ab (by decide)) (NR.append (compN_yNets mclSurjB)
    (nr_cd (cdW_append cdW_X cdW_X))) ly6110_sB
  rw [wG1_two, Ly0.wG_append, xw hbc] at e
  exact e

theorem dG_eq' : Ly0.dG = Ly0.wG Ly0.gens1 Ly0.wordD := by
  have e := eq_of_baseEq hbc (mem0 (by decide)) (mem1 (cdW_dec _)) (nr_cd (by decide))
    (nr_ab (cdW_dec _)) ly6110_sD
  rwa [wG_two] at e

theorem cAc_eq' : Ly0.cG * (Ly0.AG * Ly0.cG⁻¹) = Ly0.wG Ly0.gens1 Ly0.wordCAC := by
  have e := eq_of_baseEq hbc (mul_mem (mul_mem (mem0 cdW_one) (mem1 (by decide)))
    (mem0 cdW_neg_one)) (mem1 (cdW_dec _))
    (((nr_cd cdW_one).append (nr_ab (by decide))).append (nr_cd cdW_neg_one))
    (nr_ab (cdW_dec _)) ly6110_sCAC
  rw [wG_one, wG1_one, wG_neg_one, mul_assoc] at e
  exact e

theorem cBc_eq' : Ly0.cG * (Ly0.BG * Ly0.cG⁻¹) = Ly0.wG Ly0.gens1 Ly0.wordCBC := by
  have e := eq_of_baseEq hbc (mul_mem (mul_mem (mem0 cdW_one) (mem1 (by decide)))
    (mem0 cdW_neg_one)) (mem1 (cdW_dec _))
    (((nr_cd cdW_one).append (nr_ab (by decide))).append (nr_cd cdW_neg_one))
    (nr_ab (cdW_dec _)) ly6110_sCBC
  rw [wG_one, wG1_two, wG_neg_one, mul_assoc] at e
  exact e

theorem cXc_eq : Ly0.cG * (Ly0.R0G⁻¹ * Ly0.cG⁻¹) = Ly0.R0G := by
  have e := cdEq_eq hbc (cdW_append (cdW_append cdW_one cdW_X) cdW_neg_one)
    (fun l hl => invW_mem cdW_X l hl) ly6110_sCX
  rw [Ly0.wG_append, Ly0.wG_append, wG_one, wG_neg_one, wG_inv cdW_X, xw hbc, inv_inv,
    mul_assoc] at e
  exact e

end Facts

theorem structCheck_true (hbc : RB5Bound) : Ly0.structCheck = true := by
  have h := tabCheck_true
  have rR := Ly0.rep_R0 h
  have rX := rep_X'
  have rc := Ly0.rep_cG h
  have rci := Ly0.rep_cinv h
  unfold Ly0.structCheck
  simp only [Bool.and_eq_true, Bool.not_eq_true', beq_iff_eq, and_assoc, ne_eq,
    Bool.not_eq_true, beq_eq_false_iff_ne]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold Ly0.tabX
    exact CFSG.KS.Tbl.invOK_invT Ly0.deg_lt rR
  · exact tab_ne rR (Rep.idT Ly0.deg_lt) (R0_ne_one hbc)
  · exact tab_eq (Ly0.compT_size _ _) Ly0.idT_size (rR.compT (rR.compT rR)) (Rep.idT Ly0.deg_lt)
      (R0_cube hbc)
  · have s : (Ly0.tabs2[5]!).size = Ly0.deg := by
      rw [Ly0.tabs2_get (by decide)]
      exact Ly0.wT_size _ _ _
    exact tab_eq s tabA_size (rep_yG' 5 (by decide)) (Ly0.rep_tabA h) yG_five'
  · refine tab_eq tabB_size (Ly0.compT_size _ _) (Ly0.rep_tabB h)
      (Rep.compT (Ly0.rep_yWord h _ fun l hl => ?_) (rX.compT rX)) (BG_eq' hbc)
    obtain ⟨l', -, rfl⟩ := List.mem_map.1 hl
    exact Ly0.letterZ_mem l'
  · exact tab_eq (Ly0.wT_size _ _ _) tabX_size (Ly0.rep_word0 h _ cdW_X) rX (xw hbc)
  · exact tab_eq dT_size (Ly0.wT_size _ _ _) (Ly0.rep_dG h) (Ly0.rep_word1 h _ (cdW_dec _))
      (dG_eq' hbc)
  · exact tab_eq (Ly0.compT_size _ _) (Ly0.wT_size _ _ _) (rc.compT ((Ly0.rep_tabA h).compT rci))
      (Ly0.rep_word1 h _ (cdW_dec _)) (cAc_eq' hbc)
  · exact tab_eq (Ly0.compT_size _ _) (Ly0.wT_size _ _ _) (rc.compT ((Ly0.rep_tabB h).compT rci))
      (Ly0.rep_word1 h _ (cdW_dec _)) (cBc_eq' hbc)
  · exact tab_eq (Ly0.compT_size _ _) Ly0.idT_size (rc.compT rc) (Rep.idT Ly0.deg_lt)
      (cG_mul_cG cL_eq_cG dL_eq_dG)
  · exact tab_eq (Ly0.compT_size _ _) (Ly0.wT_size _ _ _) (rc.compT (rX.compT rci)) rR
      (cXc_eq hbc)

section Rest

variable (hbc : RB5Bound)
include hbc

theorem comm_of {u v : List ℤ} (hu : CdW u) (hv : CdW v)
    (h : cdEq (u ++ v) (v ++ u) = true) :
    Ly0.wG Ly0.gens0 u * Ly0.wG Ly0.gens0 v = Ly0.wG Ly0.gens0 v * Ly0.wG Ly0.gens0 u := by
  have e := cdEq_eq hbc (cdW_append hu hv) (cdW_append hv hu) h
  rwa [Ly0.wG_append, Ly0.wG_append] at e

theorem inv_of {u v : List ℤ} (hu : CdW u) (hv : CdW v)
    (h : cdEq (u ++ v) (invW v ++ u) = true) :
    Ly0.wG Ly0.gens0 u * (Ly0.wG Ly0.gens0 v * (Ly0.wG Ly0.gens0 u)⁻¹) =
      (Ly0.wG Ly0.gens0 v)⁻¹ := by
  have e := cdEq_eq hbc (cdW_append hu hv) (cdW_append (fun l hl => invW_mem hv l hl) hu) h
  rw [Ly0.wG_append, Ly0.wG_append, wG_inv hv] at e
  rw [← mul_assoc, e, mul_inv_cancel_right]

end Rest

theorem conj_of_comm {G : Type*} [Group G] {a b : G} (h : a * b = b * a) : a * (b * a⁻¹) = b := by
  rw [← mul_assoc, h, mul_inv_cancel_right]

theorem pow_five_eq {G : Type*} [Group G] (a : G) : a ^ 5 = a * (a * (a * (a * a))) := by
  simp only [pow_succ, pow_zero, one_mul, mul_assoc]

theorem cp1Check_true (hbc : RB5Bound) : Ly0.cp1Check = true := by
  have h := tabCheck_true
  have rR := Ly0.rep_R0 h
  have rX := rep_X'
  have rY := Ly0.rep_tabYw h
  have rF := Ly0.rep_tabF h
  have rN := Ly0.rep_tabN h
  have rNi := Ly0.rep_tabNinv h
  have hY : CdW Ly0.wordY := cdW_dec _
  have hF : CdW Ly0.wordF := cdW_dec _
  have hN : CdW Ly0.wordN := cdW_dec _
  have yw := Ly0.y0G_def.symm
  have fw := Ly0.fG_def.symm
  have nw := Ly0.nG_def.symm
  have xw' := xw hbc
  unfold Ly0.cp1Check
  simp only [Bool.and_eq_true, Bool.not_eq_true', beq_iff_eq, and_assoc, ne_eq,
    Bool.not_eq_true, beq_eq_false_iff_ne]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · have e := comm_of hbc hY cdW_X ly6110_cYX
    rw [yw, xw'] at e
    exact tab_eq (Ly0.compT_size _ _) (Ly0.compT_size _ _) (rY.compT rX) (rX.compT rY) e
  · have e := cdEq_eq hbc (cdW_append hY (cdW_append hY hY)) cdW_nil ly6110_cY3
    rw [Ly0.wG_append, Ly0.wG_append, yw, Ly0.wG_nil] at e
    exact tab_eq (Ly0.compT_size _ _) Ly0.idT_size (rY.compT (rY.compT rY)) (Rep.idT Ly0.deg_lt) e
  · have e := cdEq_ne hbc hY cdW_nil ly6110_cY1
    rw [yw, Ly0.wG_nil] at e
    exact tab_ne rY (Rep.idT Ly0.deg_lt) e
  · have e := cdEq_ne hbc (cdW_append hY hY) (fun l hl => invW_mem cdW_X l hl) ly6110_cYYR
    rw [Ly0.wG_append, wG_inv cdW_X, yw, xw', inv_inv] at e
    exact tab_ne (rY.compT rY) rR e
  · have e := cdEq_ne hbc hY (fun l hl => invW_mem cdW_X l hl) ly6110_cYR
    rw [wG_inv cdW_X, yw, xw', inv_inv] at e
    exact tab_ne rY rR e
  · have e := cdEq_eq hbc (cdW_append hF (cdW_append hF (cdW_append hF (cdW_append hF hF))))
      cdW_nil ly6110_cF5
    rw [Ly0.wG_append, Ly0.wG_append, Ly0.wG_append, Ly0.wG_append, fw, Ly0.wG_nil] at e
    exact tab_eq (powT_size 5 _) Ly0.idT_size (Rep.powT Ly0.deg_lt rF 5) (Rep.idT Ly0.deg_lt)
      ((pow_five_eq _).trans e)
  · have e := cdEq_ne hbc hF cdW_nil ly6110_cF1
    rw [fw, Ly0.wG_nil] at e
    exact tab_ne rF (Rep.idT Ly0.deg_lt) e
  · have e := comm_of hbc hF hY ly6110_cFY
    rw [fw, yw] at e
    exact tab_eq (Ly0.compT_size _ _) (Ly0.compT_size _ _) (rF.compT rY) (rY.compT rF) e
  · have e := comm_of hbc hN hY ly6110_cNY
    rw [nw, yw] at e
    exact tab_eq (Ly0.compT_size _ _) (Ly0.wT_size _ _ _) (rN.compT (rY.compT rNi)) rY
      (conj_of_comm e)
  · have e := inv_of hbc hN cdW_X ly6110_cNX
    rw [nw, xw', inv_inv] at e
    exact tab_eq (Ly0.compT_size _ _) (Ly0.wT_size _ _ _) (rN.compT (rX.compT rNi)) rR e

theorem invCheck_true (hbc : RB5Bound) : Ly0.invCheck = true := by
  have h := tabCheck_true
  have rR := Ly0.rep_R0 h
  have rX := rep_X'
  have rY := Ly0.rep_tabYw h
  have rG := Ly0.rep_tabG h
  have rGi := Ly0.rep_tabGinv h
  have hY : CdW Ly0.wordY := cdW_dec _
  have hG : CdW Ly0.wordGg := cdW_dec _
  have yw := Ly0.y0G_def.symm
  have gw := Ly0.gG_def.symm
  have ww := Ly0.w0G_def.symm
  have xw' := xw hbc
  unfold Ly0.invCheck
  simp only [Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq, List.all_eq_true, List.mem_range]
  refine ⟨⟨⟨?_, Or.inr ?_⟩, Or.inr ?_⟩, fun j hj => Or.inr ?_⟩
  · have e := inv_of hbc hG cdW_X ly6110_iGX
    rw [gw, xw', inv_inv] at e
    exact tab_eq (Ly0.compT_size _ _) (Ly0.wT_size _ _ _) (rG.compT (rX.compT rGi)) rR e
  · have e := inv_of hbc hG hY ly6110_iGY
    rw [gw, yw] at e
    exact tab_eq (Ly0.compT_size _ _) (Ly0.wT_size _ _ _) (rG.compT (rY.compT rGi))
      (Ly0.rep_tabYinv h) e
  · have e := inv_of hbc hG cdW_W ly6110_iGW
    rw [gw, ww] at e
    exact tab_eq (Ly0.compT_size _ _) (Ly0.wT_size _ _ _) (rG.compT ((Ly0.rep_tabW h).compT rGi))
      (Ly0.rep_tabWinv h) e
  · have e := inv_of hbc (Ly0.uWords_mem j hj) hY (ly6110_iU j hj)
    rw [← Ly0.uG_def, yw] at e
    exact tab_eq (Ly0.compT_size _ _) (Ly0.wT_size _ _ _)
      ((Ly0.rep_uTabs h hj).compT (rY.compT (Ly0.rep_uInvTabs h hj))) (Ly0.rep_tabYinv h) e

theorem markCheck_true (hbc : RB5Bound) : Ly0.markCheck = true := by
  have h := tabCheck_true
  have rX := rep_X'
  have rY := Ly0.rep_tabYw h
  have rT := Ly0.rep_tabT0 h
  have rW := Ly0.rep_tabW h
  have hY : CdW Ly0.wordY := cdW_dec _
  have hT : CdW Ly0.wordT0 := cdW_dec _
  have yw := Ly0.y0G_def.symm
  have tw := Ly0.t0G_def.symm
  have ww := Ly0.w0G_def.symm
  have xw' := xw hbc
  unfold Ly0.markCheck
  simp only [Bool.and_eq_true, Bool.not_eq_true', beq_iff_eq, and_assoc, ne_eq,
    Bool.not_eq_true, beq_eq_false_iff_ne]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · have e := cdEq_eq hbc (cdW_append hT hT) cdW_nil ly6110_mT2
    rw [Ly0.wG_append, tw, Ly0.wG_nil] at e
    exact tab_eq (Ly0.compT_size _ _) Ly0.idT_size (rT.compT rT) (Rep.idT Ly0.deg_lt) e
  · have e := cdEq_ne hbc hT cdW_nil ly6110_mT1
    rw [tw, Ly0.wG_nil] at e
    exact tab_ne rT (Rep.idT Ly0.deg_lt) e
  · have e := comm_of hbc hT cdW_X ly6110_mTX
    rw [tw, xw'] at e
    exact tab_eq (Ly0.compT_size _ _) (Ly0.compT_size _ _) (rT.compT rX) (rX.compT rT) e
  · have e := comm_of hbc hT hY ly6110_mTY
    rw [tw, yw] at e
    exact tab_eq (Ly0.compT_size _ _) (Ly0.compT_size _ _) (rT.compT rY) (rY.compT rT) e
  · have e := comm_of hbc hT cdW_W ly6110_mTW
    rw [tw, ww] at e
    exact tab_eq (Ly0.compT_size _ _) (Ly0.compT_size _ _) (rT.compT rW) (rW.compT rT) e

end CertificateChecks.KernelLyModel

end
