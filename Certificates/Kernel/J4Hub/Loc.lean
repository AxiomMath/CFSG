module

public import Certificates.Kernel.J4Hub.FamGrp
public import Certificates.Kernel.J4Hub.LocData
public import CFSG.Sporadic.J4.Local
import CFSG.Certificates.Kernel.Common.Harness
public import CFSG.Perm.ChainSpec
public import CFSG.Sporadic.J4.CertParts
public import CFSG.Sporadic.Th.F2Spec

public section

namespace CertificateChecks.KernelJ4Hub

open CFSG.KC.Ord CFSG.KS.Ord CFSG.KS.J4Hub CFSG.Sporadic.J4

theorem ai_inv : Nat.beq (FMUL (CFSG.KD.FamJ4.RW 1) (CFSG.KD.FamJ4.RW 3)) CFSG.KD.FamJ4.ONE = true := by
  quickRfl

theorem bi_inv : Nat.beq (FMUL (CFSG.KD.FamJ4.RW 2) (CFSG.KD.FamJ4.RW 4)) CFSG.KD.FamJ4.ONE = true := by
  quickRfl

@[expose] def GRab : Nat := nat_lit 131073
@[expose] def IRab : Nat := nat_lit 262147

@[expose] def GRl : Nat := nat_lit 12885032961
@[expose] def IRl : Nat := nat_lit 25770131460

theorem lg_valid : andB (FV (LG 1)) (andB (FV (LG 2)) (andB (FV (LG 3)) (andB (FV (LG 4))
    (andB (FV (LG 5)) (FV (LG 6)))))) = true := by
  quickRfl

theorem lg_inv : andB (Nat.beq (FMUL (LG 1) (LG 4)) CFSG.KD.FamJ4.ONE)
    (andB (Nat.beq (FMUL (LG 2) (LG 5)) CFSG.KD.FamJ4.ONE)
      (Nat.beq (FMUL (LG 3) (LG 6)) CFSG.KD.FamJ4.ONE)) = true := by
  quickRfl

theorem lw0_word : Nat.beq (CFSG.KC.Fam.wordProd CFSG.KD.FamJ4.RW FMUL CFSG.KD.FamJ4.ONE GRab IRab lw0
    CFSG.KD.FamJ4.ONE) (LG 1) = true := by
  quickRfl

theorem lw1_word : Nat.beq (CFSG.KC.Fam.wordProd CFSG.KD.FamJ4.RW FMUL CFSG.KD.FamJ4.ONE GRab IRab lw1
    CFSG.KD.FamJ4.ONE) (LG 2) = true := by
  quickRfl

theorem lw2_word : Nat.beq (CFSG.KC.Fam.wordProd CFSG.KD.FamJ4.RW FMUL CFSG.KD.FamJ4.ONE GRab IRab lw2
    CFSG.KD.FamJ4.ONE) (LG 3) = true := by
  quickRfl

theorem xW_word : Nat.beq (CFSG.KC.Fam.wordProd LG FMUL CFSG.KD.FamJ4.ONE GRl IRl xW CFSG.KD.FamJ4.ONE)
    (CFSG.KD.FamJ4.RW 22) = true := by
  quickRfl

theorem yW_word : Nat.beq (CFSG.KC.Fam.wordProd LG FMUL CFSG.KD.FamJ4.ONE GRl IRl yW CFSG.KD.FamJ4.ONE)
    (CFSG.KD.FamJ4.RW 26) = true := by
  quickRfl

theorem zW_word : Nat.beq (CFSG.KC.Fam.wordProd LG FMUL CFSG.KD.FamJ4.ONE GRl IRl zW CFSG.KD.FamJ4.ONE)
    (CFSG.KD.FamJ4.RW 47) = true := by
  quickRfl

@[expose] def toL (l : ℤ) : ℕ × Bool := if 0 < l then (l.toNat - 1, true) else ((-l).toNat - 1, false)

theorem mainWord_eq {G : Type*} [Group G] (gs : ℕ → G) (w : List ℤ) :
    CFSG.Sporadic.J4.wordProd gs w =
      ((w.map toL).map fun x => if x.2 then gs x.1 else (gs x.1)⁻¹).prod := by
  unfold CFSG.Sporadic.J4.wordProd
  rw [List.map_map]
  congr 1
  apply List.map_congr_left
  intro l _
  by_cases h : 0 < l <;> simp [toL, h]

theorem lw0_eq : lw0 = (((CFSG.Sporadic.J4.Native.localWords ())[0]?).getD []).map toL := by decide
theorem lw1_eq : lw1 = (((CFSG.Sporadic.J4.Native.localWords ())[1]?).getD []).map toL := by decide
theorem lw2_eq : lw2 = (((CFSG.Sporadic.J4.Native.localWords ())[2]?).getD []).map toL := by decide

@[expose] noncomputable def φG : GL (Fin 112) (ZMod 2) →* Matrix (Fin 112) (Fin 112) (ZMod 2) :=
  Units.coeHom _

theorem gab0 : at16 GRab 0 = 1 := Nat.eq_of_beq_eq_true (by quickRfl)
theorem gab1 : at16 GRab 1 = 2 := Nat.eq_of_beq_eq_true (by quickRfl)
theorem iab0 : at16 IRab 0 = 3 := Nat.eq_of_beq_eq_true (by quickRfl)
theorem iab1 : at16 IRab 1 = 4 := Nat.eq_of_beq_eq_true (by quickRfl)

theorem baseGL_val0 : φG (baseGL 0) = FM (CFSG.KD.FamJ4.RW 1) := by
  change ((gA : GL (Fin 112) (ZMod 2)) : Matrix (Fin 112) (Fin 112) (ZMod 2)) = _
  rw [gA_val', matA, fam_A]

theorem baseGL_val1 : φG (baseGL 1) = FM (CFSG.KD.FamJ4.RW 2) := by
  change ((gB : GL (Fin 112) (ZMod 2)) : Matrix (Fin 112) (Fin 112) (ZMod 2)) = _
  rw [gB_val', matB, fam_B]

theorem mul_one_of {a b : Nat} (ha : FV a = true) (hb : FV b = true)
    (h : Nat.beq (FMUL a b) CFSG.KD.FamJ4.ONE = true) : FM a * FM b = 1 := by
  calc FM a * FM b = FM (FMUL a b) := (mul_sound' (hnb := rfl) CFSG.KD.FamJ4.consts ha hb).2.symm
    _ = FM CFSG.KD.FamJ4.ONE := by rw [Nat.eq_of_beq_eq_true h]
    _ = 1 := (one_sound' (hnb := rfl) CFSG.KD.FamJ4.consts).2

theorem inv_val_of {u : GL (Fin 112) (ZMod 2)} {a b : Nat} (hu : φG u = FM a) (ha : FV a = true)
    (hb : FV b = true) (h : Nat.beq (FMUL a b) CFSG.KD.FamJ4.ONE = true) : φG u⁻¹ = FM b := by
  change ((u⁻¹ : GL (Fin 112) (ZMod 2)) : Matrix (Fin 112) (Fin 112) (ZMod 2)) = _
  rw [Matrix.coe_units_inv]
  change (φG u)⁻¹ = _
  rw [hu]
  exact Matrix.inv_eq_right_inv (mul_one_of ha hb h)

theorem word_mat {RBf : Nat → Nat} {GRf IRf : Nat} {gs : ℕ → GL (Fin 112) (ZMod 2)}
    {l : List (ℕ × Bool)}
    (hv : ∀ x ∈ l, FV (CFSG.KC.Fam.letL RBf GRf IRf x) = true)
    (hl : ∀ x ∈ l, φG (if x.2 then gs x.1 else (gs x.1)⁻¹) = FM (CFSG.KC.Fam.letL RBf GRf IRf x)) :
    φG (l.map fun x => if x.2 then gs x.1 else (gs x.1)⁻¹).prod =
      FM (CFSG.KC.Fam.wordProd RBf FMUL CFSG.KD.FamJ4.ONE GRf IRf l CFSG.KD.FamJ4.ONE) := by
  refine Eq.trans ?_ (wordProd_sound' (hnb := rfl) CFSG.KD.FamJ4.consts hv).2.symm
  rw [map_list_prod, List.map_map]
  congr 1
  exact List.map_congr_left fun x hx => hl x hx

theorem fam_valid {r : Nat} (h0 : 0 < r) (h1 : r < 239) : FV (CFSG.KD.FamJ4.RW r) = true :=
  (fe_spec h0 h1).2.2

theorem lwLetter {x : ℕ × Bool} (hx : x.1 < 2) :
    FV (CFSG.KC.Fam.letL CFSG.KD.FamJ4.RW GRab IRab x) = true ∧
      φG (if x.2 then baseGL x.1 else (baseGL x.1)⁻¹) = FM (CFSG.KC.Fam.letL CFSG.KD.FamJ4.RW GRab IRab x) := by
  obtain ⟨g, s⟩ := x
  have hg : g < 2 := hx
  obtain rfl | rfl : g = 0 ∨ g = 1 := by omega
  · cases s
    · refine ⟨by simp only [CFSG.KC.Fam.letL]; rw [iab0]; exact fam_valid (by norm_num) (by norm_num), ?_⟩
      simp only [CFSG.KC.Fam.letL, Bool.false_eq_true, ↓reduceIte]
      rw [iab0]
      exact inv_val_of baseGL_val0 (fam_valid (by norm_num) (by norm_num))
        (fam_valid (by norm_num) (by norm_num)) ai_inv
    · refine ⟨by simp only [CFSG.KC.Fam.letL]; rw [gab0]; exact fam_valid (by norm_num) (by norm_num), ?_⟩
      simp only [CFSG.KC.Fam.letL, ↓reduceIte]
      rw [gab0]
      exact baseGL_val0
  · cases s
    · refine ⟨by simp only [CFSG.KC.Fam.letL]; rw [iab1]; exact fam_valid (by norm_num) (by norm_num), ?_⟩
      simp only [CFSG.KC.Fam.letL, Bool.false_eq_true, ↓reduceIte]
      rw [iab1]
      exact inv_val_of baseGL_val1 (fam_valid (by norm_num) (by norm_num))
        (fam_valid (by norm_num) (by norm_num)) bi_inv
    · refine ⟨by simp only [CFSG.KC.Fam.letL]; rw [gab1]; exact fam_valid (by norm_num) (by norm_num), ?_⟩
      simp only [CFSG.KC.Fam.letL, ↓reduceIte]
      rw [gab1]
      exact baseGL_val1

theorem lw0_lt : ∀ x ∈ lw0, x.1 < 2 := by decide
theorem lw1_lt : ∀ x ∈ lw1, x.1 < 2 := by decide
theorem lw2_lt : ∀ x ∈ lw2, x.1 < 2 := by decide

theorem locGL_val_of {k : ℕ} {lw : List (ℕ × Bool)}
    (he : lw = (((CFSG.Sporadic.J4.Native.localWords ())[k]?).getD []).map toL) (hlt : ∀ x ∈ lw, x.1 < 2)
    (hw : Nat.beq (CFSG.KC.Fam.wordProd CFSG.KD.FamJ4.RW FMUL CFSG.KD.FamJ4.ONE GRab IRab lw
      CFSG.KD.FamJ4.ONE) (LG (k + 1)) = true) : φG (locGL k) = FM (LG (k + 1)) := by
  rw [locGL, mainWord_eq, ← he, word_mat (fun x hx => (lwLetter (hlt x hx)).1)
    (fun x hx => (lwLetter (hlt x hx)).2), Nat.eq_of_beq_eq_true hw]

theorem locGL_val0 : φG (locGL 0) = FM (LG 1) := locGL_val_of lw0_eq lw0_lt lw0_word
theorem locGL_val1 : φG (locGL 1) = FM (LG 2) := locGL_val_of lw1_eq lw1_lt lw1_word
theorem locGL_val2 : φG (locGL 2) = FM (LG 3) := locGL_val_of lw2_eq lw2_lt lw2_word

theorem lgv {r : Nat} (h0 : 0 < r) (h1 : r < 7) : FV (LG r) = true := by
  have h := lg_valid
  obtain rfl | rfl | rfl | rfl | rfl | rfl : r = 1 ∨ r = 2 ∨ r = 3 ∨ r = 4 ∨ r = 5 ∨ r = 6 := by omega
  · exact (andB_true h).1
  · exact (andB_true (andB_true h).2).1
  · exact (andB_true (andB_true (andB_true h).2).2).1
  · exact (andB_true (andB_true (andB_true (andB_true h).2).2).2).1
  · exact (andB_true (andB_true (andB_true (andB_true (andB_true h).2).2).2).2).1
  · exact (andB_true (andB_true (andB_true (andB_true (andB_true h).2).2).2).2).2

theorem gl_at (g : ℕ) (hg : g < 3) : at16 GRl g = g + 1 ∧ at16 IRl g = g + 4 := by
  obtain rfl | rfl | rfl : g = 0 ∨ g = 1 ∨ g = 2 := by omega
  · exact ⟨Nat.eq_of_beq_eq_true (by quickRfl), Nat.eq_of_beq_eq_true (by quickRfl)⟩
  · exact ⟨Nat.eq_of_beq_eq_true (by quickRfl), Nat.eq_of_beq_eq_true (by quickRfl)⟩
  · exact ⟨Nat.eq_of_beq_eq_true (by quickRfl), Nat.eq_of_beq_eq_true (by quickRfl)⟩

theorem locGL_val {g : ℕ} (hg : g < 3) : φG (locGL g) = FM (LG (g + 1)) := by
  obtain rfl | rfl | rfl : g = 0 ∨ g = 1 ∨ g = 2 := by omega
  · exact locGL_val0
  · exact locGL_val1
  · exact locGL_val2

theorem lg_inv_at {g : ℕ} (hg : g < 3) : Nat.beq (FMUL (LG (g + 1)) (LG (g + 4))) CFSG.KD.FamJ4.ONE = true := by
  have h := lg_inv
  obtain rfl | rfl | rfl : g = 0 ∨ g = 1 ∨ g = 2 := by omega
  · exact (andB_true h).1
  · exact (andB_true (andB_true h).2).1
  · exact (andB_true (andB_true h).2).2

theorem locLetter {x : ℕ × Bool} (hx : x.1 < 3) :
    FV (CFSG.KC.Fam.letL LG GRl IRl x) = true ∧
      φG (if x.2 then locGL x.1 else (locGL x.1)⁻¹) = FM (CFSG.KC.Fam.letL LG GRl IRl x) := by
  obtain ⟨g, s⟩ := x
  have hg : g < 3 := hx
  obtain ⟨e1, e2⟩ := gl_at g hg
  cases s
  · simp only [CFSG.KC.Fam.letL, Bool.false_eq_true, ↓reduceIte]
    rw [e2]
    exact ⟨lgv (by omega) (by omega), inv_val_of (locGL_val hg) (lgv (by omega) (by omega))
      (lgv (by omega) (by omega)) (lg_inv_at hg)⟩
  · simp only [CFSG.KC.Fam.letL, ↓reduceIte]
    rw [e1]
    exact ⟨lgv (by omega) (by omega), locGL_val hg⟩

theorem mem_Hj_of_word {l : List (ℕ × Bool)} (hl : ∀ x ∈ l, x.1 < 3) {r : ℕ} (h0 : 0 < r) (h1 : r < 239)
    (hw : Nat.beq (CFSG.KC.Fam.wordProd LG FMUL CFSG.KD.FamJ4.ONE GRl IRl l CFSG.KD.FamJ4.ONE)
      (CFSG.KD.FamJ4.RW r) = true) : feJ r ∈ Hj := by
  have hmem : (l.map fun x => if x.2 then xJ x.1 else (xJ x.1)⁻¹).prod ∈ Hj := by
    apply Subgroup.list_prod_mem
    intro z hz
    obtain ⟨x, hx, rfl⟩ := List.mem_map.1 hz
    have hx3 := hl x hx
    have hxm : xJ x.1 ∈ Hj := xJ_mem hx3
    split_ifs
    · exact hxm
    · exact Hj.inv_mem hxm
  have e : (l.map fun x => if x.2 then xJ x.1 else (xJ x.1)⁻¹).prod = feJ r := by
    apply φJ_injective
    have h2 : φJ (l.map fun x => if x.2 then xJ x.1 else (xJ x.1)⁻¹).prod =
        φG (l.map fun x => if x.2 then locGL x.1 else (locGL x.1)⁻¹).prod := by
      change φG (J.subtype _) = _
      rw [map_list_prod, List.map_map]
      congr 2
      apply List.map_congr_left
      intro x _
      simp only [Function.comp_apply]
      split_ifs <;> simp [xJ]
    rw [h2, word_mat (fun x hx => (locLetter (hl x hx)).1) (fun x hx => (locLetter (hl x hx)).2),
      Nat.eq_of_beq_eq_true hw, φJ_apply, feJ_val h0 h1]
  exact e ▸ hmem

set_option maxRecDepth 20000 in
theorem xW_lt : ∀ x ∈ xW, x.1 < 3 := by decide
set_option maxRecDepth 20000 in
theorem yW_lt : ∀ x ∈ yW, x.1 < 3 := by decide
set_option maxRecDepth 20000 in
theorem zW_lt : ∀ x ∈ zW, x.1 < 3 := by decide

theorem X_mem_Hj : X ∈ Hj := mem_Hj_of_word xW_lt (by norm_num) (by norm_num) xW_word
theorem Y_mem_Hj : Y ∈ Hj := mem_Hj_of_word yW_lt (by norm_num) (by norm_num) yW_word
theorem Z_mem_Hj : CFSG.Certificates.J4R.zElt X Y T ∈ Hj := by
  rw [Z_eq]
  exact mem_Hj_of_word zW_lt (by norm_num) (by norm_num) zW_word

end CertificateChecks.KernelJ4Hub

end
