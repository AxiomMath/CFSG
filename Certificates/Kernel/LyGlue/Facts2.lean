module

public import Certificates.Kernel.LyGlue.KPt
public import Certificates.Kernel.LyGlue.KBlk
public import Certificates.Kernel.LyGlue.Bind
public import Certificates.Kernel.LyGlue.Facts1
public import CFSG.Certificates.Kernel.LyGlue.WordPtSound
public import CFSG.Certificates.Kernel.LyGlue.BlkSound
public import CFSG.Certificates.Kernel.LyGlue.BlockHom
public import CFSG.Sporadic.Recognition.LyonsAmalgamGlueFacts
public import Certificates.Data.Kernel.PermCent.CV

public section

namespace CertificateChecks.KernelLy

open CFSG.KC.Enum CFSG.KS CFSG.KC.LyGlue CFSG.Sporadic.Recognition.LyonsSims Equiv
  CFSG.Certificates.Kernel.PkCV CFSG.Sporadic.Recognition

section

variable (h : Ly0.tabCheck = true)
include h

theorem c2 : Ly0.cG * Ly0.cG = 1 := by
  ext a
  have e := Nat.eq_of_beq_eq_true (allN_spec k_c2 a a.2)
  rw [Perm.mul_apply, Perm.one_apply, ← cL_eq h, ← cL_eq h]
  exact e

theorem d3 : Ly0.dG ^ 3 = 1 := by
  ext a
  have e := Nat.eq_of_beq_eq_true (allN_spec k_d3 a a.2)
  rw [pow_three, Perm.mul_apply, Perm.mul_apply, Perm.one_apply, ← dL_eq h, ← dL_eq h,
    ← dL_eq h]
  exact e

theorem cdPt_eq (ws : List Int) (hws : ∀ l ∈ ws, l ≠ 0 ∧ l.natAbs ≤ 2) (a : Fin Ly0.deg) :
    cdPt ws.length (encW ws) a = (Ly0.wG Ly0.gens0 ws a : Nat) :=
  wptE_wG (cL_eq h) (dL_eq h) (c2 h) (d3 h) ws hws a

end

theorem uWords_len {k : Nat} (hk : k < 4) : (Ly0.uWords.getD k []).length = uLen k := by
  interval_cases k <;> decide +kernel

theorem uWords_code {k : Nat} (hk : k < 4) :
    sel4 k (encW Ly0.wordU1) (encW Ly0.wordU2) (encW Ly0.wordU3) (encW Ly0.wordU4) =
      encW (Ly0.uWords.getD k []) := by
  interval_cases k <;> rfl

theorem uWords_range {k : Nat} (hk : k < 4) :
    ∀ l ∈ Ly0.uWords.getD k [], l ≠ 0 ∧ l.natAbs ≤ 2 := by
  interval_cases k <;> exact fun l hl => Ly0.decodeWord_mem _ l hl

theorem uPt (h : Ly0.tabCheck = true) {k : Nat} (hk : k < 4) (a : Fin Ly0.deg) :
    cdPt (uLen k)
      (sel4 k (encW Ly0.wordU1) (encW Ly0.wordU2) (encW Ly0.wordU3) (encW Ly0.wordU4)) a =
      (Ly0.uG k a : Nat) := by
  rw [uWords_code hk, ← uWords_len hk, cdPt_eq h _ (uWords_range hk), Ly0.uG_def]

@[expose] noncomputable def OY : Set (Fin Ly0.deg) := {a | FY a ≠ 65535}

@[expose] noncomputable def fY (a : Fin Ly0.deg) : Fin 1080 := ⟨FY a % 1080, Nat.mod_lt _ (by norm_num)⟩

theorem yBlk_spec : ∀ a < 66825, FY a ≠ 65535 → FY a < 1080 ∧ ∀ k < 4,
    FY (cdPt (uLen k)
      (sel4 k (encW Ly0.wordU1) (encW Ly0.wordU2) (encW Ly0.wordU3) (encW Ly0.wordU4)) a) =
      pg 11 (mask 11) (UH.F k) (FY a) := by
  have := k_yBlk
  simp only [CFSG.KS.PF.strictB_eqP] at this
  exact blkOK_spec this

theorem fY_eq {a : Fin Ly0.deg} (h1 : FY a < 1080) : fY a = ⟨FY a, h1⟩ :=
  Fin.ext (Nat.mod_eq_of_lt h1)

theorem compatY (h : Ly0.tabCheck = true) (hY : Ly1080.YOK) :
    ∀ k < 4, ∀ a ∈ OY, Ly0.uG k a ∈ OY ∧ fY (Ly0.uG k a) = Ly1080.ug k (fY a) := by
  intro k hk a ha
  obtain ⟨h1, h2⟩ := yBlk_spec a a.2 ha
  have e := h2 k hk
  rw [uPt h hk a, ug_pg hY hk h1] at e
  have hlt := (Ly1080.ug k ⟨FY a, h1⟩).2
  have hb : FY (Ly0.uG k a) < 1080 := by rw [e]; exact hlt
  refine ⟨fun hc => by rw [hc] at hb; omega, ?_⟩
  rw [fY_eq hb, fY_eq h1]
  exact Fin.ext e

theorem surjY : ∀ j : Fin 1080, ∃ a ∈ OY, fY a = j := by
  intro j
  obtain ⟨h1, h2⟩ := secOK_spec k_ySec j j.2
  refine ⟨⟨SY j, h1⟩, ?_, ?_⟩
  · change FY (SY j) ≠ 65535
    rw [h2]
    omega
  · exact Fin.ext (by simp only [fY]; rw [h2, Nat.mod_eq_of_lt j.2])

theorem fY_SY (j : Fin 1080) : ∃ h : SY j < 66825, fY ⟨SY j, h⟩ = j ∧ (⟨SY j, h⟩ : Fin _) ∈ OY := by
  obtain ⟨h1, h2⟩ := secOK_spec k_ySec j j.2
  refine ⟨h1, Fin.ext (by simp only [fY]; rw [h2, Nat.mod_eq_of_lt j.2]), ?_⟩
  change FY (SY j) ≠ 65535
  rw [h2]
  omega

theorem exists_phiY (h : Ly0.tabCheck = true) (hY : Ly1080.YOK) :
    ∃ φ : ↥(Subgroup.closure (Ly0.uG '' {k | k < 4})) →*
        ↥(Subgroup.closure (Ly1080.ug '' {k | k < 4})),
      Function.Surjective φ ∧
      (∀ k (hk : k < 4), (φ ⟨Ly0.uG k, Subgroup.subset_closure ⟨k, hk, rfl⟩⟩ : Perm (Fin 1080)) =
        Ly1080.ug k) ∧
      ∀ (g : ↥(Subgroup.closure (Ly0.uG '' {k | k < 4}))), ∀ a ∈ OY,
        (g : Perm (Fin Ly0.deg)) a ∈ OY ∧
          fY ((g : Perm (Fin Ly0.deg)) a) = (φ g : Perm (Fin 1080)) (fY a) :=
  CFSG.KC.BlockHom.exists_hom Ly0.uG Ly1080.ug OY fY (compatY h hY) surjY

theorem txWords_len {k : Nat} (hk : k < 4) : (Glue.txWords.getD k []).length = tLen k := by
  interval_cases k <;> decide +kernel

theorem txPt (h : Ly0.tabCheck = true) {k : Nat} (hk : k < 4) (a : Fin Ly0.deg) :
    cdPt (tLen k) (sel4 k (encW (Glue.txWords.getD 0 [])) (encW (Glue.txWords.getD 1 []))
      (encW (Glue.txWords.getD 2 [])) (encW (Glue.txWords.getD 3 []))) a =
      (Glue.txG k a : Nat) := by
  have hc : sel4 k (encW (Glue.txWords.getD 0 [])) (encW (Glue.txWords.getD 1 []))
      (encW (Glue.txWords.getD 2 [])) (encW (Glue.txWords.getD 3 [])) =
      encW (Glue.txWords.getD k []) := by
    interval_cases k <;> rfl
  rw [hc, ← txWords_len hk, cdPt_eq h _ (Glue.txWords_getD_range hk)]
  rfl

@[expose] noncomputable def OT : Set (Fin Ly0.deg) := {a | FT a ≠ 65535}

@[expose] noncomputable def fT (a : Fin Ly0.deg) : Fin 243 := ⟨FT a % 243, Nat.mod_lt _ (by norm_num)⟩

theorem fT_eq {a : Fin Ly0.deg} (h1 : FT a < 243) : fT a = ⟨FT a, h1⟩ :=
  Fin.ext (Nat.mod_eq_of_lt h1)

theorem compatT (h : Ly0.tabCheck = true) (hT : Ly243.trCheck = true) :
    ∀ k < 4, ∀ a ∈ OT, Glue.txG k a ∈ OT ∧ fT (Glue.txG k a) = Ly243.gg k (fT a) := by
  have hb := k_tBlk
  simp only [CFSG.KS.PF.strictB_eqP] at hb
  have hspec := blkOK_spec hb
  intro k hk a ha
  obtain ⟨h1, h2⟩ := hspec a a.2 ha
  have e := h2 k hk
  rw [txPt h hk a, gg_pg hT (by omega) h1] at e
  have hlt := (Ly243.gg k ⟨FT a, h1⟩).2
  have hb' : FT (Glue.txG k a) < 243 := by rw [e]; exact hlt
  refine ⟨fun hc => by rw [hc] at hb'; omega, ?_⟩
  rw [fT_eq hb', fT_eq h1]
  exact Fin.ext e

theorem fT_ST (j : Fin 243) :
    ∃ h : ST j < 66825, fT ⟨ST j, h⟩ = j ∧ (⟨ST j, h⟩ : Fin _) ∈ OT := by
  obtain ⟨h1, h2⟩ := secOK_spec k_tSec j j.2
  refine ⟨h1, Fin.ext (by simp only [fT]; rw [h2, Nat.mod_eq_of_lt j.2]), ?_⟩
  change FT (ST j) ≠ 65535
  rw [h2]
  omega

theorem surjT : ∀ j : Fin 243, ∃ a ∈ OT, fT a = j := by
  intro j
  obtain ⟨h1, h2, h3⟩ := fT_ST j
  exact ⟨_, h3, h2⟩

theorem exists_phiT (h : Ly0.tabCheck = true) (hT : Ly243.trCheck = true) :
    ∃ φ : ↥(Subgroup.closure (Glue.txG '' {k | k < 4})) →*
        ↥(Subgroup.closure (Ly243.gg '' {k | k < 4})),
      Function.Surjective φ ∧
      (∀ k (hk : k < 4), (φ ⟨Glue.txG k, Subgroup.subset_closure ⟨k, hk, rfl⟩⟩ :
        Perm (Fin 243)) = Ly243.gg k) ∧
      ∀ (g : ↥(Subgroup.closure (Glue.txG '' {k | k < 4}))), ∀ a ∈ OT,
        (g : Perm (Fin Ly0.deg)) a ∈ OT ∧
          fT ((g : Perm (Fin Ly0.deg)) a) = (φ g : Perm (Fin 243)) (fT a) :=
  CFSG.KC.BlockHom.exists_hom Glue.txG Ly243.gg OT fT (compatT h hT) surjT

end CertificateChecks.KernelLy

end
