
module

public import Certificates.Kernel.Fi23M.PsiBase
public import Certificates.Kernel.Fi23M.Matrix
public import Certificates.Kernel.Fi23K.OrbEq
public import CFSG.Perm.ChainSpec
import Certificates.Kernel.Fi23M.TreeK
import Certificates.Kernel.Fi23K.Misc
import CFSG.Certificates.Kernel.Spor.RawOrbEval
import Mathlib

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelFi23M

open CFSG.F3.Native CFSG.Sporadic.Fi23 CFSG.Sporadic.Fi23.Native CFSG.KD.Fi23K CFSG.KC.Fi23K
  CFSG.KS.PC CFSG.KS.PCC CFSG.KS.PEnum CFSG.KC.Enum CFSG.Sporadic.Th.Native CFSG.KS.Raw.Orb

theorem tr_pt {k : ℕ} (hk : k < 31671) (hk0 : k ≠ 0) : tb G 91 k < k ∧
    (tb G 92 k = 1 → tb G 39 (tb G 91 k) = k) ∧ (tb G 92 k ≠ 1 → tb G 40 (tb G 91 k) = k) := by
  have h0 := tree_ok
  unfold CFSG.KD.Fi23K.trK at h0
  have h := allN_iff.1 h0 k hk
  unfold CFSG.KD.Fi23K.trAt at h
  have hb : k.beq 0 = false := by
    cases e : k.beq 0
    · rfl
    · exact absurd (Nat.eq_of_beq_eq_true e) hk0
  rw [bIf_eq, hb, if_neg Bool.false_ne_true, strictB_eq, bAnd_eq, Bool.and_eq_true, bIf_eq] at h
  obtain ⟨h1, h2⟩ := h
  refine ⟨by simpa [Nat.blt_eq] using h1, fun hl => ?_, fun hl => ?_⟩
  · have e : Nat.beq (tb G 92 k) 1 = true := by rw [hl]; rfl
    rw [e, if_pos rfl] at h2
    exact Nat.eq_of_beq_eq_true h2
  · have e : Nat.beq (tb G 92 k) 1 = false := by
      cases e : Nat.beq (tb G 92 k) 1
      · rfl
      · exact absurd (Nat.eq_of_beq_eq_true e) hl
    rw [e, if_neg Bool.false_ne_true, bAnd_eq, Bool.and_eq_true] at h2
    exact Nat.eq_of_beq_eq_true h2.2

section

noncomputable def gk : ℕ → ℕ → PG
  | 0, _ => 1
  | f + 1, k => if k = 0 then 1 else if tb G 92 k = 1 then wα * gk f (tb G 91 k)
      else wβ * gk f (tb G 91 k)

theorem inv_val_of {u : M253ˣ} {m m' : M253} (hu : u.val = m) (hm : m * m' = 1) :
    (u⁻¹).val = m' := by
  have h1 : (u⁻¹).val * u.val = 1 := by rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
  calc (u⁻¹).val = (u⁻¹).val * (m * m') := by rw [hm, mul_one]
    _ = ((u⁻¹).val * u.val) * m' := by rw [hu, mul_assoc]
    _ = m' := by rw [h1, one_mul]

theorem gk_pt : ∀ f k, k < 31671 → tb G 93 k < f → ((phiX (gk f k)) ⟨0, hn⟩).val = k
  | 0, _, _, h => absurd h (Nat.not_lt_zero _)
  | f + 1, k, hk, hd => by
    have e2 : gk (f + 1) k = if k = 0 then 1 else if tb G 92 k = 1 then wα * gk f (tb G 91 k)
        else wβ * gk f (tb G 91 k) := rfl
    by_cases h0 : k = 0
    · rw [if_pos h0] at e2
      rw [e2, map_one, Equiv.Perm.one_apply]
      exact h0.symm
    rw [if_neg h0] at e2
    obtain ⟨hp, hA, hB⟩ := tr_pt hk h0
    have hpN : tb G 91 k < 31671 := by omega
    have hdp : tb G 93 (tb G 91 k) < f := by
      have := (dep_pt hk).2 h0
      omega
    have e : phiX (gk f (tb G 91 k)) ⟨0, hn⟩ = ⟨tb G 91 k, hpN⟩ := Fin.ext (gk_pt f _ hpN hdp)
    by_cases hl : tb G 92 k = 1
    · rw [if_pos hl] at e2
      rw [e2, map_mul, Equiv.Perm.mul_apply, e, phiX_wα _ hpN, hA hl]
    · rw [if_neg hl] at e2
      rw [e2, map_mul, Equiv.Perm.mul_apply, e, phiX_wβ _ hpN, hB hl]

noncomputable abbrev tk (k : ℕ) : PG := gk 200 k

theorem tk_pt {k : ℕ} (hk : k < 31671) : phiX (tk k) ⟨0, hn⟩ = ⟨k, hk⟩ :=
  Fin.ext (gk_pt 200 k hk (dep_pt hk).1)

theorem eq_of_mat {X Y : Array W} (hX : canonM 253 (toVM X) = true)
    (hY : canonM 253 (toVM Y) = true) (h : toMatW 253 X = toMatW 253 Y) : X = Y :=
  toVM_inj (eq_of_canonM hX hY h)

theorem conj_eq {v g : PG} (h : phiX v ⟨0, hn⟩ = phiX g ⟨0, hn⟩) :
    v * wD * v⁻¹ = g * wD * g⁻¹ := by
  have h0 : phiX (g⁻¹ * v) ⟨0, hn⟩ = ⟨0, hn⟩ := by
    rw [map_mul, map_inv, Equiv.Perm.mul_apply, h, ← Equiv.Perm.mul_apply, inv_mul_cancel,
      Equiv.Perm.one_apply]
  have hc := stab_comm h0
  calc v * wD * v⁻¹ = g * ((g⁻¹ * v) * wD) * (g⁻¹ * v)⁻¹ * g⁻¹ := by group
    _ = g * (wD * (g⁻¹ * v)) * (g⁻¹ * v)⁻¹ * g⁻¹ := by rw [hc]
    _ = g * wD * g⁻¹ := by group

end

local notation "sg" => CFSG.KS.PC.sig 31671 (chainLetters orbLit)

noncomputable abbrev lv1 : Array ℕ := CFSG.Perm.Native.levelLetters (chainLetters orbLit) chainBase 1

theorem lv1_toArray : lv1 = (lvK LL BB 24 1).toArray := CFSG.KD.Fi23K.lv1_eq

theorem rep_sg : ∀ l ∈ lv1, CFSG.Sporadic.Th.Rep 31671 (chainLetters orbLit)[l]! (sg l) := by
  intro l hl i hi
  have hl' : l < 24 := by
    have := CFSG.Perm.levelLetters_lt hl
    rwa [letters_TR.1] at this
  rw [CFSG.Sporadic.Th.idx_of_lt _ hi, Equiv.Perm.smul_def, sig_val chain_hyp hl' ⟨i, hi⟩,
    ap_letter chain_hyp hl' hi]

theorem tree1_ok : CFSG.Perm.Native.treeOK 31671 1
    (CFSG.KS.TBfs.tbfsRec 31671 (CNT 1) (PTSJ 1) (POSJ 1) (PARJ 1) (LABJ 1))
    (chainLetters orbLit) lv1 = true := by
  rw [lv1_toArray]
  have hh := hdAll 1 (by change 1 < 7; omega)
  unfold hdAt at hh
  have hp := tree_pts (i := 1) (by omega)
  have hl1 : lvOf 1 = 1 := rfl
  rw [hl1] at hp
  refine (CFSG.KS.TBfs.tbfsK_sound (L := LL) (LV := lvAt LL BB 24 1) (TI := TIJ 1)
    ⟨by simp, fun t ht => ?_⟩ hh hp).2
  have ht' : t < (lvK LL BB 24 1).length := by simpa using ht
  have hm := List.getElem_mem ht'
  have hlt : (lvK LL BB 24 1)[t] < 24 := by
    unfold lvK at hm
    exact List.mem_range.1 (List.mem_filter.1 hm).1
  have e : (lvK LL BB 24 1).toArray[t]! = lvAt LL BB 24 1 t := by
    rw [getElem!_pos _ t (by simpa using ht')]
    simp [lvAt, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem ht']
  rw [e]
  have e2 : lvAt LL BB 24 1 t = (lvK LL BB 24 1)[t] := by
    simp [lvAt, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem ht']
  rw [e2]
  exact ⟨rfl, by rw [letters_TR.1]; exact hlt, fun x hx => ((letters_TR.2 _ hlt).2 x hx).1⟩

theorem lettersGroup_le : CFSG.Perm.lettersGroup lv1 (fun l => sg l) ≤ H1 := by
  unfold CFSG.Perm.lettersGroup
  apply Subgroup.closure_mono
  rintro _ ⟨l, hl, rfl⟩
  refine ⟨l, ?_, rfl⟩
  have hl' : l ∈ (lvK LL BB 24 1).toArray := by rwa [lv1_toArray] at hl
  exact List.mem_toArray.1 hl'

theorem tree_move {r cnt : ℕ} {PTS POS PAR LAB : ℕ → ℕ}
    (hT : CFSG.Perm.Native.treeOK 31671 r (CFSG.KS.TBfs.tbfsRec 31671 cnt PTS POS PAR LAB)
      (chainLetters orbLit) lv1 = true) (hr : r < 31671) {t k : ℕ} (hk : k < cnt)
    (htk : r32 PTS k = t) (ht : t < 31671) :
    ∃ s ∈ H1, s ⟨t, ht⟩ = ⟨r, hr⟩ := by
  have hF := CFSG.Perm.treeOK_facts (G := Equiv.Perm (Fin 31671)) (lG := fun l => sg l) rep_sg hT
  have hks : k < (CFSG.KS.TBfs.tbfsRec 31671 cnt PTS POS PAR LAB).pts.size := by
    simp [CFSG.KS.TBfs.tbfsRec, hk]
  have he := hF.elt k hks
  have hp : ap (CFSG.KS.TBfs.tbfsRec 31671 cnt PTS POS PAR LAB).pts k = t := by
    rw [← htk]
    exact CFSG.KS.TBfs.ap_ofFn hk
  rw [hp, CFSG.Sporadic.Th.idx_of_lt _ hr, Equiv.Perm.smul_def] at he
  set g := CFSG.Perm.treeG (CFSG.KS.TBfs.tbfsRec 31671 cnt PTS POS PAR LAB) (fun l => sg l) k
  refine ⟨g⁻¹, Subgroup.inv_mem _ (lettersGroup_le (hF.treeG_mem hks)), ?_⟩
  rw [Equiv.Perm.inv_eq_iff_eq]
  exact Fin.ext he.symm

theorem H1_fix {s : Equiv.Perm (Fin 31671)} (hs : s ∈ H1) : s ⟨0, hn⟩ = ⟨0, hn⟩ ∧ s ∈ Xc := by
  have h := (mem_Gs 1 s).1 (H1_le hs)
  refine ⟨?_, T23_le h.1⟩
  have e : bF hn BB 0 = ⟨0, hn⟩ := Fin.ext (bF_val chain_hyp hn (by norm_num))
  have := h.2 0 (by norm_num)
  rwa [e] at this

theorem move_root {t : ℕ} (ht : t < 31671) (ht0 : t ≠ 0) :
    ∃ s ∈ H1, s ⟨t, ht⟩ = ⟨1, by norm_num⟩ ∨ s ⟨t, ht⟩ = ⟨2, by norm_num⟩ := by
  have h0 := cover_ok
  unfold coverK at h0
  have h := allN_iff.1 h0 t ht
  have hb : t.beq 0 = false := by
    cases e : t.beq 0
    · rfl
    · exact absurd (Nat.eq_of_beq_eq_true e) ht0
  rw [bIf_eq, hb, if_neg Bool.false_ne_true, bIf_eq] at h
  split_ifs at h with h1
  · rw [bAnd_eq, Bool.and_eq_true] at h1
    have hk1 : r32 (TT 1 1) t < CNT 1 := by simpa [Nat.blt_eq] using h1.1
    obtain ⟨s, hs, e⟩ := tree_move tree1_ok (by norm_num) hk1 (Nat.eq_of_beq_eq_true h1.2) ht
    exact ⟨s, hs, Or.inl e⟩
  · rw [bAnd_eq, Bool.and_eq_true] at h
    have hk6 : r32 (TT 6 1) t < CNT 6 := by simpa [Nat.blt_eq] using h.1
    have hT2 : CFSG.Perm.Native.treeOK 31671 2
        (CFSG.KS.TBfs.tbfsRec 31671 (CNT 6) (PTSJ 6) (POSJ 6) (PARJ 6) (LABJ 6))
        (chainLetters orbLit) lv1 = true := t2_eq.2
    obtain ⟨s, hs, e⟩ := tree_move hT2 (by norm_num) hk6 (Nat.eq_of_beq_eq_true h.2) ht
    exact ⟨s, hs, Or.inr e⟩

section

end

end CertificateChecks.KernelFi23M

namespace CFSG.KD.Fi23K

open CertificateChecks.KernelFi23M

end CFSG.KD.Fi23K

end
