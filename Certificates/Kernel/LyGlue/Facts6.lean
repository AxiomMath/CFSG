module

public import Certificates.Kernel.LyGlue.Facts3

public section

namespace CertificateChecks.KernelLy

open CFSG.KC.Enum CFSG.KS CFSG.KC.LyGlue CFSG.Sporadic.Recognition.LyonsSims Equiv Subgroup
  CFSG.Sporadic.Recognition CFSG.Certificates.Kernel.PkCV CFSG.Sporadic.Th

@[expose] noncomputable def Yu : Perm (Fin Ly0.deg) := wordG (wordLetter Ly0.uG) yU

@[expose] noncomputable def Xu : Perm (Fin Ly0.deg) := wordG (wordLetter Ly0.uG) xU

@[expose] noncomputable def Wu : Perm (Fin Ly0.deg) := Ly0.gcG * (Yu * Yu) * Ly0.gcG⁻¹

theorem yU_range : ∀ l ∈ yU, 0 < l ∧ l ≤ 4 := by decide
theorem xU_range : ∀ l ∈ xU, 0 < l ∧ l ≤ 4 := by decide

theorem conj_range : ∀ l ∈ Ly0.wordConj, l ≠ 0 ∧ l.natAbs ≤ 2 :=
  fun l hl => Ly0.decodeWord_mem _ l hl

theorem invConj_range : ∀ l ∈ McLMultiplier.invW Ly0.wordConj, l ≠ 0 ∧ l.natAbs ≤ 2 := by
  intro l hl
  simp only [McLMultiplier.invW, List.mem_reverse, List.mem_map] at hl
  obtain ⟨l', hl', rfl⟩ := hl
  have := conj_range l' hl'
  omega

section

variable (h : Ly0.tabCheck = true)
include h

theorem tl_eq {j : Nat} (hj : j < 15) {g : Perm (Fin Ly0.deg)}
    (hg : prodP baseP (expect.getD j []) = g) (a : Fin Ly0.deg) : tl (tIdx j) a = (g a : Nat) := by
  rw [tl_target h hj, hg]

theorem tl_y (a : Fin Ly0.deg) : tl (tIdx 3) a = (Yu a : Nat) :=
  tl_eq h (j := 3) (by norm_num) (by
    change prodP baseP (uE yU) = _
    exact prodP_uE h yU yU_range) a

theorem tl_x (a : Fin Ly0.deg) : tl (tIdx 4) a = (Xu a : Nat) :=
  tl_eq h (j := 4) (by norm_num) (by
    change prodP baseP (uE xU) = _
    exact prodP_uE h xU xU_range) a

theorem prodP_wE : prodP baseP wE = Wu := by
  unfold wE Wu
  rw [prodP_append, prodP_append, prodP_append, prodP_cdE h _ conj_range,
    prodP_cdE h _ invConj_range, prodP_uE h yU yU_range,
    Ly0.wG_invW Ly0.gens0 (fun l hl => (conj_range l hl).1), ← Ly0.gcG_def]
  rfl

theorem tl_w (a : Fin Ly0.deg) : tl (tIdx 8) a = (Wu a : Nat) :=
  tl_eq h (j := 8) (by norm_num) (by
    change prodP baseP wE = _
    exact prodP_wE h) a

theorem tl_x2 (a : Fin Ly0.deg) : tl (tIdx 9) a = ((Xu * Xu) a : Nat) :=
  tl_eq h (j := 9) (by norm_num) (by
    change prodP baseP (uE xU ++ uE xU) = _
    rw [prodP_append, prodP_uE h xU xU_range]; rfl) a

theorem tl_y2 (a : Fin Ly0.deg) : tl (tIdx 7) a = ((Yu * Yu) a : Nat) :=
  tl_eq h (j := 7) (by norm_num) (by
    change prodP baseP (uE yU ++ uE yU) = _
    rw [prodP_append, prodP_uE h yU yU_range]; rfl) a

theorem tl_w2 (a : Fin Ly0.deg) : tl (tIdx 10) a = ((Wu * Wu) a : Nat) :=
  tl_eq h (j := 10) (by norm_num) (by
    change prodP baseP (wE ++ wE) = _
    rw [prodP_append, prodP_wE h]) a

theorem tl_p {k : Nat} (hk : k < 4) (a : Fin Ly0.deg) :
    tl (tIdx (11 + k)) a = (Glue.txG k a : Nat) := by
  refine tl_eq h (by omega) ?_ a
  have e : expect.getD (11 + k) [] = cdE (Glue.txWords.getD k []) := by
    interval_cases k <;> rfl
  rw [e, prodP_cdE h _ (Glue.txWords_getD_range hk)]
  rfl

theorem conj_perm {j : Nat} (hj : j < 13) {A B C D : Perm (Fin Ly0.deg)}
    (hA : ∀ a : Fin Ly0.deg, tl (tIdx (conjList.getD j (0, 0, 0, 0)).1) a = (A a : Nat))
    (hB : ∀ a : Fin Ly0.deg, tl (tIdx (conjList.getD j (0, 0, 0, 0)).2.1) a = (B a : Nat))
    (hC : ∀ a : Fin Ly0.deg, tl (tIdx (conjList.getD j (0, 0, 0, 0)).2.2.1) a = (C a : Nat))
    (hD : ∀ a : Fin Ly0.deg, tl (tIdx (conjList.getD j (0, 0, 0, 0)).2.2.2) a = (D a : Nat)) :
    A * B = C * D := by
  have hc := cj_all j hj
  unfold conjK at hc
  ext a
  have e := Nat.eq_of_beq_eq_true (allN_spec hc a a.2)
  rw [hB a, hD a, hA (B a), hC (D a)] at e
  simpa [Perm.mul_apply] using e

end

end CertificateChecks.KernelLy

end
