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

theorem prodP_wE : prodP baseP wE = Wu := by
  unfold wE Wu
  rw [prodP_append, prodP_append, prodP_append, prodP_cdE h _ conj_range,
    prodP_cdE h _ invConj_range, prodP_uE h yU yU_range,
    Ly0.wG_invW Ly0.gens0 (fun l hl => (conj_range l hl).1), ← Ly0.gcG_def]
  rfl

theorem prodP_y : prodP baseP (expect.getD 3 []) = Yu := prodP_uE h yU yU_range

theorem prodP_w : prodP baseP (expect.getD 8 []) = Wu := prodP_wE h

theorem prodP_y2 : prodP baseP (expect.getD 7 []) = Yu * Yu := by
  change prodP baseP (uE yU ++ uE yU) = _
  rw [prodP_append, prodP_uE h yU yU_range]
  rfl

theorem prodP_w2 : prodP baseP (expect.getD 10 []) = Wu * Wu := by
  change prodP baseP (wE ++ wE) = _
  rw [prodP_append, prodP_wE h]

theorem prodP_tx {k : Nat} (hk : k < 4) : prodP baseP (expect.getD (11 + k) []) = Glue.txG k := by
  have e : expect.getD (11 + k) [] = cdE (Glue.txWords.getD k []) := by
    interval_cases k <;> rfl
  rw [e, prodP_cdE h _ (Glue.txWords_getD_range hk)]
  rfl

end

theorem prodP_wShort (hM : Ly0.ModelChecks) : prodP baseP wShort = Wu :=
  (lyProdP_eq_base hM (M := wE) (by decide +kernel) (by decide +kernel)
    (by decide +kernel)).trans (prodP_wE hM.tab)

theorem yShort_base (hM : Ly0.ModelChecks) : prodP baseP yShort = prodP baseP (cdE Ly0.wordY) := by
  have h : (Nat.beq (lyPtE yShort 0) (lyPtE (cdE Ly0.wordY) 0) &&
      Nat.beq (lyPtE yShort 3) (lyPtE (cdE Ly0.wordY) 3) &&
      Nat.beq (lyPtE yShort 1) (lyPtE (cdE Ly0.wordY) 1)) = true := by decide +kernel
  simp only [Bool.and_eq_true] at h
  exact lyProdP_eq_base hM h.1.1 h.1.2 h.2

theorem prodP_yShort (hM : Ly0.ModelChecks) : prodP baseP yShort = Ly0.y0G := by
  rw [yShort_base hM, prodP_cdE hM.tab Ly0.wordY (fun l hl => Ly0.decodeWord_mem _ l hl),
    Ly0.y0G_def]

theorem conj_perm (hM : Ly0.ModelChecks) {j : Nat} (hj : j < 9) {A B C D : Perm (Fin Ly0.deg)}
    (hA : prodP baseP (expect.getD (conjList.getD j (0, 0, 0, 0)).1 []) = A)
    (hB : prodP baseP (expect.getD (conjList.getD j (0, 0, 0, 0)).2.1 []) = B)
    (hC : prodP baseP (expect.getD (conjList.getD j (0, 0, 0, 0)).2.2.1 []) = C)
    (hD : prodP baseP (expect.getD (conjList.getD j (0, 0, 0, 0)).2.2.2 []) = D) :
    A * B = C * D := by
  rw [← hA, ← hB, ← hC, ← hD]
  exact lyConj_base hM hj

end CertificateChecks.KernelLy

end
