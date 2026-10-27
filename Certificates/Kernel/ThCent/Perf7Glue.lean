module

public import Certificates.Kernel.ThCent.LGlue
public import Certificates.Kernel.ThCent.Perf7Checks
public import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.ThSeven
public import CFSG.Certificates.Kernel.Th.Spec.Rows

public section

namespace CertificateChecks.KernelThList

open CFSG.Sporadic.Th CFSG.Sporadic.Th.Native CFSG.KC.Th CFSG.KC.Th.BigS CFSG.KC.Th.Spec
  CFSG.KC.ThCent CFSG.KD.ThCent.L CFSG.SectionRank.Native
  CFSG.HardMathSupport.Timmesfeld.SporadicBalance.ThSlpNative
  CFSG.HardMathSupport.Timmesfeld.SporadicBalance.ThSevenNative
  CFSG.HardMathSupport.Timmesfeld.SporadicBalance.ThSevenPerfect
  CFSG.HardMathSupport.Timmesfeld.SporadicBalance.ThSlp CFSG.HardMathSupport.Timmesfeld.SporadicBalance
  CFSG.KD

set_option maxRecDepth 100000


local notation "regsR" => slpRows (rowsOf seedA) (rowsOf seedB) 43 prog7

theorem wf_powRowsN {M : Array V4} (hM : WfRows M) : ∀ e, WfRows (powRowsN M e)
  | 0 => wfRows_idRows
  | e + 1 => by
    rw [powRowsN]
    exact wfRows_mulRows (wf_powRowsN hM e) hM

theorem wf_wordRowsL {gs : Array (Array V4)} {w : List ℕ} (h : ∀ r ∈ w, WfRows gs[r]!) :
    WfRows (wordRowsL gs w) := by
  suffices H : ∀ (w : List ℕ), (∀ r ∈ w, WfRows gs[r]!) → ∀ acc : Array V4, WfRows acc →
      WfRows (w.foldl (fun acc r => mulRows acc gs[r]!) acc) by
    exact H w h _ wfRows_idRows
  intro w
  induction w with
  | nil => intro _ acc hacc; exact hacc
  | cons r w ih =>
    intro hw acc hacc
    rw [List.foldl_cons]
    exact ih (fun y hy => hw y (List.mem_cons_of_mem _ hy)) _
      (wfRows_mulRows hacc (hw r List.mem_cons_self))

theorem wf_slpRows {A B : Array V4} (hA : WfRows A) (hB : WfRows B) {n : ℕ} {prog : List Op}
    (hprog : prog.all (Op.lt n) = true) : ∀ r < n, WfRows (slpRows A B n prog)[r]! := by
  suffices H : ∀ (prog : List Op), prog.all (Op.lt n) = true →
      ∀ (R : Array (Array V4)), R.size = n → (∀ r < n, WfRows R[r]!) →
        (prog.foldl opRows R).size = n ∧ ∀ r < n, WfRows (prog.foldl opRows R)[r]! by
    refine (H prog hprog _ (by simp [initRows]) fun r hr => ?_).2
    rw [initRows, getElem!_pos _ r (by simpa using hr), Array.getElem_ofFn]
    split_ifs
    · exact hA
    · exact hB
    · exact wfRows_idRows
  intro prog
  induction prog with
  | nil => intro _ R hs hR; exact ⟨hs, hR⟩
  | cons op prog ih =>
    intro hp R hs hR
    simp only [List.all_cons, Bool.and_eq_true] at hp
    refine ih hp.2 _ (by rw [opRows_size, hs]) fun r hr => ?_
    have hr' : r < R.size := hs ▸ hr
    cases op with
    | mul i j k =>
      have hp1 := hp.1
      simp only [Op.lt, Bool.and_eq_true, decide_eq_true_eq] at hp1
      obtain ⟨⟨hi, hj⟩, -⟩ := hp1
      simp only [opRows]
      rw [getElem!_setIfInBounds_of_lt hr']
      split_ifs
      · exact wfRows_mulRows (hR i hi) (hR j hj)
      · exact hR r hr
    | pow e i k =>
      have hp1 := hp.1
      simp only [Op.lt, Bool.and_eq_true, decide_eq_true_eq] at hp1
      obtain ⟨hi, -⟩ := hp1
      simp only [opRows]
      rw [getElem!_setIfInBounds_of_lt hr']
      split_ifs
      · exact wf_powRowsN (hR i hi) e
      · exact hR r hr

theorem wf_reg {r : ℕ} (hr : r < 43) : WfRows regsR[r]! :=
  wf_slpRows (wfRows_rowsOf _) (wfRows_rowsOf _) ThSeven.prog7_lt r hr

theorem rowsDiffer_of_ne {X Y : Array V4} (h : rowsMatrix X ≠ rowsMatrix Y) :
    rowsDiffer X Y = true := by
  by_contra hne
  apply h
  have hall : ∀ k < 248, ∀ c < 248, (rowAt X k).testBit c = (rowAt Y k).testBit c := by
    intro k hk c hc
    by_contra e
    apply hne
    unfold rowsDiffer
    simp only [List.any_eq_true, List.mem_range, bne_iff_ne, ne_eq]
    exact ⟨k, hk, c, hc, e⟩
  funext i j
  rw [rowsMatrix_apply, rowsMatrix_apply, V4.toVec_apply, V4.toVec_apply]
  have := hall i.val i.isLt j.val j.isLt
  unfold rowAt at this
  rw [this]


theorem lt_of_mem_regs7 {r : ℕ} (hr : r ∈ regs7) : r < 43 := by
  simp only [regs7, List.mem_cons, List.not_mem_nil, or_false] at hr
  omega

theorem rows_reg {r : ℕ} (hr : r ∈ regs7) : rowsMatrix regsR[r]! = pkMat (V7 r) :=
  (ThSeven.rowsMatrix_regs7.2 r (lt_of_mem_regs7 hr)).trans (mat_R7 r hr)

theorem rows_word {w : List ℕ} (hw : ∀ r ∈ w, r ∈ regs7) :
    rowsMatrix (wordRowsL regsR w) = pkMat (wordR ThS.c ThS.rm ThS.ONE V7 w) :=
  (rowsMatrix_wordRowsL (R := slpJ a b prog7)
    fun r hr => ThSeven.rowsMatrix_regs7.2 r (lt_of_mem_regs7 (hw r hr))).trans (mat_word mat_R7 hw)

theorem wf_word {w : List ℕ} (hw : ∀ r ∈ w, r ∈ regs7) : WfRows (wordRowsL regsR w) :=
  wf_wordRowsL fun r hr => wf_reg (lt_of_mem_regs7 (hw r hr))

theorem rows_Z : rowsMatrix (mulRows regsR[24]! (powRowsN regsR[25]! 6)) = pkMat CFSG.KD.ThCent.W.Z7 :=
  ThSeven.rowsMatrix_z7.trans KernelThCent.mat_z7

theorem wf_Z : WfRows (mulRows regsR[24]! (powRowsN regsR[25]! 6)) :=
  wfRows_mulRows (wf_reg (by norm_num)) (wf_powRowsN (wf_reg (by norm_num)) 6)

theorem eqRows_of_pk {X Y : Array V4} (hX : WfRows X) (hY : WfRows Y) {P Q : ℕ}
    (hP : rowsMatrix X = pkMat P) (hQ : rowsMatrix Y = pkMat Q) (h : Nat.beq P Q = true) :
    eqRows X Y = true :=
  eqRows_of_rowsMatrix_eq hX hY (by rw [hP, hQ, Nat.eq_of_beq_eq_true h])

theorem mem_of_okReg {w : List ℕ} (hw : w.all okReg = true) : ∀ r ∈ w, r ∈ regs7 := by
  intro r hr
  have h := List.all_eq_true.1 hw r hr
  unfold okReg at h
  simp only [Bool.or_eq_true, beq_iff_eq] at h
  rcases h with ((rfl | rfl) | rfl) | rfl <;> decide

theorem invW_okReg {w : List ℕ} (hw : w.all okReg = true) : (invW w).all okReg = true := by
  rw [List.all_eq_true] at hw ⊢
  intro r hr
  simp only [invW, List.mem_reverse, List.mem_map] at hr
  obtain ⟨r0, hr0, rfl⟩ := hr
  have h := hw r0 hr0
  unfold okReg at h ⊢
  simp only [Bool.or_eq_true, beq_iff_eq] at h ⊢
  rcases h with ((rfl | rfl) | rfl) | rfl <;> simp [invReg]

theorem perfAt_of {i : ℕ}
    (hok : ((sWords[i]!).all okReg && (sWords[(sIdx[i]!).1]!).all okReg &&
      (sWords[(sIdx[i]!).2]!).all okReg) = true)
    (hK : perf7At ThS.c ThS.rm ThS.ONE V7 CFSG.KD.ThCent.W.Z7 i = true) :
    perfAt regsR (mulRows regsR[24]! (powRowsN regsR[25]! 6)) i = true := by
  obtain ⟨-, -, -, hk⟩ := KernelThCent.fwd_mats
  simp only [Bool.and_eq_true] at hok
  obtain ⟨⟨hw, hwj⟩, hwk⟩ := hok
  unfold perf7At at hK
  rw [strictF_eq, Bool.and_eq_true] at hK
  obtain ⟨hc, he⟩ := hK
  have mw := mem_of_okReg hw
  have mc : ∀ r ∈ sWords[(sIdx[i]!).1]! ++ sWords[(sIdx[i]!).2]! ++ invW sWords[(sIdx[i]!).1]! ++
      invW sWords[(sIdx[i]!).2]!, r ∈ regs7 := by
    intro r hr
    simp only [List.mem_append] at hr
    rcases hr with ((h | h) | h) | h
    · exact mem_of_okReg hwj r h
    · exact mem_of_okReg hwk r h
    · exact mem_of_okReg (invW_okReg hwj) r h
    · exact mem_of_okReg (invW_okReg hwk) r h
  unfold perfAt
  simp only [Bool.and_eq_true]
  refine ⟨⟨⟨⟨hw, hwj⟩, hwk⟩, ?_⟩, ?_⟩
  · exact eqRows_of_pk (wfRows_mulRows (wf_word mw) wf_Z) (wfRows_mulRows wf_Z (wf_word mw))
      (by rw [rowsMatrix_mulRows, rows_word mw, rows_Z, pkMat_mulB hk])
      (by rw [rowsMatrix_mulRows, rows_word mw, rows_Z, pkMat_mulB hk]) hc
  · exact eqRows_of_pk (wf_word mw) (wf_word mc) (rows_word mw) (rows_word mc) he

theorem thPerfOK_K : thPerfOK = true := by
  obtain ⟨-, -, -, hk⟩ := KernelThCent.fwd_mats
  unfold thPerfOK
  simp only [Bool.and_eq_true, List.all_eq_true, List.mem_range, decide_eq_true_eq]
  refine ⟨⟨⟨?_, ?_⟩, ?_⟩, fun i hi => ⟨⟨?_, ?_⟩, ?_⟩⟩
  · exact eqRows_of_pk (wfRows_mulRows (wf_reg (by norm_num)) (wf_reg (by norm_num)))
      wfRows_idRows (by rw [rowsMatrix_mulRows, rows_reg (by decide), rows_reg (by decide),
        pkMat_mulB hk])
      (by rw [rowsMatrix_idRows, pkMat_one hk]) perf7_inv39
  · exact eqRows_of_pk (wfRows_mulRows (wf_reg (by norm_num)) (wf_reg (by norm_num)))
      wfRows_idRows (by rw [rowsMatrix_mulRows, rows_reg (by decide), rows_reg (by decide),
        pkMat_mulB hk])
      (by rw [rowsMatrix_idRows, pkMat_one hk]) perf7_inv40
  · have mw : ∀ r ∈ sWords[0]!, r ∈ regs7 := mem_of_okReg (by decide)
    have hne := neB_sound hk perf7_s0
    rw [pkMat_one hk] at hne
    apply rowsDiffer_of_ne
    rw [rows_word mw, rowsMatrix_idRows]
    exact hne
  · interval_cases i <;> decide
  · interval_cases i <;> decide
  · interval_cases i
    · exact perfAt_of (by decide) perf7_0
    · exact perfAt_of (by decide) perf7_1
    · exact perfAt_of (by decide) perf7_2
    · exact perfAt_of (by decide) perf7_3
    · exact perfAt_of (by decide) perf7_4
    · exact perfAt_of (by decide) perf7_5

end CertificateChecks.KernelThList
