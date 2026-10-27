module

public import Certificates.Kernel.ThCent.Perf7Glue
public import Certificates.Kernel.ThCent.Plane31021Checks
public import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81ThreeOneSporPlaneThData

public section

namespace CertificateChecks.KernelThList

open CFSG.Sporadic.Th CFSG.Sporadic.Th.Native CFSG.KC.Th CFSG.KC.Th.BigS CFSG.KC.Th.Spec
  CFSG.KC.ThCent CFSG.KD.ThCent.L CFSG.SectionRank.Native
  CFSG.HardMathSupport.Timmesfeld.SporadicBalance.ThSlpNative
  CFSG.HardMathSupport.Timmesfeld.SporadicBalance.ThFiveNative
  CFSG.HardMathSupport.Timmesfeld.SporadicBalance.ThSlp CFSG.HardMathSupport.Dickson.I271
  CFSG.LocalAnalysis.RankThreeTheoremC.Hyp111.ThreeOne CFSG.KD

set_option maxRecDepth 100000


local notation "regsP" => slpRows (rowsOf seedA) (rowsOf seedB) 118 prog5

def PkR (X : Array V4) (P : ℕ) : Prop := WfRows X ∧ rowsMatrix X = pkMat P

theorem PkR.mul {X Y : Array V4} {P Q : ℕ} (hX : PkR X P) (hY : PkR Y Q) :
    PkR (mulRows X Y) (mulB ThS.c ThS.rm P Q) := by
  obtain ⟨-, -, -, hk⟩ := KernelThCent.fwd_mats
  exact ⟨wfRows_mulRows hX.1 hY.1, by rw [rowsMatrix_mulRows, hX.2, hY.2, pkMat_mulB hk]⟩

theorem PkR.pow {X : Array V4} {P : ℕ} (hX : PkR X P) {e : ℕ} (he : e < 8) :
    PkR (powRowsN X e) (powB ThS.c ThS.rm ThS.ONE P e (nat_lit 3)) := by
  obtain ⟨-, -, -, hk⟩ := KernelThCent.fwd_mats
  refine ⟨wf_powRowsN hX.1 e, ?_⟩
  rw [CFSG.HardMathSupport.Timmesfeld.SporadicBalance.ThCent.rowsMatrix_powRowsN, hX.2,
    pkMat_powB hk _ _ 3 (by norm_num; exact he)]

theorem PkR.one : PkR (idRows ()) ThS.ONE := by
  obtain ⟨-, -, -, hk⟩ := KernelThCent.fwd_mats
  exact ⟨wfRows_idRows, by rw [rowsMatrix_idRows, pkMat_one hk]⟩

theorem PkR.eqRows {X Y : Array V4} {P Q : ℕ} (hX : PkR X P) (hY : PkR Y Q)
    (h : Nat.beq P Q = true) : eqRows X Y = true :=
  eqRows_of_rowsMatrix_eq hX.1 hY.1 (by rw [hX.2, hY.2, Nat.eq_of_beq_eq_true h])

theorem PkR.differ {X Y : Array V4} {P Q : ℕ} (hX : PkR X P) (hY : PkR Y Q)
    (h : neB ThS.c ThS.rm ThS.ONE P Q = true) : rowsDiffer X Y = true := by
  obtain ⟨-, -, -, hk⟩ := KernelThCent.fwd_mats
  apply rowsDiffer_of_ne
  rw [hX.2, hY.2]
  exact neB_sound hk h

theorem prog5_lt31021 : prog5.all (Op.lt 118) = true := by decide +kernel

theorem slp5 : (regsP).size = 118 ∧ ∀ r < 118, rowsMatrix regsP[r]! =
    CFSG.HardMathSupport.Timmesfeld.SporadicBalance.ThCent.matJ (slpJ a b prog5 r) :=
  rowsMatrix_slpRows CFSG.HardMathSupport.Timmesfeld.SporadicBalance.ThCent.rowsMatrix_seedA
    CFSG.HardMathSupport.Timmesfeld.SporadicBalance.ThCent.rowsMatrix_seedB prog5_lt31021

theorem lt_of_mem_regs5 {r : ℕ} (hr : r ∈ regs5) : r < 118 := by
  simp only [regs5, List.mem_cons, List.not_mem_nil, or_false] at hr
  omega

theorem pk_reg {r : ℕ} (hr : r ∈ regs5) : PkR regsP[r]! (V5 r) :=
  ⟨wf_slpRows (wfRows_rowsOf _) (wfRows_rowsOf _) prog5_lt31021 r (lt_of_mem_regs5 hr),
    (slp5.2 r (lt_of_mem_regs5 hr)).trans (mat_R5 r hr)⟩

theorem pk_word {w : List ℕ} (hw : ∀ r ∈ w, r ∈ regs5) :
    PkR (wordRowsL regsP w) (wordR ThS.c ThS.rm ThS.ONE V5 w) :=
  ⟨wf_wordRowsL fun r hr => (pk_reg (hw r hr)).1,
    (rowsMatrix_wordRowsL (R := slpJ a b prog5)
      fun r hr => slp5.2 r (lt_of_mem_regs5 (hw r hr))).trans (mat_word mat_R5 hw)⟩

theorem pk_seedA : PkR (rowsOf seedA) (ThS.RBf 1) :=
  ⟨wfRows_rowsOf _,
    CFSG.HardMathSupport.Timmesfeld.SporadicBalance.ThCent.rowsMatrix_seedA.trans
      KernelThCent.fwd_mats.1⟩

theorem pk_seedB : PkR (rowsOf seedB) (ThS.RBf 2) :=
  ⟨wfRows_rowsOf _,
    CFSG.HardMathSupport.Timmesfeld.SporadicBalance.ThCent.rowsMatrix_seedB.trans
      KernelThCent.fwd_mats.2.1⟩

theorem size_lt {r : ℕ} (hr : r ∈ regs5) : r < (regsP).size := by
  rw [slp5.1]
  exact lt_of_mem_regs5 hr

theorem eig_parts {c rm ONE : ℕ} {V : ℕ → ℕ} {Xp Yp Cp : ℕ} {e : ℕ × ℕ × ℕ × ℕ}
    (h : eig31021 c rm ONE V Xp Yp Cp e = true) :
    neB c rm ONE (cubeP c rm ONE Xp Yp Cp 0 e.2.1 e.2.2.1) ONE = true ∧
      Nat.beq (powB c rm ONE (cubeP c rm ONE Xp Yp Cp 0 e.2.1 e.2.2.1) 5 (nat_lit 3)) ONE = true ∧
      Nat.beq (mulB c rm (V e.1) (cubeP c rm ONE Xp Yp Cp 0 e.2.1 e.2.2.1))
        (mulB c rm (powB c rm ONE (cubeP c rm ONE Xp Yp Cp 0 e.2.1 e.2.2.1) e.2.2.2 (nat_lit 3))
          (V e.1)) = true := by
  unfold eig31021 at h
  rw [strictF_eq] at h
  obtain ⟨h1, h2⟩ := andB_tt h
  exact ⟨h1, andB_tt h2⟩

theorem eigOK_of {regs : Array (Array V4)} {I X Y C : Array V4} {e : ℕ × ℕ × ℕ × ℕ}
    (hs : e.1 < regs.size) (h1 : rowsDiffer (cubeProd X Y C 0 e.2.1 e.2.2.1) I = true)
    (h2 : eqRows (powRowsN (cubeProd X Y C 0 e.2.1 e.2.2.1) 5) I = true)
    (h3 : eqRows (mulRows regs[e.1]! (cubeProd X Y C 0 e.2.1 e.2.2.1))
      (mulRows (powRowsN (cubeProd X Y C 0 e.2.1 e.2.2.1) e.2.2.2) regs[e.1]!) = true) :
    thPlaneEigOK regs I X Y C e = true := by
  unfold thPlaneEigOK
  simp only [Bool.and_eq_true, decide_eq_true_eq]
  exact ⟨⟨⟨hs, h1⟩, h2⟩, h3⟩

theorem conj_parts {c rm ONE : ℕ} {V : ℕ → ℕ} {Xp Yp Cp : ℕ} {d : List ℕ × ℕ × ℕ} {i j : ℕ}
    (h : conj31021 c rm ONE V Xp Yp Cp d i j = true) :
    Nat.beq (mulB c rm (wordR c rm ONE V d.1) Cp) (mulB c rm Cp (wordR c rm ONE V d.1)) = true ∧
      Nat.beq (mulB c rm (wordR c rm ONE V d.1) Yp)
        (mulB c rm (mulB c rm (powB c rm ONE (mulB c rm
          (powB c rm ONE Xp i (nat_lit 3)) (powB c rm ONE Yp j (nat_lit 3)))
          d.2.1 (nat_lit 3)) (powB c rm ONE Cp d.2.2 (nat_lit 3)))
          (wordR c rm ONE V d.1)) = true := by
  unfold conj31021 at h
  rw [strictF_eq] at h
  exact andB_tt h

theorem conjOK_of {regs : Array (Array V4)} {X Y C : Array V4} {d : List ℕ × ℕ × ℕ} {i j : ℕ}
    (hs : ∀ r ∈ d.1, r < regs.size)
    (h1 : eqRows (mulRows (wordRowsL regs d.1) C) (mulRows C (wordRowsL regs d.1)) = true)
    (h2 : eqRows (mulRows (wordRowsL regs d.1) Y) (mulRows (mulRows (powRowsN (mulRows
      (powRowsN X i) (powRowsN Y j)) d.2.1) (powRowsN C d.2.2)) (wordRowsL regs d.1)) = true) :
    thPlaneConjOK regs X Y C d i j = true := by
  unfold thPlaneConjOK
  simp only [Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq]
  exact ⟨hs, h1, h2⟩

theorem eig_of {X Y C : Array V4} {Xp Yp Cp : ℕ} (pX : PkR X Xp) (pY : PkR Y Yp) (pC : PkR C Cp)
    {e : ℕ × ℕ × ℕ × ℕ} (hr : e.1 ∈ regs5) (hj : e.2.1 < 8) (hk : e.2.2.1 < 8)
    (ha : e.2.2.2 < 8) (h : eig31021 ThS.c ThS.rm ThS.ONE V5 Xp Yp Cp e = true) :
    thPlaneEigOK regsP (idRows ()) X Y C e = true := by
  obtain ⟨h1, h2, h3⟩ := eig_parts h
  have pW : PkR (cubeProd X Y C 0 e.2.1 e.2.2.1)
      (cubeP ThS.c ThS.rm ThS.ONE Xp Yp Cp 0 e.2.1 e.2.2.1) :=
    ((pX.pow (e := 0) (by norm_num)).mul (pY.pow hj)).mul (pC.pow hk)
  have pR := pk_reg hr
  exact eigOK_of (size_lt hr) (pW.differ PkR.one h1) ((pW.pow (e := 5) (by norm_num)).eqRows PkR.one h2)
    ((pR.mul pW).eqRows ((pW.pow ha).mul pR) h3)

theorem conj_of {X Y C : Array V4} {Xp Yp Cp : ℕ} (pX : PkR X Xp) (pY : PkR Y Yp) (pC : PkR C Cp)
    {d : List ℕ × ℕ × ℕ} {i j : ℕ} (hw : ∀ r ∈ d.1, r ∈ regs5) (hi : i < 8) (hj : j < 8)
    (hm : d.2.1 < 8) (hn : d.2.2 < 8) (h : conj31021 ThS.c ThS.rm ThS.ONE V5 Xp Yp Cp d i j = true) :
    thPlaneConjOK regsP X Y C d i j = true := by
  obtain ⟨h1, h2⟩ := conj_parts h
  have pM := pk_word hw
  exact conjOK_of (fun r hr => size_lt (hw r hr)) ((pM.mul pC).eqRows (pC.mul pM) h1)
    ((pM.mul pY).eqRows (((((pX.pow hi).mul (pY.pow hj)).pow hm).mul (pC.pow hn)).mul pM) h2)

theorem eig_facts : ∀ e ∈ thPlaneEig (), e.1 ∈ regs5 ∧ e.2.1 < 8 ∧ e.2.2.1 < 8 ∧ e.2.2.2 < 8 := by
  decide

theorem conj_facts : ∀ k < 25, (∀ r ∈ ((thPlaneConj ())[k]!).1, r ∈ regs5) ∧
    ((thPlaneConj ())[k]!).2.1 < 8 ∧ ((thPlaneConj ())[k]!).2.2 < 8 := by
  decide

theorem conjRow {i : ℕ} (hi : i < 5) : conjRow31021 i = true := by
  interval_cases i
  · exact p31021_conj0
  · exact p31021_conj1
  · exact p31021_conj2
  · exact p31021_conj3
  · exact p31021_conj4

theorem thPlaneOK_K : thPlaneOK () = true := by
  have pX : PkR regsP[94]! (V5 94) := pk_reg (by decide)
  have pY : PkR regsP[105]! (V5 105) := pk_reg (by decide)
  have pC : PkR (mulRows (mulRows (mulRows regsP[94]! regsP[105]!) (powRowsN regsP[94]! 4))
      (powRowsN regsP[105]! 4)) C5 :=
    ((pX.mul pY).mul (pX.pow (e := 4) (by norm_num))).mul (pY.pow (e := 4) (by norm_num))
  unfold thPlaneOK thPlaneCore
  simp only [Bool.and_eq_true]
  refine ⟨⟨⟨⟨⟨⟨⟨?_, by decide⟩, by decide⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩
  · rw [List.all_eq_true]
    intro e he
    have h := List.all_eq_true.1 p31021_eig e he
    rw [strictF_eq] at h
    obtain ⟨h1, h2, h3, h4⟩ := eig_facts e he
    exact eig_of pX pY pC h1 h2 h3 h4 h
  · rw [slp5.1]
    decide
  · rw [slp5.1]
    decide
  · exact (pk_word (by decide)).eqRows pk_seedA p31021_wA
  · exact (pk_word (by decide)).eqRows pk_seedB p31021_wB
  · simp only [List.all_eq_true, List.mem_range]
    intro i hi j hj
    have hrow := conjRow hi
    unfold conjRow31021 at hrow
    rw [strictF_eq, List.all_eq_true] at hrow
    rcases Bool.or_eq_true_iff.1 (hrow j (List.mem_range.2 hj)) with h | h
    · rw [Nat.eq_of_beq_eq_true h]
      rfl
    · obtain ⟨h1, h2, h3⟩ := conj_facts (5 * i + j) (by omega)
      rw [conj_of pX pY pC h1 (by omega) (by omega) h2 h3 h, Bool.or_true]

end CertificateChecks.KernelThList

end
