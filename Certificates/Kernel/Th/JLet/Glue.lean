module

public import Certificates.Kernel.Th.JLet.Chk
public import Certificates.Kernel.Th.DModel.Glue
public import Certificates.Kernel.Th.Fam.Ctx

public section

set_option maxRecDepth 100000

namespace CertificateChecks.KernelTh.JLet

open CFSG.KC.Th CFSG.KC.Th.SurjS CFSG.KC.Th.Spec CFSG.KD.ThS CFSG.Sporadic.Th
open CFSG.Sporadic.Th.Native CFSG.Sporadic.Th.Recog
open CertificateChecks.KernelTh.DModel (codeW codeW_lett codeW_lt wRows_spec)
open CertificateChecks.KernelTh.Fam (thK thCtx)
open CFSG.KC.Th.Expr (TE pk_sound lay_pk wf_rows wf_A)

theorem strictN_eq (y : ℕ) (k : ℕ → ℕ) : CFSG.KC.Loop.strictN y k = k y := by
  cases y <;> rfl

theorem wordV_cons (RB : ℕ → ℕ) (x : ℕ) (w : List ℕ) (acc : ℕ) :
    wordV RB c rm (x :: w) acc = wordV RB c rm w (mulB c rm acc (BigS.letV RB GR IR x)) := by
  change CFSG.KC.Loop.strictN _ _ = _
  rw [strictN_eq]
  rfl

theorem lay_wordV (RB : ℕ → ℕ) : ∀ (w : List ℕ) (acc : ℕ), InLayout acc →
    InLayout (wordV RB c rm w acc)
  | [], _, h => h
  | x :: w, acc, _ => by
    rw [wordV_cons]
    exact lay_wordV RB w _ (inLayout_mulB k0 _ _)

theorem wordMatFrom_eq (RB : ℕ → ℕ) (M : Matrix (Fin 248) (Fin 248) (ZMod 2))
    (w : List (ℕ × Bool)) : wordMatFrom RB M w = M * (w.map (regMat RB)).prod := by
  induction w generalizing M with
  | nil => simp [wordMatFrom]
  | cons l w ih =>
    unfold wordMatFrom at ih ⊢
    rw [List.foldl_cons, ih, List.map_cons, List.prod_cons, mul_assoc]

theorem pk_wordV (RB : ℕ → ℕ) (w : List ℕ) (hw : ∀ x ∈ w, x / 2 < 8) :
    pkMat (wordV RB c rm w ONE) = ((w.map lettOfCode).map (regMat RB)).prod := by
  rw [wordV_spec k0 w ONE hw, pkMat_one k0, wordMatFrom_eq, one_mul]

theorem pk_codeW (RB : ℕ → ℕ) (w : List (Fin 8 × Bool)) :
    pkMat (wordV RB c rm (codeW w) ONE) = (w.map fun l => regMat RB (l.1.val, l.2)).prod := by
  rw [pk_wordV RB _ (codeW_lt w), codeW_lett, List.map_map]
  rfl

theorem code6_lett (w : List (Fin 6 × Bool)) :
    (code6 w).map lettOfCode = w.map fun l => (l.1.val, l.2) := by
  unfold code6
  rw [List.map_map]
  apply List.map_congr_left
  rintro ⟨g, b⟩ -
  cases b
  · refine Prod.ext ?_ ?_
    · change (2 * g.val + 1) / 2 = g.val
      omega
    · change decide ((2 * g.val + 1) % 2 = 0) = false
      exact decide_eq_false (by omega)
  · refine Prod.ext ?_ ?_
    · change (2 * g.val + 0) / 2 = g.val
      omega
    · change decide ((2 * g.val + 0) % 2 = 0) = true
      exact decide_eq_true (by omega)

theorem code6_lt (w : List (Fin 6 × Bool)) : ∀ x ∈ code6 w, x / 2 < 8 := by
  intro x hx
  unfold code6 at hx
  obtain ⟨⟨g, b⟩, -, rfl⟩ := List.mem_map.1 hx
  have hg := g.isLt
  cases b
  · change (2 * g.val + 1) / 2 < 8
    omega
  · change (2 * g.val + 0) / 2 < 8
    omega

theorem pk_code6 (RB : ℕ → ℕ) (w : List (Fin 6 × Bool)) :
    pkMat (wordV RB c rm (code6 w) ONE) = (w.map fun l => regMat RB (l.1.val, l.2)).prod := by
  rw [pk_wordV RB _ (code6_lt w), code6_lett, List.map_map]
  rfl

@[expose] noncomputable def codeL (l : Fin 8 × Bool) : ℕ :=
  Nat.add (Nat.mul 2 l.1.val) (Bool.rec (motive := fun _ => Nat) 1 0 l.2)

theorem hV_eq (l : Fin 8 × Bool) :
    hV (codeL l) = wordV CFSG.KD.ThSj.RB c rm (codeW ((cWord ++ [l]) ++ FreeGroup.invRev cWord))
      ONE := by
  unfold hV cC cI codeW
  rw [List.map_append, List.map_append, List.map_singleton, List.append_assoc,
    List.singleton_append]
  rfl

theorem hsw_pk (g : Fin 8) : pkMat (hV (codeL (g, true))) = rowsMatrix (rowsHsw g) := by
  rw [hV_eq, pk_codeW]
  exact ((wRows_spec (hswWord g)).2).symm

theorem hswInv_pk (g : Fin 8) : pkMat (hV (codeL (g, false))) = rowsMatrix (rowsHswInv g) := by
  rw [hV_eq, pk_codeW]
  exact ((wRows_spec (hswWordInv g)).2).symm

theorem wf_hsw (g : Fin 8) : WfRows (rowsHsw g) := (wRows_spec (hswWord g)).1

theorem wf_hswInv (g : Fin 8) : WfRows (rowsHswInv g) := (wRows_spec (hswWordInv g)).1

theorem RH_reg (l : Fin 8 × Bool) :
    regMat RH (l.1.val, l.2) = rowsMatrix (if l.2 then rowsHsw l.1 else rowsHswInv l.1) := by
  obtain ⟨g, b⟩ := l
  have hg := g.isLt
  unfold regMat RH
  cases b
  · have e : regCode (g.val + 9) = codeL (g, false) := by
      unfold regCode codeL
      have h9 : Nat.blt (g.val + 9) 9 = false := by
        refine Bool.eq_false_iff.2 fun h => ?_
        rw [Nat.blt_eq] at h
        omega
      rw [h9]
      change 2 * (g.val + 9 - 9) + 1 = 2 * g.val + 1
      omega
    simp only [Bool.false_eq_true, ↓reduceIte]
    rw [e, hswInv_pk]
  · have e : regCode (g.val + 1) = codeL (g, true) := by
      unfold regCode codeL
      have h9 : Nat.blt (g.val + 1) 9 = true := by rw [Nat.blt_eq]; omega
      rw [h9]
      change 2 * (g.val + 1 - 1) = 2 * g.val + 0
      omega
    simp only [↓reduceIte]
    rw [e, hsw_pk]

theorem wRowsArr_hsw (w : List (Fin 8 × Bool)) :
    WfRows (wRowsArr (rowsHswArr ()) (rowsHswInvArr ()) w) ∧
      rowsMatrix (wRowsArr (rowsHswArr ()) (rowsHswInvArr ()) w) =
        pkMat (wordV RH c rm (codeW w) ONE) := by
  unfold wRowsArr
  have hsel : ∀ l : Fin 8 × Bool,
      (if l.2 then ((rowsHswArr ())[l.1.val]?).getD idRows
        else ((rowsHswInvArr ())[l.1.val]?).getD idRows) =
        if l.2 then rowsHsw l.1 else rowsHswInv l.1 := by
    rintro ⟨g, b⟩
    cases b
    · exact rowsHswInvArr_get g
    · exact rowsHswArr_get g
  simp only [hsel]
  refine ⟨wfRows_prodRows ?_, ?_⟩
  · intro X hX
    obtain ⟨⟨g, b⟩, -, rfl⟩ := List.mem_map.1 hX
    cases b
    · exact wf_hswInv g
    · exact wf_hsw g
  · rw [Spec.rowsMatrix_prodRows, pk_codeW, List.map_map]
    congr 1
    apply List.map_congr_left
    intro l _
    exact (RH_reg l).symm

theorem lWordN_val (j : Fin 6) : lWordN j.val = lWord j := by
  unfold lWordN
  rw [Fin.ofNat_val_eq_self]

theorem wf_L (j : Fin 6) : WfRows (rowsL j) := (wRowsArr_hsw (lWord j)).1

theorem L_pk (j : Fin 6) : pkMat (lV j.val) = rowsMatrix (rowsL j) := by
  unfold lV
  rw [lWordN_val]
  exact (wRowsArr_hsw (lWord j)).2.symm

theorem wf_LInv (j : Fin 6) : WfRows (rowsLInv j) :=
  (wRowsArr_hsw (FreeGroup.invRev (lWord j))).1

theorem LInv_pk (j : Fin 6) : pkMat (lIV j.val) = rowsMatrix (rowsLInv j) := by
  unfold lIV
  rw [lWordN_val]
  exact (wRowsArr_hsw (FreeGroup.invRev (lWord j))).2.symm

theorem RL_reg (l : Fin 6 × Bool) :
    regMat RL (l.1.val, l.2) = rowsMatrix (if l.2 then rowsL l.1 else rowsLInv l.1) := by
  obtain ⟨g, b⟩ := l
  have hg := g.isLt
  unfold regMat RL
  cases b
  · have h9 : Nat.blt (g.val + 9) 9 = false := by
      refine Bool.eq_false_iff.2 fun h => ?_
      rw [Nat.blt_eq] at h
      omega
    simp only [Bool.false_eq_true, ↓reduceIte]
    rw [h9]
    change pkMat (lIV (g.val + 9 - 9)) = _
    rw [Nat.add_sub_cancel, LInv_pk]
  · have h9 : Nat.blt (g.val + 1) 9 = true := by rw [Nat.blt_eq]; omega
    simp only [↓reduceIte]
    rw [h9]
    change pkMat (lV (g.val + 1 - 1)) = _
    rw [Nat.add_sub_cancel, L_pk]

theorem wRowsArr_L (w : List (Fin 6 × Bool)) :
    WfRows (wRowsArr (rowsLArr ()) (rowsLInvArr ()) w) ∧
      rowsMatrix (wRowsArr (rowsLArr ()) (rowsLInvArr ()) w) =
        pkMat (wordV RL c rm (code6 w) ONE) := by
  unfold wRowsArr
  have hsel : ∀ l : Fin 6 × Bool,
      (if l.2 then ((rowsLArr ())[l.1.val]?).getD idRows
        else ((rowsLInvArr ())[l.1.val]?).getD idRows) =
        if l.2 then rowsL l.1 else rowsLInv l.1 := by
    rintro ⟨g, b⟩
    cases b
    · exact rowsLInvArr_get g
    · exact rowsLArr_get g
  simp only [hsel]
  refine ⟨wfRows_prodRows ?_, ?_⟩
  · intro X hX
    obtain ⟨⟨g, b⟩, -, rfl⟩ := List.mem_map.1 hX
    cases b
    · exact wf_LInv g
    · exact wf_L g
  · rw [Spec.rowsMatrix_prodRows, pk_code6, List.map_map]
    congr 1
    apply List.map_congr_left
    intro l _
    exact (RL_reg l).symm

theorem wj_rows (k : Fin 8) :
    TE.rows (.mul (.word (wJ k)) (.pow .a (εJ k))) = rowsWJ k := rfl

theorem wj_pk (k : Fin 8) : pkMat (wjV k) = rowsMatrix (rowsWJ k) := by
  unfold wjV
  rw [pk_sound thCtx, wj_rows]

theorem wf_WJ (k : Fin 8) : WfRows (rowsWJ k) := by
  rw [← wj_rows]
  exact wf_rows _

theorem a_pk : pkMat aV = rowsMatrix CFSG.Sporadic.Th.Max3.rowsA := pk_sound thCtx .a

theorem eqRows_of_beq {X Y : Array V4} {P Q : ℕ} (hX : WfRows X) (hY : WfRows Y)
    (hP : pkMat P = rowsMatrix X) (hQ : pkMat Q = rowsMatrix Y) (h : Nat.beq P Q = true) :
    eqRows X Y = true := by
  refine eqRows_of_rowsMatrix_eq hX hY ?_
  rw [← hP, ← hQ, Nat.eq_of_beq_eq_true h]

theorem ne_of_notB {X Y : Array V4} {P Q : ℕ} (hPl : InLayout P) (hQl : InLayout Q)
    (hP : pkMat P = rowsMatrix X) (hQ : pkMat Q = rowsMatrix Y)
    (h : BigS.notB (Nat.beq P Q) = true) : rowsMatrix X ≠ rowsMatrix Y := by
  intro e
  have hPQ : P = Q := pkMat_inj hPl hQl (by rw [hP, hQ, e])
  rw [hPQ, Nat.beq_refl] at h
  exact Bool.noConfusion h

theorem comm_of {X Y : Array V4} {P Q : ℕ} (hX : WfRows X) (hY : WfRows Y)
    (hP : pkMat P = rowsMatrix X) (hQ : pkMat Q = rowsMatrix Y) (h : commV P Q = true) :
    eqRows (mulRows X Y) (mulRows Y X) = true := by
  refine eqRows_of_beq (wfRows_mulRows hX hY) (wfRows_mulRows hY hX) ?_ ?_ h
  · rw [pkMat_mulB k0, hP, hQ, rowsMatrix_mulRows]
  · rw [pkMat_mulB k0, hP, hQ, rowsMatrix_mulRows]

theorem lay_hV (x : ℕ) : InLayout (hV x) := lay_wordV _ _ _ (inLayout_one k0)

theorem lay_lV (j : ℕ) : InLayout (lV j) := lay_wordV _ _ _ (inLayout_one k0)

theorem conj0 : eqRows (rowsHsw 0) CFSG.Sporadic.Th.Max3.rowsA = true :=
  eqRows_of_beq (wf_hsw 0) wf_A (hsw_pk 0) a_pk k687002_a

theorem conj1 : rowsMatrix (rowsHsw 1) ≠ rowsMatrix CFSG.Sporadic.Th.Max3.rowsA :=
  ne_of_notB (lay_hV _) (lay_pk thCtx .a) (hsw_pk 1) a_pk k687002_b

theorem conj2 : ∀ i : Fin 8, i ≠ 1 → eqRows (mulRows (rowsHsw 0) (rowsHsw i))
    (mulRows (rowsHsw i) (rowsHsw 0)) = true := by
  intro i hi
  have h : ∀ k : Fin 8, commV (hV (codeL (0, true))) (hV (codeL (k, true))) = true →
      eqRows (mulRows (rowsHsw 0) (rowsHsw k)) (mulRows (rowsHsw k) (rowsHsw 0)) = true :=
    fun k hk => comm_of (wf_hsw 0) (wf_hsw k) (hsw_pk 0) (hsw_pk k) hk
  fin_cases i
  · exact h 0 k687002_c0
  · exact absurd rfl hi
  · exact h 2 k687002_c2
  · exact h 3 k687002_c3
  · exact h 4 k687002_c4
  · exact h 5 k687002_c5
  · exact h 6 k687002_c6
  · exact h 7 k687002_c7

theorem relsV_mem {R : ℕ → ℕ} {ws : List (List ℕ)} (h : relsV R ws = true) :
    ∀ w ∈ ws, Nat.beq (wordV R c rm w ONE) ONE = true := by
  induction ws with
  | nil => intro w hw; simp at hw
  | cons v ws ih =>
    unfold relsV at h
    change Bool.rec false (relsV R ws) (Nat.beq (wordV R c rm v ONE) ONE) = true at h
    intro w hw
    cases hv : Nat.beq (wordV R c rm v ONE) ONE
    · rw [hv] at h
      exact Bool.noConfusion h
    · rw [hv] at h
      rcases List.mem_cons.1 hw with rfl | hw
      · exact hv
      · exact ih h w hw

theorem conj3 : checkLJ () = true := by
  unfold checkLJ
  refine List.all_eq_true.2 fun r hr => ?_
  have hb := relsV_mem k687002_rels (code6 r) (List.mem_map.2 ⟨r, hr, rfl⟩)
  exact eqRows_of_beq (wRowsArr_L r).1 wfRows_idRows (wRowsArr_L r).2.symm
    ((pkMat_one k0).trans rowsMatrix_idRows.symm) hb

theorem conj4 : ∀ i : Fin 6, eqRows (mulRows (rowsL i) (rowsHsw 6))
    (mulRows (rowsHsw 6) (rowsL i)) = true := by
  intro i
  have h : ∀ k : Fin 6, commV (lV k.val) (hV (codeL (6, true))) = true →
      eqRows (mulRows (rowsL k) (rowsHsw 6)) (mulRows (rowsHsw 6) (rowsL k)) = true :=
    fun k hk => comm_of (wf_L k) (wf_hsw 6) (L_pk k) (hsw_pk 6) hk
  fin_cases i
  · exact h 0 k687002_t0
  · exact h 1 k687002_t1
  · exact h 2 k687002_t2
  · exact h 3 k687002_t3
  · exact h 4 k687002_t4
  · exact h 5 k687002_t5

theorem conj5 : rowsMatrix (rowsL 0) ≠ rowsMatrix idRows :=
  ne_of_notB (lay_lV 0) (inLayout_one k0) (L_pk 0) ((pkMat_one k0).trans rowsMatrix_idRows.symm)
    k687002_l0

theorem wj_of (k : Fin 8) (h : Nat.beq (hV (codeL (k, true))) (wjV k) = true) :
    eqRows (rowsHsw k) (rowsWJ k) = true :=
  eqRows_of_beq (wf_hsw k) (wf_WJ k) (hsw_pk k) (wj_pk k) h

theorem conj6 : checkWJ2 () = true := wj_of 2 k687002_w2
theorem conj7 : checkWJ3 () = true := wj_of 3 k687002_w3
theorem conj8 : checkWJ4 () = true := wj_of 4 k687002_w4
theorem conj9 : checkWJ5 () = true := wj_of 5 k687002_w5
theorem conj10 : checkWJ6 () = true := wj_of 6 k687002_w6
theorem conj11 : checkWJ7 () = true := wj_of 7 k687002_w7

end CertificateChecks.KernelTh.JLet

end
