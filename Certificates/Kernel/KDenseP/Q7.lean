module

public import Certificates.Kernel.KDenseP.AgreeB
public import Certificates.Kernel.KDenseP.SepAt
public import Certificates.Kernel.KDense.Basic
public import Certificates.Kernel.KDenseP.Axis.Base
public import CFSG.Certificates.Kernel.KDense.Data.Checks
public import CFSG.Certificates.Kernel.KDenseP.Q7.MonoEChk
public import CFSG.Certificates.Kernel.KDenseP.Q7.C17487
public import CFSG.YGroups.Y443.Native.EdgeNoncommInputs
public import Certificates.Data.TabMSevenQ
import Certificates.Kernel.KDenseP.MonoTabL

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CertificateChecks.KernelKDenseP.Q7

open CFSG.KC CFSG.KC.KDense CFSG.KC.KDenseP CFSG.KC.KDenseP.TwoPoint CFSG.KC.KDenseP.Q7
  CertificateChecks.KernelKDenseP.Axis CertificateChecks.KernelKDenseP.TwoPoint
  CFSG.Monster.AxisCount CFSG.AGLEmbedding.Norton.MON5_7 CFSG.YGroups.Y443 CFSG.YGroups.Y443Native
  CFSG.HardMathSupport.Dickson.I271.TabMSeven

set_option maxRecDepth 100000

theorem monoTab_ok : monoTabOK CFSG.KD.KDF.F CFSG.KD.Q7M.MT = true := by
  kd_monoTabL CFSG.KD.Q7ME t

theorem data_ok : dataOKP CFSG.KD.KDF.F CFSG.KD.Q7M.MT CFSG.KD.KDF.KT CFSG.KD.KDF.TH
    CFSG.KD.KDF.OCT CFSG.KD.KDF.DU1 = true :=
  andB_true CFSG.KD.KDF.th_ok (andB_true CFSG.KD.KDF.oct_ok (andB_true CFSG.KD.KDF.du1_ok
    (andB_true CFSG.KD.KDF.keys_ok (andB_true CFSG.KD.KDF.keyPlanes_ok (andB_true CFSG.KD.KDF.fix_ok
      monoTab_ok)))))

@[expose] def tpWKq : List (ℕ × ℕ) := tpWK 11 0 ++ [(0, 1), (0, 1), (2, 1)]

theorem wk_ok : wkOK CFSG.KD.Q7.c17487.IT tpWKq = true := by quickRfl

theorem tpWKq_eq {x j : ℕ} (hx : x < 3) (hj : j < 11) : tpWKq.getD (11 * x + j) (0, 0) = (x, 0) := by
  unfold tpWKq
  rw [List.getD_eq_getElem?_getD, List.getElem?_append_left (by simp [tpWK]; omega),
    ← List.getD_eq_getElem?_getD]
  exact tpWK_getD_eq hx hj

theorem items : ∀ t < CFSG.KD.Q7.c17487.IT.length,
    let p := tp3 q7Eqs q7Nes
    (∀ g ∈ (p.getD t ([], [])).1, g.validB = true) ∧ (∀ g ∈ (p.getD t ([], [])).2, g.validB = true) ∧
      (CFSG.KD.Q7.c17487.IT[t]! / 4 % 2 = 0 → Cong5D
        (Native.evalWord (p.getD t ([], [])).1 (KernelKDense.wit (CFSG.KD.Q7.c17487.IT[t]! % 4)))
        (Native.evalWord (p.getD t ([], [])).2 (KernelKDense.wit (CFSG.KD.Q7.c17487.IT[t]! % 4)))) ∧
      (CFSG.KD.Q7.c17487.IT[t]! / 4 % 2 = 1 → ∃ k < 196884,
        DVec.res5 (Native.evalWord (p.getD t ([], [])).1
          (KernelKDense.wit (CFSG.KD.Q7.c17487.IT[t]! % 4))) k ≠
        DVec.res5 (Native.evalWord (p.getD t ([], [])).2
          (KernelKDense.wit (CFSG.KD.Q7.c17487.IT[t]! % 4))) k) :=
  itemL data_ok (p := tp3 q7Eqs q7Nes) (by quickRfl) (S := CFSG.KD.Q7.c17487.S)
    (fun x hx => by interval_cases x <;> rfl) (CH := CFSG.KD.Q7.c17487.CH)
    (nch := kd_count% CFSG.KD.Q7.c17487 t) (IT := CFSG.KD.Q7.c17487.IT)
    (by kd_allE CFSG.KD.Q7.c17487 t) (by quickRfl)

theorem ops : ∀ e ∈ q7Eqs, (∀ g ∈ e.1, g.validB = true) ∧
    (∀ g ∈ e.2, g.validB = true) ∧ wordLin e.1 = wordLin e.2 := by
  obtain ⟨hl, hk⟩ := wkOK_spec wk_ok
  have hlen : CFSG.KD.Q7.c17487.IT.length = 36 := by rw [hl]; rfl
  intro e he
  obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem he
  have hj' : j < 11 := hj
  have hx : ∀ x < 3, (∀ g ∈ q7Eqs[j].1, g.validB = true) ∧ (∀ g ∈ q7Eqs[j].2, g.validB = true) ∧
      Cong5D (Native.evalWord q7Eqs[j].1 (KernelKDense.wit x))
        (Native.evalWord q7Eqs[j].2 (KernelKDense.wit x)) := by
    intro x hx
    have ht : 11 * x + j < CFSG.KD.Q7.c17487.IT.length := by rw [hlen]; omega
    obtain ⟨k1, k2⟩ := hk _ ht
    rw [tpWKq_eq hx hj'] at k1 k2
    obtain ⟨v1, v2, c, -⟩ := items _ ht
    have hp := tp3_getD_eq q7Eqs q7Nes hx hj
    change (tp3 q7Eqs q7Nes).getD (11 * x + j) ([], []) = q7Eqs[j] at hp
    rw [hp] at v1 v2 c
    rw [k1] at c
    exact ⟨v1, v2, c k2⟩
  exact ⟨(hx 0 (by norm_num)).1, (hx 0 (by norm_num)).2.1, KernelKDense.Y443.eq_of_three hx⟩

theorem seps {j x : ℕ} (hj : j < 3)
    (hx : ([(0, 1), (0, 1), (2, 1)] : List (ℕ × ℕ)).getD j (0, 0) = (x, 1)) :
    (∀ g ∈ q7Nes[j].1, g.validB = true) ∧ (∀ g ∈ q7Nes[j].2, g.validB = true) ∧
      EdgeNoncomm.moveCheckAux (Native.evalWord q7Nes[j].1 (KernelKDense.wit x))
        (Native.evalWord q7Nes[j].2 (KernelKDense.wit x)) = true := by
  obtain ⟨hl, hk⟩ := wkOK_spec wk_ok
  have hlen : CFSG.KD.Q7.c17487.IT.length = 36 := by rw [hl]; rfl
  have ht : 11 * 3 + j < CFSG.KD.Q7.c17487.IT.length := by rw [hlen]; omega
  obtain ⟨k1, k2⟩ := hk _ ht
  have hw : tpWKq.getD (11 * 3 + j) (0, 0) = (x, 1) := by
    unfold tpWKq
    rw [List.getD_eq_getElem?_getD, List.getElem?_append_right (by simp [tpWK]),
      ← List.getD_eq_getElem?_getD]
    simpa [tpWK] using hx
  rw [hw] at k1 k2
  obtain ⟨v1, v2, -, n⟩ := items _ ht
  have hp := tp3_getD_ne q7Eqs q7Nes (j := j) hj
  change (tp3 q7Eqs q7Nes).getD (11 * 3 + j) ([], []) = q7Nes[j] at hp
  rw [hp] at v1 v2 n
  obtain ⟨k, hk', hne⟩ := n k2
  rw [k1] at hne
  exact ⟨v1, v2, KernelKDenseP.moveCheckAux_of_res5 hk' hne⟩

theorem evalWord_append' (w₁ w₂ : List Native.Gen) (v : Native.DVec) :
    Native.evalWord (w₁ ++ w₂) v = Native.evalWord w₂ (Native.evalWord w₁ v) := by
  simp only [Native.evalWord, Native.evalWordC, List.foldl_append]

theorem evalWord_nil' (v : Native.DVec) : Native.evalWord [] v = v := rfl

theorem evalWord_powL_succ (k : ℕ) (w : List Native.Gen) (v : Native.DVec) :
    Native.evalWord (powL (k + 1) w) v = Native.evalWord (powL k w) (Native.evalWord w v) := by
  simp only [powL, List.replicate_succ, List.flatten_cons, evalWord_append']

theorem evalWord_powL_zero (w : List Native.Gen) (v : Native.DVec) :
    Native.evalWord (powL 0 w) v = v := rfl

theorem op {w₁ w₂ : List Native.Gen} (he : (w₁, w₂) ∈ q7Eqs)
    {v : Native.DVec} (hv : v.D.size = 196884) :
    (Native.evalWord w₁ v).eqv (Native.evalWord w₂ v) = true :=
  have h := ops _ he
  KernelKDenseP.eqv_evalWord h.1 h.2.1 h.2.2 hv

theorem valid_app {w₁ w₂ w₃ : List Native.Gen} (he : (w₁ ++ w₂, w₃) ∈ q7Eqs) :
    (w₁.all fun g => g.validB) = true ∧ (w₂.all fun g => g.validB) = true := by
  have h := (ops _ he).1
  exact ⟨List.all_eq_true.2 fun g hg => h g (List.mem_append_left _ hg),
    List.all_eq_true.2 fun g hg => h g (List.mem_append_right _ hg)⟩

@[expose] def chkW (Z F A X T : List Native.Gen) (v : Native.DVec) : Bool :=
  let z1 := Native.evalWord Z v
  let z2 := Native.evalWord Z z1
  let z3 := Native.evalWord Z z2
  let z4 := Native.evalWord Z z3
  let z5 := Native.evalWord Z z4
  let z6 := Native.evalWord Z z5
  let f1 := Native.evalWord F v
  let f2 := Native.evalWord F f1
  let f3 := Native.evalWord F f2
  let f4 := Native.evalWord F f3
  let a1 := Native.evalWord A v
  let a2 := Native.evalWord A a1
  let a3 := Native.evalWord A a2
  let x1 := Native.evalWord X v
  let t1 := Native.evalWord T v
  [Z, F, A, X, T].all (fun w => w.all fun g => g.validB) &&
    (Native.evalWord Z z6).eqv v && (Native.evalWord F f4).eqv v &&
    (Native.evalWord T t1).eqv v &&
    (Native.evalWord F z1).eqv (Native.evalWord Z f1) &&
    (Native.evalWord T z1).eqv (Native.evalWord Z t1) &&
    (Native.evalWord T f1).eqv (Native.evalWord F t1) &&
    (Native.evalWord A z1).eqv (Native.evalWord Z a1) &&
    (Native.evalWord X z1).eqv (Native.evalWord Z x1) && (Native.evalWord A a3).eqv t1 &&
    (Native.evalWord X x1).eqv t1 && (Native.evalWord A (Native.evalWord X a1)).eqv x1

theorem qAt_eq_chkW (v : Native.DVec) : qAt v = chkW qZ qF qA qX qT v := rfl

theorem chkW_of {Z F A X T : List Native.Gen} {v : Native.DVec}
    (vZ : (Z.all fun g => g.validB) = true) (vF : (F.all fun g => g.validB) = true)
    (vA : (A.all fun g => g.validB) = true) (vX : (X.all fun g => g.validB) = true)
    (vT : (T.all fun g => g.validB) = true)
    (h1 : (Native.evalWord (powL 7 Z) v).eqv (Native.evalWord [] v) = true)
    (h2 : (Native.evalWord (powL 5 F) v).eqv (Native.evalWord [] v) = true)
    (h3 : (Native.evalWord (T ++ T) v).eqv (Native.evalWord [] v) = true)
    (h4 : (Native.evalWord (Z ++ F) v).eqv (Native.evalWord (F ++ Z) v) = true)
    (h5 : (Native.evalWord (Z ++ T) v).eqv (Native.evalWord (T ++ Z) v) = true)
    (h6 : (Native.evalWord (F ++ T) v).eqv (Native.evalWord (T ++ F) v) = true)
    (h7 : (Native.evalWord (Z ++ A) v).eqv (Native.evalWord (A ++ Z) v) = true)
    (h8 : (Native.evalWord (Z ++ X) v).eqv (Native.evalWord (X ++ Z) v) = true)
    (h9 : (Native.evalWord (powL 4 A) v).eqv (Native.evalWord T v) = true)
    (h10 : (Native.evalWord (powL 2 X) v).eqv (Native.evalWord T v) = true)
    (h11 : (Native.evalWord (A ++ X ++ A) v).eqv (Native.evalWord X v) = true) :
    chkW Z F A X T v = true := by
  simp only [evalWord_append', evalWord_nil', evalWord_powL_succ, evalWord_powL_zero] at h1 h2 h3 h4
  simp only [evalWord_append', evalWord_nil', evalWord_powL_succ, evalWord_powL_zero] at h5 h6 h7 h8
  simp only [evalWord_append', evalWord_nil', evalWord_powL_succ, evalWord_powL_zero] at h9 h10 h11
  simp only [chkW, Bool.and_eq_true]
  refine ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨?_, h1⟩, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩, h9⟩, h10⟩, h11⟩
  simp only [List.all_cons, List.all_nil, vZ, vF, vA, vX, vT, Bool.and_self, Bool.and_true]

theorem qAt_of_ops {v : Native.DVec} (hv : v.D.size = 196884) :
    qAt v = true := by
  have h1 := op (w₁ := powL 7 qZ) (w₂ := []) (by simp only [q7Eqs, List.mem_cons, true_or]) hv
  have h2 := op (w₁ := powL 5 qF) (w₂ := [])
    (by simp only [q7Eqs, List.mem_cons, true_or, or_true]) hv
  have h3 := op (w₁ := qT ++ qT) (w₂ := []) (by simp only [q7Eqs, List.mem_cons, true_or, or_true]) hv
  have h4 := op (w₁ := qZ ++ qF) (w₂ := qF ++ qZ)
    (by simp only [q7Eqs, List.mem_cons, true_or, or_true]) hv
  have h5 := op (w₁ := qZ ++ qT) (w₂ := qT ++ qZ)
    (by simp only [q7Eqs, List.mem_cons, true_or, or_true]) hv
  have h6 := op (w₁ := qF ++ qT) (w₂ := qT ++ qF)
    (by simp only [q7Eqs, List.mem_cons, true_or, or_true]) hv
  have h7 := op (w₁ := qZ ++ qA) (w₂ := qA ++ qZ)
    (by simp only [q7Eqs, List.mem_cons, true_or, or_true]) hv
  have h8 := op (w₁ := qZ ++ qX) (w₂ := qX ++ qZ)
    (by simp only [q7Eqs, List.mem_cons, true_or, or_true]) hv
  have h9 := op (w₁ := powL 4 qA) (w₂ := qT) (by simp only [q7Eqs, List.mem_cons, true_or, or_true]) hv
  have h10 := op (w₁ := powL 2 qX) (w₂ := qT)
    (by simp only [q7Eqs, List.mem_cons, true_or, or_true]) hv
  have h11 := op (w₁ := qA ++ qX ++ qA) (w₂ := qX)
    (by simp only [q7Eqs, List.mem_cons, true_or, or_true]) hv
  have vZF := valid_app (w₁ := qZ) (w₂ := qF) (w₃ := qF ++ qZ)
    (by simp only [q7Eqs, List.mem_cons, true_or, or_true])
  have vZT := valid_app (w₁ := qZ) (w₂ := qT) (w₃ := qT ++ qZ)
    (by simp only [q7Eqs, List.mem_cons, true_or, or_true])
  have vZA := valid_app (w₁ := qZ) (w₂ := qA) (w₃ := qA ++ qZ)
    (by simp only [q7Eqs, List.mem_cons, true_or, or_true])
  have vZX := valid_app (w₁ := qZ) (w₂ := qX) (w₃ := qX ++ qZ)
    (by simp only [q7Eqs, List.mem_cons, true_or, or_true])
  rw [qAt_eq_chkW]
  exact chkW_of vZF.1 vZF.2 vZA.2 vZX.2 vZT.2 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11

theorem moveCheck_of_suffixW {w s : List Native.Gen}
    (hw : ∀ g ∈ w ++ s, g.validB = true) (hs : ∀ g ∈ s, g.validB = true)
    (h : EdgeNoncomm.moveCheckAux (Native.evalWord (w ++ s) (wV ())) (Native.evalWord s (wV ())) = true) :
    EdgeNoncomm.moveCheck w (wV ()) = true := by
  have hw' : ∀ g ∈ w, g.validB = true := fun g hg => hw g (List.mem_append_left _ hg)
  have hne := interp_ne_of_moveCheckAux h
  rw [evalWord_sound _ hw, evalWord_sound _ hs, wordLin_append, LinearEquiv.mul_apply] at hne
  unfold EdgeNoncomm.moveCheck
  rw [Bool.and_eq_true]
  refine ⟨List.all_eq_true.2 hw', moveCheckAux_of_interp_ne
    (KernelKDenseP.size_evalWordC _ w _ KernelKDenseP.size_wV) KernelKDenseP.size_wV fun e => hne ?_⟩
  rw [← evalWord_sound _ hw', e]

open Certificates in
open CFSG.YGroups.Y443 CFSG.YGroups.Y443Native CFSG.HardMathSupport.Dickson.I271.TabMSeven in
theorem c17487 :
    qAt (aV ()) = true ∧ qAt (bV ()) = true ∧ qAt (wV ()) = true ∧
      EdgeNoncomm.moveCheck qZ (aV ()) = true ∧ EdgeNoncomm.moveCheck qF (aV ()) = true ∧
      EdgeNoncomm.moveCheck qT (wV ()) = true := by
  have s0 := seps (j := 0) (x := 0) (by norm_num) rfl
  have s1 := seps (j := 1) (x := 0) (by norm_num) rfl
  have s2 := seps (j := 2) (x := 2) (by norm_num) rfl
  have e0 : KernelKDense.wit 0 = aV () := rfl
  have e2 : KernelKDense.wit 2 = wV () := rfl
  rw [e0] at s0 s1
  rw [e2] at s2
  refine ⟨qAt_of_ops KernelKDenseP.size_aV, qAt_of_ops KernelKDenseP.size_bV,
    qAt_of_ops KernelKDenseP.size_wV, ?_, ?_, ?_⟩
  · exact moveCheck_of_suffix (w := qZ) (s := [.xi, .tau]) s0.1 s0.2.1 s0.2.2
  · exact moveCheck_of_suffix (w := qF) (s := [.xi, .tau]) s1.1 s1.2.1 s1.2.2
  · exact moveCheck_of_suffixW (w := qT) (s := [.tau]) s2.1 s2.2.1 s2.2.2

end CertificateChecks.KernelKDenseP.Q7

end
