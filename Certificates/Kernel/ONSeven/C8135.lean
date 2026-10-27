module

public import Certificates.Kernel.ONSeven.Lin
import CFSG.Certificates.Kernel.Common.Harness
import Mathlib.Tactic.IntervalCases

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSpor.ONS

open CFSG.KC.Enum CFSG.KS CFSG.KS.TW CFSG.KS.ONLin CFSG.ONSchreier CFSG.ONSchreier.Native
  CFSG.Sporadic.ON.Native CFSG.RankThree.Native
open CertificateChecks.KernelSpor.ON (TT UU allBelowN_iff')
open CertificateChecks.KernelSpor.ON3 (LetM invW letM_invW)
open CertificateChecks.KernelSpor.ON8 (L onP)

@[expose] noncomputable def Wl (j : Nat) : Nat → Nat := WW (onSevenLineWords.getD j [])

@[expose] noncomputable def Wr (r : Nat) : Nat → Nat := Wl (onSevenRepIdx.getD r 0)

@[expose] noncomputable def transChk (r : Nat) : Bool :=
  (onSevenTransporterData.getD r #[]).toList.all fun t =>
    decide (1 ≤ t.power) && decide (t.power ≤ 6) && decide (t.line < 57) &&
      onP (fun x => WW t.word (iter (Wr r) t.power x)) (fun x => Wl t.line (WW t.word x))

theorem trans0 : transChk 0 = true := by quickRfl
theorem trans1 : transChk 1 = true := by quickRfl
theorem trans2 : transChk 2 = true := by quickRfl
theorem trans3 : transChk 3 = true := by quickRfl
theorem trans4 : transChk 4 = true := by quickRfl

@[expose] def letOK (w : List Int) : Bool := w.all fun l => l != 0 && decide (l.natAbs ≤ 7)

theorem letM_of {w : List Int} (h : letOK w = true) : LetM 7 w := by
  intro l hl
  have := List.all_eq_true.1 h l hl
  simp only [Bool.and_eq_true, bne_iff_ne, ne_eq, decide_eq_true_eq] at this
  exact this

theorem lets_ok : (onSevenLineWords.toList.all letOK && onSevenSylowWords.toList.all letOK &&
    (onSevenCentWords.toList.all fun a => a.toList.all letOK) &&
    (onSevenNormalWords.toList.all fun a => a.toList.all letOK) &&
    (onSevenTransporterData.toList.all fun a => a.toList.all fun t => letOK t.word) &&
    onSevenConjWords.toList.all letOK &&
    (onSevenBadData.toList.all fun a => a.toList.all fun b => letOK b.2)) = true := by
  decide +kernel

theorem getD_mem {α : Type} [Inhabited α] {a : Array α} {i : Nat} (d : α) (h : i < a.size) :
    a.getD i d ∈ a.toList := by
  rw [getD_eq a d h, getElem!_pos a i h]
  exact Array.getElem_mem_toList h

theorem lets_all {α : Type} {l : List α} {p : α → Bool} (h : l.all p = true) {x : α} (hx : x ∈ l) :
    p x = true :=
  List.all_eq_true.1 h x hx

theorem let_line {j : Nat} (hj : j < 57) : LetM 7 (onSevenLineWords.getD j []) := by
  have h := lets_ok
  simp only [Bool.and_eq_true] at h
  exact letM_of (lets_all h.1.1.1.1.1.1 (getD_mem _ (by
    have : onSevenLineWords.size = 57 := rfl
    omega)))

theorem lineArr_get {j : Nat} (hj : j < 57) {i : Nat} (hi : i < 245520) :
    (onSevenLineArrs[j]!)[i]! = Wl j i := by
  have hs : j < onSevenLineWords.size := by have : onSevenLineWords.size = 57 := rfl; omega
  have e : onSevenLineArrs[j]! = onSevenArr (onSevenLineWords.getD j []) := by
    unfold onSevenLineArrs
    rw [getElem!_pos _ j (by simpa using hs), Array.getElem_map, getD_eq _ _ hs,
      getElem!_pos onSevenLineWords j hs]
  rw [e, arr_get (let_line hj) hi]
  rfl

theorem repIdx_lt {r : Nat} (hr : r < 5) : onSevenRepIdx.getD r 0 < 57 := by
  interval_cases r <;> decide

theorem repArr_get {r : Nat} (hr : r < 5) {i : Nat} (hi : i < 245520) :
    (onSevenRepArr r)[i]! = Wr r i := by
  unfold onSevenRepArr Wr
  rw [← getD_eq onSevenRepIdx 0 (by have : onSevenRepIdx.size = 5 := rfl; omega)]
  exact lineArr_get (repIdx_lt hr) hi

theorem lin_Wl {j : Nat} (hj : j < 57) : L (Wl j) := lin_WW (let_line hj)

theorem lin_Wr {r : Nat} (hr : r < 5) : L (Wr r) := lin_Wl (repIdx_lt hr)

theorem let_trans {r : Nat} (hr : r < 5) {t : ONSevenTransporter}
    (ht : t ∈ (onSevenTransporterData.getD r #[]).toList) : LetM 7 t.word := by
  have h := lets_ok
  simp only [Bool.and_eq_true] at h
  have hs : r < onSevenTransporterData.size := by
    have : onSevenTransporterData.size = 5 := rfl
    omega
  exact letM_of (lets_all (lets_all h.1.1.2 (getD_mem #[] hs)) ht)

theorem trans_check {r : Nat} (hr : r < 5) : onSevenTransCheck r = true := by
  have hc : transChk r = true := by
    interval_cases r
    · exact trans0
    · exact trans1
    · exact trans2
    · exact trans3
    · exact trans4
  have e : onSevenTransporterData[r]! = onSevenTransporterData.getD r #[] :=
    (getD_eq _ _ (by have : onSevenTransporterData.size = 5 := rfl; omega)).symm
  unfold onSevenTransCheck
  unfold transChk at hc
  rw [e, ← Array.all_toList]
  refine List.all_eq_true.2 fun t ht => ?_
  have h := List.all_eq_true.1 hc t ht
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h ⊢
  obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := h
  refine ⟨⟨⟨h1, h2⟩, h3⟩, ?_⟩
  have hw := let_trans hr ht
  exact peq_of_onP (Lin.comp (lin_WW hw) (lin_iter (lin_Wr hr) _))
    (Lin.comp (lin_Wl h3) (lin_WW hw))
    (fun i hi => by
      rw [pcomp_get hi, pow_get (lin_Wr hr) (fun i hi => repArr_get hr hi) _ i hi,
        arr_get hw (lt_of_L (lin_iter (lin_Wr hr) _) hi)])
    (fun i hi => by rw [pcomp_get hi, arr_get hw hi, lineArr_get h3 (WW_lt hi)]) h4

@[expose] def wa : List Int := onSevenSylowWords.getD 0 []
@[expose] def wb : List Int := onSevenSylowWords.getD 1 []
@[expose] def wh : List Int := (onSevenCentWords.getD 0 #[]).getD 2 []

@[expose] noncomputable def Zq (x : Nat) : Nat := WW wa (WW wb (WW (invW wa) (WW (invW wb) x)))

@[expose] noncomputable def kerChk : Bool :=
  !(onP Zq fun x => x) &&
    onP (fun x => Zq (WW wa x)) (fun x => WW wa (Zq x)) &&
    onP (fun x => Zq (WW wb x)) (fun x => WW wb (Zq x)) &&
    onP (fun x => WW wh (WW wa (WW (invW wh) x)))
      (fun x => iter (WW wa) 6 (iter (WW wb) 0 (iter Zq 3 x))) &&
    onP (fun x => WW wh (WW wb (WW (invW wh) x)))
      (fun x => iter (WW wa) 0 (iter (WW wb) 6 (iter Zq 2 x))) &&
    onP (fun x => WW wh (Zq (WW (invW wh) x))) (fun x => iter Zq 1 x)

theorem ker_ok : kerChk = true := by quickRfl

theorem let_wa : LetM 7 wa := letM_of (by decide)
theorem let_wb : LetM 7 wb := letM_of (by decide)
theorem let_wh : LetM 7 wh := letM_of (by decide)

theorem lin_Zq : L Zq :=
  (Lin.comp (lin_WW let_wa) (Lin.comp (lin_WW let_wb)
    (Lin.comp (lin_WW (letM_invW let_wa)) (lin_WW (letM_invW let_wb))))).congr fun _ _ => rfl

theorem map_get (ws : Array (List Int)) {j : Nat} (hj : j < ws.size) :
    (ws.map onSevenArr)[j]! = onSevenArr (ws.getD j []) := by
  rw [getElem!_pos _ j (by simpa using hj), Array.getElem_map, getD_eq _ _ hj, getElem!_pos ws j hj]

theorem qa_eq : onSevenQArrs[0]! = onSevenArr wa := map_get _ (by decide)
theorem qb_eq : onSevenQArrs[1]! = onSevenArr wb := map_get _ (by decide)
theorem h_eq : onSevenHArr = onSevenArr wh := by
  unfold onSevenHArr onSevenCArrs wh
  rw [← getD_eq onSevenCentWords #[] (by decide)]
  exact map_get _ (by decide)

theorem z_get {i : Nat} (hi : i < 245520) : onSevenZArr[i]! = Zq i := by
  unfold onSevenZArr Zq
  rw [qa_eq, qb_eq, pcomp_get hi, inv_get let_wb hi, pcomp_get (WW_lt hi),
    inv_get let_wa (WW_lt hi), pcomp_get (WW_lt (WW_lt hi)), arr_get let_wb (WW_lt (WW_lt hi)),
    arr_get let_wa (WW_lt (WW_lt (WW_lt hi)))]

theorem conj_get {w : List Int} (hw : LetM 7 w) {x : Array Nat} {F : Nat → Nat}
    (hx : ∀ i < 245520, x[i]! = F i) (hF : ∀ i < 245520, F i < 245520) {i : Nat}
    (hi : i < 245520) : (onSevenConj (onSevenArr w) x)[i]! = WW w (F (WW (invW w) i)) := by
  unfold onSevenConj
  rw [pcomp_get hi, inv_get hw hi, pcomp_get (WW_lt hi), hx _ (WW_lt hi),
    arr_get hw (hF _ (WW_lt hi))]

set_option maxHeartbeats 2000000 in
theorem kernel_check : onSevenKernelCheck = true := by
  have h := ker_ok
  unfold kerChk at h
  simp only [Bool.and_eq_true, Bool.not_eq_true'] at h
  obtain ⟨⟨⟨⟨⟨hz, hza⟩, hzb⟩, hha⟩, hhb⟩, hhz⟩ := h
  have ha := fun i (hi : i < 245520) => arr_get let_wa hi
  have hb := fun i (hi : i < 245520) => arr_get let_wb hi
  have lA := lin_WW let_wa
  have lB := lin_WW let_wb
  have lH := lin_WW let_wh
  have lHi := lin_WW (letM_invW let_wh)
  have zl : ∀ i < 245520, Zq i < 245520 := fun i hi => lt_of_L lin_Zq hi
  unfold onSevenKernelCheck
  simp only [Bool.and_eq_true, Bool.not_eq_true']
  have hH : pisInv 245520 onSevenHArr (pinvCand 245520 onSevenHArr) = true := by
    rw [h_eq]
    exact pisInv_word let_wh
  have hA : pisInv 245520 onSevenQArrs[0]! (pinvCand 245520 onSevenQArrs[0]!) = true := by
    rw [qa_eq]
    exact pisInv_word let_wa
  have hB : pisInv 245520 onSevenQArrs[1]! (pinvCand 245520 onSevenQArrs[1]!) = true := by
    rw [qb_eq]
    exact pisInv_word let_wb
  refine ⟨⟨⟨⟨⟨⟨⟨⟨hA, hB⟩, hH⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩
  ·
    rw [Bool.eq_false_iff]
    intro hp
    have e : ∀ i < 245520, Zq i = i := fun i hi => by
      have := allBelowN_iff'.1 hp i hi
      rw [beq_iff_eq, z_get hi, CFSG.KS.PW.pid_get' hi] at this
      exact this
    have : onP Zq (fun x => x) = true := by
      unfold CertificateChecks.KernelSpor.ON8.onP
      refine CFSG.KS.Raw.allN_of_forall fun t ht => ?_
      rw [e _ ((CertificateChecks.KernelSpor.ON8.spans').1 t ht), Nat.beq_refl]
    rw [hz] at this
    exact absurd this (by decide)
  · exact peq_of_onP (Lin.comp lin_Zq lA) (Lin.comp lA lin_Zq)
      (fun i hi => by rw [pcomp_get hi, qa_eq, ha i hi, z_get (WW_lt hi)])
      (fun i hi => by rw [pcomp_get hi, qa_eq, z_get hi, ha _ (zl i hi)]) hza
  · exact peq_of_onP (Lin.comp lin_Zq lB) (Lin.comp lB lin_Zq)
      (fun i hi => by rw [pcomp_get hi, qb_eq, hb i hi, z_get (WW_lt hi)])
      (fun i hi => by rw [pcomp_get hi, qb_eq, z_get hi, hb _ (zl i hi)]) hzb
  · refine peq_of_onP (Lin.comp lH (Lin.comp lA lHi))
      (Lin.comp (lin_iter lA 6) (Lin.comp (lin_iter lB 0) (lin_iter lin_Zq 3)))
      (fun i hi => by rw [h_eq, qa_eq]; exact conj_get let_wh ha (fun _ h => WW_lt h) hi)
      (fun i hi => ?_) hha
    rw [qa_eq, qb_eq, pcomp_get hi, pow_get lin_Zq (fun i hi => z_get hi) 3 i hi,
      pcomp_get (lt_of_L (lin_iter lin_Zq 3) hi),
      pow_get lB hb 0 _ (lt_of_L (lin_iter lin_Zq 3) hi),
      pow_get lA ha 6 _ (lt_of_L (lin_iter lB 0) (lt_of_L (lin_iter lin_Zq 3) hi))]
  · refine peq_of_onP (Lin.comp lH (Lin.comp lB lHi))
      (Lin.comp (lin_iter lA 0) (Lin.comp (lin_iter lB 6) (lin_iter lin_Zq 2)))
      (fun i hi => by rw [h_eq, qb_eq]; exact conj_get let_wh hb (fun _ h => WW_lt h) hi)
      (fun i hi => ?_) hhb
    rw [qa_eq, qb_eq, pcomp_get hi, pow_get lin_Zq (fun i hi => z_get hi) 2 i hi,
      pcomp_get (lt_of_L (lin_iter lin_Zq 2) hi),
      pow_get lB hb 6 _ (lt_of_L (lin_iter lin_Zq 2) hi),
      pow_get lA ha 0 _ (lt_of_L (lin_iter lB 6) (lt_of_L (lin_iter lin_Zq 2) hi))]
  · exact peq_of_onP (Lin.comp lH (Lin.comp lin_Zq lHi)) (lin_iter lin_Zq 1)
      (fun i hi => by rw [h_eq]; exact conj_get let_wh (fun i hi => z_get hi) zl hi)
      (fun i hi => pow_get lin_Zq (fun i hi => z_get hi) 1 i hi) hhz

theorem facts8135 : (onSevenTransCheck 0 = true ∧ onSevenTransCheck 1 = true ∧
    onSevenTransCheck 2 = true ∧ onSevenTransCheck 3 = true ∧ onSevenTransCheck 4 = true) ∧
    onSevenKernelCheck = true :=
  ⟨⟨trans_check (by norm_num), trans_check (by norm_num), trans_check (by norm_num),
    trans_check (by norm_num), trans_check (by norm_num)⟩, kernel_check⟩

end CertificateChecks.KernelSpor.ONS

end
