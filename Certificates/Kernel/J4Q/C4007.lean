module

public import CFSG.Sporadic.J4.QT2LocHNative
public import Certificates.Kernel.J4Q.IsetOk
public import Certificates.Kernel.J4Q.IsetBr
public import Certificates.Kernel.J4Q.Orbits
public import Certificates.Kernel.J4Q.LocVec
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelJ4Q

open CFSG.KC.J4Q CFSG.KD.J4Q CFSG.KD.IS CFSG.Sporadic.J4.QT CFSG.Sporadic.J4.QT2

theorem iC_fold {c : Nat} (hc : c < 676) :
    List.foldl vStepB (VGP.take (getN 0 IVC c)) (iChunk c) = VGP.take (getN 0 IVC (c + 1)) := by
  have h := iC_spec hc
  unfold iCK at h
  rw [andB_eq, Bool.and_eq_true] at h
  exact beq_iff_eq.1 h.1

theorem iAll_spec {k : Nat} (hk : k < 43264) : iAllB (iKey k) = true := by
  have hc : Nat.div k 64 < 676 := by change k / 64 < 676; omega
  have h := iC_spec hc
  unfold iCK at h
  rw [andB_eq, Bool.and_eq_true] at h
  have h2 := allR_spec h.2 (Nat.mod k 64) (by change k % 64 < 64; omega)
  have e : Nat.add (Nat.mul 64 (Nat.div k 64)) (Nat.mod k 64) = k := by
    change 64 * (k / 64) + k % 64 = k
    omega
  beta_reduce at h2
  rw [e] at h2
  exact h2

theorem iset_keys : isetT = ((List.range 43264).map iKey).map unpackP := by
  rw [iset_eq, List.map_map]
  rfl

theorem fold_chunks : ∀ m ≤ 676,
    List.foldl vStepB [] ((List.range (64 * m)).map iKey) = VGP.take (getN 0 IVC m)
  | 0, _ => rfl
  | m + 1, hm => by
    have e : 64 * (m + 1) = 64 * m + 64 := by ring
    rw [e, List.range_add, List.map_append, List.foldl_append, fold_chunks m (by omega), List.map_map]
    exact iC_fold (by omega)

theorem vgp_take : VGP.take (getN 0 IVC 676) = VGP := beq_iff_eq.1 (by quickRfl)

theorem vGroups_eq : vGroups = VGL := by
  have h := fold_chunks 676 le_rfl
  rw [vgp_take] at h
  have h2 := fold_U ((List.range 43264).map iKey) []
  rw [h] at h2
  unfold VGL
  rw [← h2, ← iset_keys]
  rfl

theorem lines17_ins : lines17 = (((List.range 2048).filter fun v => v != 0 && fpfL (span4 v) && invL (span4 v)).map
    (fun v => ((span4 v).eraseDups).insertionSort (· ≤ ·))).eraseDups := by
  unfold lines17
  congr 1
  apply List.map_congr_left
  intro v _
  exact List.mergeSort_eq_insertionSort (r := (· ≤ ·)) _

@[expose] noncomputable def ordInsK (a : Nat) (l : List Nat) : List Nat :=
  List.rec (motive := fun _ => List Nat) [a]
    (fun b l' ih => Bool.rec (motive := fun _ => List Nat) (b :: ih) (a :: b :: l') (Nat.ble a b)) l

@[expose] noncomputable def insK (l : List Nat) : List Nat :=
  List.rec (motive := fun _ => List Nat) [] (fun b _ ih => ordInsK b ih) l

theorem ordInsK_eq (a : Nat) : ∀ l : List Nat, ordInsK a l = l.orderedInsert (· ≤ ·) a
  | [] => by
    rw [List.orderedInsert_nil]
    rfl
  | b :: l => by
    rw [List.orderedInsert_cons]
    change Bool.rec (motive := fun _ => List Nat) (b :: ordInsK a l) (a :: b :: l) (Nat.ble a b) = _
    rw [ordInsK_eq a l]
    by_cases h : a ≤ b
    · rw [Nat.ble_eq_true_of_le h, if_pos h]
    · have hf : Nat.ble a b = false := Bool.eq_false_iff.2 fun h' => h (Nat.le_of_ble_eq_true h')
      rw [hf, if_neg h]

theorem insK_eq : ∀ l : List Nat, insK l = l.insertionSort (· ≤ ·)
  | [] => by
    rw [List.insertionSort_nil]
    rfl
  | b :: l => by
    rw [List.insertionSort_cons]
    change ordInsK b (insK l) = _
    rw [insK_eq l, ordInsK_eq]

@[expose] noncomputable def spB (v : Nat) : List Nat := (List.range 16).map fun m =>
  (((if m.testBit 0 = true then v else 0) ^^^ if m.testBit 1 = true then actB (xkP 1) v else 0) ^^^
    if m.testBit 2 = true then actB (xkP 1) (actB (xkP 1) v) else 0) ^^^
      if m.testBit 3 = true then actB (xkP 1) (actB (xkP 1) (actB (xkP 1) v)) else 0

@[expose] noncomputable def LLB : List (List Nat) :=
  (((List.range 2048).filter fun v => v != 0 && (spB v).all (fun s => s == 0 || actB (xkP 1) s != s) &&
    (spB v).all (fun s => (spB v).contains (actB (xkP 1) s))).map
    (fun v => insK ((spB v).eraseDups))).eraseDups

theorem span4_eq (v : Nat) : span4 v = spB v := by
  unfold span4 spB
  simp only [xiT_U, actT_U]

theorem fpfL_eq (S : List Nat) : fpfL S = S.all fun s => s == 0 || actB (xkP 1) s != s := by
  unfold fpfL
  simp only [xiT_U, actT_U]

theorem invL_eq (S : List Nat) : invL S = S.all fun s => S.contains (actB (xkP 1) s) := by
  unfold invL
  simp only [xiT_U, actT_U]

theorem llb_chk : (LLB == L17) = true := by quickRfl

theorem lines17_eq : lines17 = L17 := by
  rw [lines17_ins]
  have e : (((List.range 2048).filter fun v => v != 0 && fpfL (span4 v) && invL (span4 v)).map
      (fun v => ((span4 v).eraseDups).insertionSort (· ≤ ·))).eraseDups = LLB := by
    unfold LLB
    simp only [span4_eq, fpfL_eq, invL_eq, insK_eq]
  rw [e]
  exact beq_iff_eq.1 llb_chk

theorem duadL_eq : duadL = IDL := by
  unfold duadL
  rw [tMasks_eq]
  exact eqLK_spec (by quickRfl)

theorem duad_ok : chkDuad = true := by
  unfold chkDuad
  rw [duadL_eq]
  quickRfl

theorem lines_ok : chkLines = true := by
  unfold chkLines span4 fpfL
  simp only [xiT_U, actT_U]
  quickRfl

theorem v12_chk : (VGL.length == 5 && VGL.all (fun G => G.length == 16 && decide G.Nodup &&
    G.all fun y => y == idT || G.all fun g => (spanT y).contains g)) = true := by
  unfold VGL
  simp only [List.length_map, List.all_map, Function.comp_def, spanT_U, idT_U, beq_U, contains_U]
  quickRfl

theorem iAll_parts {d : List Nat} (hd : d ∈ isetT) :
    vY d = true ∧ (cI 1 d && cI 2 d && cI 3 d && cI 4 d) = true ∧
      (cII 1 d && cII 2 d && cII 3 d && cII 4 d) = true := by
  obtain ⟨k, hk, rfl⟩ := mem_iset.1 hd
  have h := iAll_spec hk
  unfold iAllB at h
  unfold iTS
  rw [vY_U, cI_U (by decide), cI_U (by decide), cI_U (by decide), cI_U (by decide), cII_U (by decide),
    cII_U (by decide), cII_U (by decide), cII_U (by decide)]
  simp only [Bool.and_eq_true] at h ⊢
  exact ⟨h.1.1, h.1.2, h.2⟩

theorem v_ok : chkV = true := by
  unfold chkV
  rw [vGroups_eq]
  rw [Bool.and_eq_true]
  refine ⟨v12_chk, List.all_eq_true.2 fun y hy => ?_⟩
  exact (iAll_parts hy).1

theorem caseI_ok {k : Nat} (hk : ∀ d ∈ isetT, cI k d = true) : chkCaseI k = true := by
  unfold chkCaseI
  rw [vGroups_eq, duadL_eq]
  exact List.all_eq_true.2 fun G hG => List.all_eq_true.2 fun d hd => List.all_eq_true.1 (hk d hd) G hG

theorem caseII_ok {k : Nat} (hk : ∀ d ∈ isetT, cII k d = true) : chkCaseII k = true := by
  unfold chkCaseII
  rw [lines17_eq, duadL_eq]
  exact List.all_eq_true.2 fun d hd => hk d hd

theorem c4007 : chkAll = true := by
  have hI := fun {d} (hd : d ∈ isetT) => iAll_parts hd
  unfold chkAll
  simp only [Bool.and_eq_true]
  refine ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨iset_ok, duad_ok⟩, v_ok⟩, lines_ok⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩
  · exact caseI_ok fun d hd => by have := (hI hd).2.1; simp only [Bool.and_eq_true] at this; exact this.1.1.1
  · exact caseI_ok fun d hd => by have := (hI hd).2.1; simp only [Bool.and_eq_true] at this; exact this.1.1.2
  · exact caseI_ok fun d hd => by have := (hI hd).2.1; simp only [Bool.and_eq_true] at this; exact this.1.2
  · exact caseI_ok fun d hd => by have := (hI hd).2.1; simp only [Bool.and_eq_true] at this; exact this.2
  · exact caseII_ok fun d hd => by have := (hI hd).2.2; simp only [Bool.and_eq_true] at this; exact this.1.1.1
  · exact caseII_ok fun d hd => by have := (hI hd).2.2; simp only [Bool.and_eq_true] at this; exact this.1.1.2
  · exact caseII_ok fun d hd => by have := (hI hd).2.2; simp only [Bool.and_eq_true] at this; exact this.1.2
  · exact caseII_ok fun d hd => by have := (hI hd).2.2; simp only [Bool.and_eq_true] at this; exact this.2

end CertificateChecks.KernelJ4Q

end
