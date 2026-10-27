module

public import Certificates.Kernel.ONCover.Dce.Folds
public import CFSG.Certificates.Kernel.TwistDce3.Fold
public import CFSG.Certificates.Kernel.TwistDce2.Sound
public import CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.Coordinator.ONCoverInputs

public section

namespace CFSG.KD.ONCoverDce3

open CFSG.KC.TwDce3 CFSG.KC.TwDce2 CFSG.CosetTable
  CFSG.Certificates.CosetEnumeration CFSG.Certificates.TwDce CFSG.LieType.Multipliers
  CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.Coordinator.ONCover
open CFSG.Certificates.TwDce2 (wdVal)

theorem foldRange_add (m : ℕ) : ∀ n a S,
    foldRange PB F INVM BS NB NT PSF PSB RD RW RA WD RJ a (n + m) S =
    foldRange PB F INVM BS NB NT PSF PSB RD RW RA WD RJ (a + n) m
      (foldRange PB F INVM BS NB NT PSF PSB RD RW RA WD RJ a n S)
  | 0, a, S => by simp only [Nat.zero_add, Nat.add_zero]; rfl
  | n + 1, a, S => by
    have e1 : n + 1 + m = (n + m) + 1 := by omega
    have e2 : a + 1 + n = a + (n + 1) := by omega
    rw [e1, CFSG.Certificates.TwDce3.Fold.foldRange_succ, foldRange_add m n (a + 1),
      CFSG.Certificates.TwDce3.Fold.foldRange_succ, e2]

theorem fold_step {n m k S S' : ℕ}
    (h : foldRange PB F INVM BS NB NT PSF PSB RD RW RA WD RJ 0 n 1 = S)
    (hp : foldRange PB F INVM BS NB NT PSF PSB RD RW RA WD RJ n m S = S') (hk : n + m = k) :
    foldRange PB F INVM BS NB NT PSF PSB RD RW RA WD RJ 0 k 1 = S' := by
  rw [← hk, foldRange_add m n 0 1, h, Nat.zero_add, hp]

theorem fold_ok : foldRange PB F INVM BS NB NT PSF PSB RD RW RA WD RJ 0 18934 1 = 775 := by
  have h1 := fold_step (k := 3268) fold0 fold1 (by norm_num)
  have h2 := fold_step (k := 4565) h1 fold2 (by norm_num)
  have h3 := fold_step (k := 6452) h2 fold3 (by norm_num)
  have h4 := fold_step (k := 9331) h3 fold4 (by norm_num)
  have h5 := fold_step (k := 10485) h4 fold5 (by norm_num)
  have h6 := fold_step (k := 11569) h5 fold6 (by norm_num)
  have h7 := fold_step (k := 12803) h6 fold7 (by norm_num)
  have h8 := fold_step (k := 13710) h7 fold8 (by norm_num)
  have h9 := fold_step (k := 14288) h8 fold9 (by norm_num)
  have h10 := fold_step (k := 15236) h9 fold10 (by norm_num)
  have h11 := fold_step (k := 16074) h10 fold11 (by norm_num)
  have h12 := fold_step (k := 16802) h11 fold12 (by norm_num)
  have h13 := fold_step (k := 17180) h12 fold13 (by norm_num)
  have h14 := fold_step (k := 17567) h13 fold14 (by norm_num)
  have h15 := fold_step (k := 17891) h14 fold15 (by norm_num)
  have h16 := fold_step (k := 18175) h15 fold16 (by norm_num)
  have h17 := fold_step (k := 18437) h16 fold17 (by norm_num)
  have h18 := fold_step (k := 18691) h17 fold18 (by norm_num)
  exact fold_step h18 fold19 (by norm_num)

@[expose] def topCode (l : Fin 4 × Bool) : ℕ :=
  [0, 4, 2, 12].getD l.1.val 0 + bif l.2 then 0 else 1

@[expose] def mainTopCodes : List (List ℕ) := (cov ++ rsWs).map (·.map topCode)

@[expose] def wdShape (w : ℕ) : Prop :=
  CFSG.KC.TwDce.wLen w < 2 ^ 12 ∧ (∀ c ∈ wList w, c < 15) ∧
    ((wList w).filter (· != 14) = [] ∨ (wList w).filter (· != 14) = [12, 13] ∨
      (wList w).filter (· != 14) = [13, 12] ∨
      ∃ r ∈ mainTopCodes, r.length = ((wList w).filter (· != 14)).length ∧
        (wList w).filter (· != 14) ∈ rotations r)

@[expose] noncomputable def modB (n : ℕ) : ℕ → Bool :=
  Nat.rec (motive := fun _ => ℕ → Bool) (fun _ => true)
    (fun _ ih a => Nat.beq (WD a) (WD (a % 512)) && ih (a + 1)) n

theorem modB_sound : ∀ n a, modB n a = true → ∀ r < n, WD (a + r) = WD ((a + r) % 512)
  | 0, _, _, r, hr => absurd hr (Nat.not_lt_zero r)
  | n + 1, a, h, r, hr => by
    have h' : (Nat.beq (WD a) (WD (a % 512)) && modB n (a + 1)) = true := h
    simp only [Bool.and_eq_true] at h'
    rcases r with _ | r
    · exact Nat.eq_of_beq_eq_true h'.1
    · have e := modB_sound n (a + 1) h'.2 r (by omega)
      rwa [Nat.add_right_comm, Nat.add_assoc] at e

theorem mod_ok : modB 3584 512 = true := by decide +kernel

theorem wd_mod : ∀ i < 4096, WD i = WD (i % 512) := by
  intro i hi
  by_cases h : i < 512
  · rw [Nat.mod_eq_of_lt h]
  · have e := modB_sound 3584 512 mod_ok (i - 512) (by omega)
    rwa [Nat.add_sub_cancel' (by omega)] at e

set_option maxRecDepth 100000 in
theorem wd_ok512 : ∀ i < 512, wdShape (WD i) := by
  unfold wdShape
  decide +kernel

theorem wd_ok : ∀ i < 4096, CFSG.KC.TwDce.wLen (WD i) < 2 ^ 12 ∧ (∀ c ∈ wList (WD i), c < 15) ∧
    ((wList (WD i)).filter (· != 14) = [] ∨ (wList (WD i)).filter (· != 14) = [12, 13] ∨
      (wList (WD i)).filter (· != 14) = [13, 12] ∨
      ∃ r ∈ mainTopCodes, r.length = ((wList (WD i)).filter (· != 14)).length ∧
        (wList (WD i)).filter (· != 14) ∈ rotations r) := by
  intro i hi
  rw [wd_mod i hi]
  exact wd_ok512 _ (Nat.mod_lt _ (by norm_num))

abbrev onPC : Type := PG 4 mainWs

@[expose] def onHGen (c : ℕ) : Fin 4 := ⟨[0, 2, 1].getD (c / 2) 0 % 4, Nat.mod_lt _ (by norm_num)⟩

@[expose] noncomputable def onX (c : ℕ) : onPC :=
  if c < 6 then (if c % 2 = 0 then PresentedGroup.of (onHGen c) else (PresentedGroup.of (onHGen c))⁻¹)
  else 1

noncomputable abbrev onT : onPC := PresentedGroup.of 3

theorem wdVal_topCode (l : Fin 4 × Bool) : wdVal onX onT (topCode l) =
    cond l.2 (PresentedGroup.of l.1 : onPC) (PresentedGroup.of l.1)⁻¹ := by
  obtain ⟨i, b⟩ := l
  fin_cases i <;> cases b <;> rfl

theorem mem_mainWs_of {r : List (Fin 4 × Bool)} (hr : r ∈ cov ++ rsWs) : r ∈ mainWs :=
  (List.mergeSort_perm _ _).mem_iff.2 hr

theorem evalWord_top {r : List (Fin 4 × Bool)} (hr : r ∈ mainWs) :
    evalWord (wdVal onX onT) (r.map topCode) = 1 := by
  have e : evalWord (wdVal onX onT) (r.map topCode) =
      PresentedGroup.mk {r : FreeGroup (Fin 4) | r ∈ mainWs.map FreeGroup.mk} (FreeGroup.mk r) := by
    rw [CFSG.Sporadic.Recognition.CoverTransfer.mk_eq_lift_of, FreeGroup.lift_mk, evalWord,
      List.map_map]
    congr 1
    exact List.map_congr_left fun l _ => wdVal_topCode l
  rw [e]
  exact PresentedGroup.one_of_mem (List.mem_map_of_mem hr)

theorem wdVal_filter : ∀ l : List ℕ,
    evalWord (wdVal onX onT) l = evalWord (wdVal onX onT) (l.filter (· != 14))
  | [] => rfl
  | c :: l => by
    by_cases h : c = 14
    · subst h
      rw [List.filter_cons_of_neg (by decide), evalWord_cons, ← wdVal_filter l]
      simp [wdVal]
    · rw [List.filter_cons_of_pos (by simpa using h), evalWord_cons, evalWord_cons,
        wdVal_filter l]

theorem wd_one {i : ℕ} (hi : i < 4096) : evalWord (wdVal onX onT) (wList (WD i)) = 1 := by
  rw [wdVal_filter]
  rcases (wd_ok i hi).2.2 with h | h | h | ⟨r, hr, -, hv⟩
  · rw [h]; rfl
  · rw [h]; simp [evalWord, wdVal]
  · rw [h]; simp [evalWord, wdVal]
  · obtain ⟨r', hr', rfl⟩ := List.mem_map.1 hr
    exact CFSG.CosetTable.evalWord_rotation hv (evalWord_top (mem_mainWs_of hr'))

theorem hWD : ∀ i < 4096, CFSG.KC.TwDce.wLen (WD i) < 2 ^ 12 ∧ (∀ c ∈ wList (WD i), c < 15) ∧
    evalWord (wdVal onX onT) (wList (WD i)) = 1 :=
  fun i hi => ⟨(wd_ok i hi).1, (wd_ok i hi).2.1, wd_one hi⟩

end CFSG.KD.ONCoverDce3

end
