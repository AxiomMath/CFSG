module

public import CFSG.Certificates.Kernel.Misc.YamakiAutSound
public import Certificates.Kernel.Misc.YamakiRep.FinalF
public import Certificates.Kernel.Misc.YamakiAut.Checks
public import Certificates.Kernel.Misc.YamakiAut.ChecksQ
public import Certificates.Data.Sp62RecCR1W
public import Certificates.Data.Sp62RecCR1E64

public section

namespace CFSG.KD.YamakiAut

open CFSG.ClassicalInvolution.Sp62Rec CFSG.KC.YamakiAut CFSG.KD.YamakiRepF CFSG.KD.YamakiRep
  CFSG.KC.YamakiS0 CFSG.KC.YamakiA0 CFSG.KC.YamakiRep CFSG.KC.YamakiRepF CFSG.KD.BfsK
  CFSG.KC.BfsEnum CFSG.ClassicalInvolution.Solomon73.Yamaki CFSG.ClassicalInvolution.Q3.AE
open CFSG.KD.Sp62 (MULF ONE)

@[expose] def wli0 : List Nat := [8, 9, 7, 4, 11, 0, 2, 3, 1, 10, 5, 6]

@[expose] def wli1 : List Nat := [11, 8, 4, 3, 1, 0, 5, 2, 10, 9, 7, 6]

@[expose] def qli0 : List Nat := [5, 7, 1, 4, 3, 9, 6, 12, 0, 8, 11, 10, 2, 13]

@[expose] def qli1 : List Nat := [11, 2, 0, 8, 6, 10, 12, 4, 9, 7, 1, 13, 3, 5]

theorem ya550851_h0 : w6code w6Img0 = arrL 12 wl0 := by decide +kernel

theorem ya550851_h1 : w6code w6Img1 = arrL 12 wl1 := by decide +kernel

theorem ya550851_pi : encA 12 wPi = w6code (Wr.allOnes 6) := by decide +kernel

theorem ya550831_h0 : wcode e64H0 = arrL 14 ql0 := by decide +kernel

theorem ya550831_h1 : wcode e64H1 = arrL 14 ql1 := by decide +kernel

theorem ya550851_inv0 : ∀ i < 12, wl0.getD i 0 < 12 ∧ wli0.getD i 0 < 12 ∧
    wl0.getD (wli0.getD i 0) 0 = i ∧ wli0.getD (wl0.getD i 0) 0 = i := by decide

theorem ya550851_inv1 : ∀ i < 12, wl1.getD i 0 < 12 ∧ wli1.getD i 0 < 12 ∧
    wl1.getD (wli1.getD i 0) 0 = i ∧ wli1.getD (wl1.getD i 0) 0 = i := by decide

theorem ya550831_inv0 : ∀ i < 14, ql0.getD i 0 < 14 ∧ qli0.getD i 0 < 14 ∧
    ql0.getD (qli0.getD i 0) 0 = i ∧ qli0.getD (ql0.getD i 0) 0 = i := by decide

theorem ya550831_inv1 : ∀ i < 14, ql1.getD i 0 < 14 ∧ qli1.getD i 0 < 14 ∧
    ql1.getD (qli1.getD i 0) 0 = i ∧ qli1.getD (ql1.getD i 0) 0 = i := by decide

theorem ya550851_one : ∀ i < 12, nib wOne i = i := by decide +kernel

theorem ya550831_one : ∀ i < 14, nib qOne i = i := by decide +kernel

theorem ya550851_one' : compL (List.range 12) wOne = wOne := by decide +kernel

theorem ya550831_one' : compL (List.range 14) qOne = qOne := by decide +kernel

theorem ya550851_step : ∀ i < 23040 * 2, recPOS RH 14 2 i < 23040 ∧
    recX RH 14 (recPOS RH 14 2 i) = MULF (recX RH 14 (i / 2)) (RH (12 + i % 2)) := by
  have rows := rows_of_chunks (L := 512) (m := 45)
    (fun q hq => chunkK_of_chunkF (yfHK.all q hq)) (by norm_num)
  intro i hi
  have s := stepAt_facts (step_of_rows (by norm_num) (by norm_num) rows i hi)
  exact ⟨s.2.2.1, s.2.2.2.1⟩

theorem ya550831_step : ∀ i < 10752 * 2, recPOS RN 14 2 i < 10752 ∧
    recX RN 14 (recPOS RN 14 2 i) = MULF (recX RN 14 (i / 2)) (RN (12 + i % 2)) := by
  have rows := rows_of_chunks (L := 512) (m := 21)
    (fun q hq => chunkK_of_chunkF (yfNK.all q hq)) (by norm_num)
  intro i hi
  have s := stepAt_facts (step_of_rows (by norm_num) (by norm_num) rows i hi)
  exact ⟨s.2.2.1, s.2.2.2.1⟩

theorem ya550851_gens : ∀ j < 2, (gH ())[j]! = arrN (RH (12 + j)) := by
  intro j hj
  rw [gH, wordsA_get _ _ (by simpa [hWords] using hj),
    words_gen yfH_gens hWords 12 (by decide) yfH_gen j (by simpa [hWords] using hj)]

theorem ya550831_gens : ∀ j < 2, (gN ())[j]! = arrN (RN (12 + j)) := by
  intro j hj
  rw [gN, wordsA_get _ _ (by simpa [nWords] using hj),
    words_gen yfN_gens nWords 12 (by decide) yfN_gen j (by simpa [nWords] using hj)]

theorem ya550851_aut :
    autOK (enumH ()) (gH ()) #[arrL 12 wl0, arrL 12 wl1]
        (buildF (enumH ()) #[arrL 12 wl0, arrL 12 wl1]) = true ∧
      ∀ t < 23040, (buildF (enumH ()) #[arrL 12 wl0, arrL 12 wl1])[t]! = encA 12 (RW t) :=
  autOK_of_codes (R := RH) (RP := RW) (l0 := wl0) (l1 := wl1) (lr := List.range 12)
    (li0 := wli0) (li1 := wli1) (m := 12) (n := 23040) (ONEP := wOne) (v0 := 31) (v1 := 165)
    enumH_repF.1 (by norm_num) enumH_repF.2.2.1
    enumH_repF.2.2.2.1 enumH_repF.2.2.2.2 ya550851_step (by simp [gH, wordsA, hWords])
    ya550851_gens (by norm_num) rfl rfl (by simp) ya550851_inv0 ya550851_inv1
    (by decide) ya550851_one ya550851_one' ch550851i
    (autAt_of_chunks (L := 512) (M := 45) (fun q hq => by
      have e := ch550851K.all q hq
      unfold ch550851C at e
      exact e) (by norm_num))

theorem ya550831_aut :
    autOK (enumN ()) (gN ()) #[arrL 14 ql0, arrL 14 ql1]
        (buildF (enumN ()) #[arrL 14 ql0, arrL 14 ql1]) = true :=
  (autOK_of_codes (R := RN) (RP := RQ) (l0 := ql0) (l1 := ql1) (lr := List.range 14)
    (li0 := qli0) (li1 := qli1) (m := 14) (n := 10752) (ONEP := qOne) (v0 := 7) (v1 := 114)
    enumN_repF.1 (by norm_num) enumN_repF.2.2.1
    enumN_repF.2.2.2.1 enumN_repF.2.2.2.2 ya550831_step (by simp [gN, wordsA, nWords])
    ya550831_gens (by norm_num) rfl rfl (by simp) ya550831_inv0 ya550831_inv1
    (by decide) ya550831_one ya550831_one' ch550831i
    (autAt_of_chunks (L := 512) (M := 21) (fun q hq => by
      have e := ch550831K.all q hq
      unfold ch550831C at e
      exact e) (by norm_num))).1

theorem w6IsoCheck_holds : w6IsoCheck () = true := by
  have hs : w6Hs () = #[arrL 12 wl0, arrL 12 wl1] := by
    unfold w6Hs
    rw [ya550851_h0, ya550851_h1]
  have hu := ch550851u
  simp only [Bool.and_eq_true, Nat.beq_eq] at hu
  have hl : (enumH ()).lookup (genA ())[5]! = some 22990 := by
    rw [genA_eq12 yfH_gens (by norm_num), ← hu.1]
    exact lookup_of_inv enumH_repF.1 (by norm_num)
  unfold w6IsoCheck
  dsimp only
  rw [hs, ya550851_aut.1, Bool.true_and, decide_eq_true_eq]
  unfold appF
  rw [hl, Option.getD_some, ya550851_aut.2 22990 (by norm_num), hu.2, ya550851_pi]

theorem e64IsoCheck_holds : e64IsoCheck () = true := by
  have hs : e64Hs () = #[arrL 14 ql0, arrL 14 ql1] := by
    unfold e64Hs
    rw [ya550831_h0, ya550831_h1]
  unfold e64IsoCheck
  dsimp only
  rw [hs]
  exact ya550831_aut

end CFSG.KD.YamakiAut

end
