module

public import Certificates.Kernel.HN1408.Words
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.TwoHSData.WordData
public import Certificates.Kernel.Sporadic.OddCore.MulHGlue
public import Certificates.Kernel.Sporadic.OddCore.CentGlue
public import CFSG.Certificates.Kernel.Misc.HexFlatSound
public import CFSG.Certificates.Kernel.Spor.PackWord
public import CFSG.Certificates.Kernel.BfsPinAlg

public section

namespace CFSG.KD.HN1408

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KS.MulH CFSG.KC.BfsPin
open CFSG.EvenSporadicStandard.HNRecog CFSG.Sporadic.Th.Native CFSG.Sporadic.SmallOddCore
open CFSG.Sporadic.Schreier.Native CFSG.Sporadic.SmallOddCore.Native

abbrev Cn (p : Nat) : Prop := canonK 1408 11 (mask 11) (1408 * 11) p = true

theorem hn : szOK 1408 11 = true := by decide

theorem cId : Cn idK := (CFSG.KC.BfsPin.PP.id hn).1

theorem h8 {j : Nat} (hj : j < 7) :
    Cn (H8.F j) ∧ invEqK 1408 11 (mask 11) (1408 * 11) (H8.F j) (H8.F j) = true := by
  have h := allN_spec h8_ok j hj
  exact (bAnd_iff _ _).1 h

theorem h1408T_eq {j : Nat} (hj : j < 7) : h1408T j = tabT (unpack 1408 11 (H8.F j)) := by
  have h := CFSG.KC.Misc.HexFlat.hexT_sound H8.all (by norm_num) j hj
  rw [← H8.eq] at h
  rw [← h, tabT_natArr]
  rfl

theorem idT_eq : idT 1408 = tabT (unpack 1408 11 idK) := by
  rw [idT_tabT, CFSG.KC.BfsPin.idA_eq hn]
  rfl

theorem gens_getD {l : Nat} (h1 : 1 ≤ l) (h7 : l ≤ 7) :
    h1408Gens.getD (l - 1) (idT 1408) = tabT (unpack 1408 11 (L l)) ∧ Cn (L l) := by
  have hl : l - 1 < 7 := by omega
  refine ⟨?_, (h8 hl).1⟩
  have e : h1408Gens.getD (l - 1) (idT 1408) = h1408T (l - 1) := by
    simp [h1408Gens, List.getD_eq_getElem?_getD, hl]
  rw [e, h1408T_eq hl]
  rfl

theorem lettersOK_spec {wd : List Nat} (h : lettersOK wd = true) : ∀ l ∈ wd, 1 ≤ l ∧ l ≤ 7 := by
  intro l hl
  have := List.all_eq_true.1 h l hl
  simpa using this

theorem tabW_eq {wd : List Nat} (h : lettersOK wd = true) :
    tabW wd = tabT (unpack 1408 11 (WK wd)) ∧ Cn (WK wd) :=
  wordTbl_unpack idT_eq cId fun l hl =>
    gens_getD (lettersOK_spec h l hl).1 (lettersOK_spec h l hl).2

theorem mem_gens {g : Table} (hg : g ∈ h1408Gens) :
    ∃ j < 7, g = tabT (unpack 1408 11 (H8.F j)) := by
  simp only [h1408Gens, List.mem_map, List.mem_finRange, true_and] at hg
  obtain ⟨j, rfl⟩ := hg
  exact ⟨j.val, j.isLt, h1408T_eq j.isLt⟩

theorem gen_ok {j : Nat} (hj : j < 7) :
    (permOK 1408 (tabT (unpack 1408 11 (H8.F j))) &&
      invOK 1408 (tabT (unpack 1408 11 (H8.F j))) (invT 1408 (tabT (unpack 1408 11 (H8.F j))))) =
      true := by
  rw [invT_unpack (by norm_num) (h8 hj).2, Bool.and_eq_true]
  exact ⟨permOK_unpack (h8 hj).1 (h8 hj).2, invOK_unpack (h8 hj).1 (h8 hj).1 (h8 hj).2⟩

theorem involOK_eq {X : Nat} (hX : Cn X) :
    involOK 1408 (tabT (unpack 1408 11 X)) = involK X :=
  involOK_unpack' (by norm_num) idT_eq cId hX

theorem invoOK_eq {X : Nat} (hX : Cn X) :
    invoOK 1408 (tabT (unpack 1408 11 X)) = Nat.beq (pc X X) idK := by
  rw [invoOK_eq' (by norm_num), compT_unpack hX hX, idT_eq, tblEq_unpack (canonK_pcomp hX hX) cId]
  rfl

theorem commTT_eq {X Y : Nat} (hX : Cn X) (hY : Cn Y) :
    commTT 1408 (tabT (unpack 1408 11 X)) (tabT (unpack 1408 11 Y)) = commP X Y :=
  commTT_unpack hX hY

theorem tblEq_eq {X Y : Nat} (hX : Cn X) (hY : Cn Y) :
    tblEq 1408 (tabT (unpack 1408 11 X)) (tabT (unpack 1408 11 Y)) = Nat.beq X Y :=
  tblEq_unpack hX hY

theorem ap_eq {X i : Nat} (hX : Cn X) (hi : i < 1408) :
    ap (tabT (unpack 1408 11 X)) i = pt X i := by
  rw [ap_tabT _ (unpack_lt hX), CFSG.KC.Misc.PairCount.unpack_get hi]
  rfl

theorem halves_eq {X : Nat} (hX : Cn X) (h : halvesK X = true) :
    preservesHalves (tabT (unpack 1408 11 X)) = true := by
  unfold preservesHalves
  rw [List.all_eq_true]
  intro k hk
  have hk' : k < 704 := List.mem_range.1 hk
  have h' := allN_spec h k hk'
  simp only [bAnd_iff, Nat.blt_eq, Nat.ble_eq] at h'
  rw [ap_eq hX (by omega), ap_eq hX (by omega)]
  simp [h'.1, h'.2]

theorem swapsZero_eq {X : Nat} (hX : Cn X) :
    swapsZero (tabT (unpack 1408 11 X)) = decide (704 ≤ pt X 0) := by
  unfold swapsZero
  rw [ap_eq hX (by norm_num)]

end CFSG.KD.HN1408

end
