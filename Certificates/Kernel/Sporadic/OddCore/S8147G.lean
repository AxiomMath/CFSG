module

public import Certificates.Kernel.Sporadic.OddCore.S8147E
public import Certificates.Kernel.Sporadic.OddCore.S8147Lite
public import Certificates.Kernel.Sporadic.OddCore.S8147Rnd0
public import Certificates.Kernel.Sporadic.OddCore.S8147Rnd1
public import Certificates.Kernel.Sporadic.OddCore.S8147Rnd2
public import Certificates.Kernel.Sporadic.OddCore.S8147Rnd3
public import Certificates.Kernel.Sporadic.OddCore.S8147Rnd4
public import Certificates.Kernel.Sporadic.OddCore.S8147Rnd5
public import Certificates.Kernel.Sporadic.OddCore.S2301Final
import CFSG.Certificates.Kernel.Common.Harness
import Mathlib.Tactic.IntervalCases

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSpor.S8147

open CFSG.RankThree.Native CFSG.Sporadic.SuzOddCore CFSG.KC.Enum CFSG.KC.N3153 CFSG.KD.S8147
open CFSG.KC.S2301 CFSG.KS.Raw CFSG.Certificates CFSG.Certificates.Native CFSG.Monster.B.Co2
open CFSG.Monster.B.Co2.Native CFSG.KC.Fi22Snd CertificateChecks.KernelSpor

@[expose] noncomputable def col (k : Nat) : Array Nat := colOf 1782 (X k) (Q k)

theorem col_size (k : Nat) : (col k).size = 1782 := colOf_size _ _ _

theorem line12_eq {i : Nat} (hi : i < 6) : suzFiveLineArr i = unpack 1782 12 (SFL12 i) := by
  rw [line_eq hi, bindK_sound (CFSG.KC.Pack.allN_spec bindL i hi)]

theorem line_get {i v : Nat} (hi : i < 6) (hv : v < 1782) : (suzFiveLineArr i)[v]! = tg (SFL12 i) v := by
  rw [line12_eq hi, unpack12_get hv]
  rfl

theorem tlt {i : Nat} (hi : i < 6) : ∀ v < 1782, tg (SFL12 i) v < 1782 := fun v hv =>
  Nat.le_of_ble_eq_true (CFSG.KC.Pack.allN_spec (CFSG.KC.Pack.allN_spec tltL i hi) v hv)

theorem rnd_facts {T k : Nat} (h : rnd T k = true) :
    tabOK 1782 (K (k - 1)) (X (k - 1)) (Q (k - 1)) = true ∧ ordOK 1782 (Q (k - 1)) (O (k - 1)) = true ∧
      roundOK 1782 (X (k - 1)) (Q (k - 1)) (X k) (Q k) T (O (k - 1)) CFSG.KD.S2301.W = true := by
  unfold rnd at h
  obtain ⟨h1, h2⟩ := CFSG.KC.Pack.band_iff.1 h
  obtain ⟨h2, h3⟩ := CFSG.KC.Pack.band_iff.1 h2
  exact ⟨h1, h2, h3⟩

theorem round_eq {i k : Nat}
    (hi : i < 6) (h : rnd (SFL12 i) k = true) :
    refineStepT (suzFiveLineArr i) (col (k - 1)) = col k := by
  obtain ⟨htab, hord, hr⟩ := rnd_facts h
  have hs := round_sound (by norm_num) S2301.rows S2301.symm' S2301.masks htab hord (tlt hi) hr
  refine S2301.arr_ext (S2301.refineStepT_size _ _) (col_size _) fun v hv => ?_
  rw [S2301.refineStepT_get _ _ hv, S2301.nbr_eq, line12_eq hi]
  exact hs v hv

theorem ind_eq {k p j : Nat} (h : ind k p j = true) : indivPoint (col (k - 1)) p j = col k := by
  rw [indivPoint, col, col, indiv_sound (CFSG.KC.Pack.allN_spec h)]
  rfl

theorem iter_eq {i a : Nat}
    (hi : i < 6) : ∀ m, (∀ j < m, rnd (SFL12 i) (Nat.add a (Nat.add j (nat_lit 1))) = true) →
      refineIterT (suzFiveLineArr i) (col a) m = col (a + m)
  | 0, _ => rfl
  | m + 1, hall => by
    rw [refineIterT, iter_eq hi m fun j hj => hall j (by omega)]
    have e := round_eq hi (hall m (by omega))
    have e1 : Nat.add a (Nat.add m (nat_lit 1)) - 1 = a + m := by
      change a + (m + 1) - 1 = a + m
      omega
    have e2 : Nat.add a (Nat.add m (nat_lit 1)) = a + (m + 1) := rfl
    rw [e1, e2] at e
    exact e

theorem rnds_spec {T a m : Nat} (h : rnds T a m = true) :
    ∀ j < m, rnd T (Nat.add a (Nat.add j (nat_lit 1))) = true :=
  CFSG.KC.Pack.allN_spec h

theorem init_fixed {i k : Nat} (hi : i < 6)
    (h : allN 1782 (initOK true (X k) (Q k) CFSG.KD.S2301.M (SFL12 i)) = true) :
    initColour "fixed" (suzFiveLineArr i) = col k := by
  refine S2301.arr_ext (S2301.initColour_size _ _) (col_size _) fun v hv => ?_
  rw [S2301.initColour_get _ _ hv, col, colOf_get hv, S2301.initOK_true (CFSG.KC.Pack.allN_spec h v hv),
    if_pos (beq_self_eq_true _), line_get hi hv]
  by_cases e : tg (SFL12 i) v = v
  · rw [if_pos (beq_iff_eq.2 e), if_pos e]
  · rw [if_neg fun h => e (beq_iff_eq.1 h), if_neg e]

theorem init_eq {i : Nat} (hi : i < 6) :
    initColour "fixed" (suzFiveLineArr i) = col (caseStart i) := by
  interval_cases i
  · exact init_fixed (by norm_num) init0
  · exact init_fixed (by norm_num) init1
  · exact init_fixed (by norm_num) init2
  · exact init_fixed (by norm_num) init3
  · exact init_fixed (by norm_num) init4
  · exact init_fixed (by norm_num) init5

theorem nSteps_le : ∀ i < 6, nSteps i ≤ 5 := by decide

theorem blocks {i s : Nat} (hi : i < 6) (hs : s ≤ nSteps i) : blkB i s = true := by
  have hs6 : s < 6 := by
    have := nSteps_le i hi
    omega
  have h : caseB i s = true := by
    interval_cases i
    · exact Rnd0.all s hs6
    · exact Rnd1.all s hs6
    · exact Rnd2.all s hs6
    · exact Rnd3.all s hs6
    · exact Rnd4.all s hs6
    · exact Rnd5.all s hs6
  have hb : Nat.ble s (nSteps i) = true := by
    rw [Nat.ble_eq]
    exact hs
  unfold caseB at h
  rw [hb] at h
  exact h

theorem stage_eq {i : Nat}
    (hi : i < 6) : ∀ s ≤ nSteps i,
      suzFiveStage (suzFiveLineArr i) suzFiveInit[i]! suzFiveSteps[i]! s = col (stageIdx i s)
  | 0, _ => by
    have h := blocks hi (Nat.zero_le _)
    rw [blkB, CFSG.KC.Pack.strictB_eq] at h
    rw [suzFiveStage, init_eq hi]
    exact iter_eq hi _ (rnds_spec h)
  | s + 1, hs => by
    have h := blocks hi hs
    rw [blkB, CFSG.KC.Pack.strictB_eq] at h
    obtain ⟨hind, hr⟩ := CFSG.KC.Pack.band_iff.1 h
    rw [suzFiveStage, stage_eq hi s (by omega)]
    have e := ind_eq hind
    have e1 : Nat.add (stageIdx i s) (nat_lit 1) - 1 = stageIdx i s := by
      change stageIdx i s + 1 - 1 = _
      omega
    rw [e1] at e
    change refineIterT (suzFiveLineArr i) (indivPoint (col (stageIdx i s)) (point i s) s)
      (rounds i s) = _
    rw [e]
    exact iter_eq hi _ (rnds_spec hr)

theorem classCount_col {k p : Nat} (htab : tabOK 1782 (K k) (X k) (Q k) = true) (hp : p < 1782) :
    classCount (col k) p = cellCntK 1782 (Q k) (rk (Q k) p) := by
  rw [classCount, cellCntK_eq, ← CFSG.Sporadic.FischerOddCore.card_fin_subtype_eq_countP,
    ← Nat.card_eq_finsetCard]
  refine Nat.card_congr (Equiv.subtypeEquivRight fun w => ?_)
  rw [beq_iff_eq, ← colOf_eq_iff (X := X k) htab w.2 hp]
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  rfl

theorem nodup_of_injOK {k : Nat} (h : injOK 1782 (X k) (Q k) (O k) = true) :
    ((col k).toList.take 1782).Nodup := by
  unfold injOK at h
  obtain ⟨h1, h2⟩ := CFSG.KC.Pack.band_iff.1 h
  have hlt : ∀ i < 1782, rg (O k) i < 1782 := fun i hi =>
    Nat.le_of_ble_eq_true (CFSG.KC.Pack.allN_spec h1 i hi)
  have hinj := inj_of_order (c := col k) hlt fun i hi => by
    rw [col, colOf_get (hlt i (by omega)), colOf_get (hlt (i + 1) (by omega))]
    exact Nat.le_of_ble_eq_true (CFSG.KC.Pack.allN_spec h2 i hi)
  have hl : (col k).toList = (List.range 1782).map fun w => (col k)[w]! := by
    apply List.ext_getElem (by simp [col_size])
    intro j hj1 hj2
    simp only [Array.getElem_toList, List.getElem_map, List.getElem_range]
    rw [getElem!_pos (col k) j (by simpa [col_size] using hj1)]
  rw [List.take_of_length_le (by simp [col_size]), hl]
  exact List.Nodup.map_on (fun v hv w hw e => hinj v (List.mem_range.1 hv) w (List.mem_range.1 hw) e)
    List.nodup_range

theorem point_lt : ∀ i < 6, ∀ s < nSteps i, point i s < 1782 := by decide

theorem last_eq {i : Nat} (hi : i < 6) :
    stageIdx i (nSteps i) = [25, 43, 61, 87, 113, 131].getD i 0 := by
  interval_cases i <;> rfl

theorem graphCheck {i : Nat}
    (hi : i < 6) :
    suzFiveGraphCheck (suzFiveLineArr i) suzFiveInit[i]! suzFiveSteps[i]! = true := by
  have hlen : suzFiveSteps[i]!.length = nSteps i := rfl
  unfold suzFiveGraphCheck
  simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq]
  refine ⟨⟨⟨?_, ?_⟩, ?_⟩, ?_⟩
  · interval_cases i <;> decide
  · rw [CFSG.Monster.B.Co2.allLt_iff]
    intro s hs
    rw [decide_eq_true_eq, stage_eq hi s (by rw [← hlen]; omega)]
    have h := CFSG.KC.Pack.allN_spec (Cell.all i hi) s (by rw [← hlen]; exact hs)
    rw [CFSG.KC.Pack.strictB_eq] at h
    obtain ⟨htab, hle⟩ := CFSG.KC.Pack.band_iff.1 h
    have hp := point_lt i hi s (by rw [← hlen]; exact hs)
    change classCount (col (stageIdx i s)) (point i s) ≤ bound i s
    rw [classCount_col htab hp]
    exact Nat.le_of_ble_eq_true hle
  · rw [hlen, stage_eq hi _ le_rfl, last_eq hi]
    interval_cases i
    · exact nodup_of_injOK inj0
    · exact nodup_of_injOK inj1
    · exact nodup_of_injOK inj2
    · exact nodup_of_injOK inj3
    · exact nodup_of_injOK inj4
    · exact nodup_of_injOK inj5
  · rw [hlen, stage_eq hi _ le_rfl]
    exact col_size _

end CertificateChecks.KernelSpor.S8147

end
