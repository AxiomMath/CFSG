
module

public import Certificates.Kernel.Sporadic.OddCore.S2301Chk
public import Certificates.Kernel.Sporadic.OddCore.S2301Lite
public import Certificates.Kernel.Sporadic.OddCore.S2301Bind
public import Certificates.Kernel.Sporadic.OddCore.S2301Rnd0
public import Certificates.Kernel.Sporadic.OddCore.S2301Rnd1
public import Certificates.Kernel.Sporadic.OddCore.S2301Rnd2
public import Certificates.Kernel.Sporadic.OddCore.S2301Rnd3
public import CFSG.Certificates.Kernel.Fi22Nbr3153Sound
public import CFSG.Certificates.Kernel.Fi22Snd.Colour
public import CFSG.Certificates.Kernel.Suz2301Sound
public import CFSG.Sporadic.SuzOddCore.InvGraphBase
public import CFSG.Sporadic.FischerOddCore.LabelSpec
import CFSG.Certificates.Kernel.Common.Harness
import Mathlib.Tactic.IntervalCases
public import CFSG.Certificates.Kernel.Spor.RawOrbGrp

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSpor.S2301

open CFSG.Sporadic.SuzOddCore CFSG.KC.Enum CFSG.KC.N3153 CFSG.KD.S2301 CFSG.KC.S2301 CFSG.KS.Raw
open CFSG.Certificates CFSG.Certificates.Native CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native
open CFSG.KC.Fi22Snd CertificateChecks.KernelSpor

attribute [local irreducible] CFSG.KD.S2301.R CFSG.KD.S2301.M CFSG.KD.S2301.S CFSG.KD.S2301.T
  CFSG.KD.S2301.X CFSG.KD.S2301.K CFSG.KD.S2301.Q CFSG.KD.S2301.O CFSG.KD.S2301.W GP SuzTP
  invNbr

theorem of_blocks {f : Nat → Bool} (h : ∀ s < 28, blk f s = true) : ∀ x < 1782, f x = true := by
  intro x hx
  have h2 := CFSG.KC.Pack.allBlk_spec (h (x / 64) (by omega)) (x % 64) (Nat.mod_lt _ (by norm_num))
  have e : Nat.add (Nat.mul 64 (x / 64)) (x % 64) = x := by
    change 64 * (x / 64) + x % 64 = x
    omega
  have hb : Nat.blt x 1782 = true := Eq.mpr Nat.blt_eq hx
  rw [e, hb] at h2
  exact h2

theorem rows : ∀ x < 1782, rowOK 1782 416 R M S x = true := of_blocks Row.all

theorem imgs : ∀ k < 3, ∀ x < 1782, imgOK 1782 416 (GP k) R M x = true := by
  intro k hk
  interval_cases k
  · exact of_blocks Img0.all
  · exact of_blocks Img1.all
  · exact of_blocks Img2.all

theorem masks : ∀ x < 1782, maskOK 416 R W x = true := of_blocks Mask.all

theorem b0_eq : b0Arr = unpack 1782 12 (GP 0) := by
  rw [Suz2306.b0Arr_eq, bindK_sound bind0]

theorem b1_eq : b1Arr = unpack 1782 12 (GP 1) := by
  rw [Suz2306.b1Arr_eq, bindK_sound bind1]

theorem v_eq : vArr = unpack 1782 12 (GP 2) := by
  rw [Suz2306.vArr_eq, bindK_sound bind2]

theorem gens_eq : ∀ k < 2, (#[b0Arr, b1Arr] : Array (Array Nat))[k]! = unpack 1782 12 (GP k) := by
  intro k hk
  interval_cases k
  · exact b0_eq
  · exact b1_eq

theorem tArr_eq11 {i : Nat} (hi : i < 4) : tArr i = unpack 1782 11 (SuzTP i) :=
  (OddCore.rep_facts hi).1

theorem tArr_eq {i : Nat} (hi : i < 4) : tArr i = unpack 1782 12 (GP (3 + i)) := by
  rw [tArr_eq11 hi]
  interval_cases i
  · rw [bindK_sound bindT0]
  · rw [bindK_sound bindT1]
  · rw [bindK_sound bindT2]
  · rw [bindK_sound bindT3]

theorem tlt {i : Nat} (hi : i < 4) : ∀ v < 1782, tg (GP (3 + i)) v < 1782 := by
  intro v hv
  interval_cases i
  · exact Nat.le_of_ble_eq_true (CFSG.KC.Pack.allN_spec tlt0 v hv)
  · exact Nat.le_of_ble_eq_true (CFSG.KC.Pack.allN_spec tlt1 v hv)
  · exact Nat.le_of_ble_eq_true (CFSG.KC.Pack.allN_spec tlt2 v hv)
  · exact Nat.le_of_ble_eq_true (CFSG.KC.Pack.allN_spec tlt3 v hv)

theorem tArr_get {i v : Nat} (hi : i < 4) (hv : v < 1782) : (tArr i)[v]! = tg (GP (3 + i)) v := by
  rw [tArr_eq hi, unpack12_get hv]
  rfl

theorem root_eq : invNeighbors = decodeRow 416 (R 0) := by
  apply List.ext_getElem
  · rw [row_length]
    rfl
  · intro i h1 h2
    have hi : i < 416 := by rwa [row_length] at h2
    have hr := Nat.eq_of_beq_eq_true (CFSG.KC.Pack.allN_spec root i hi)
    rw [OddCore.nget_eq] at hr
    rw [← List.getD_eq_getElem _ 0 h1, ← hr]
    simp only [decodeRow_eq, List.getElem_map, List.getElem_range]

theorem graph : adjSearch 1782 #[b0Arr, b1Arr] invNeighbors = rowsArr 1782 416 R ∧
    adjOK 1782 #[b0Arr, b1Arr] (rowsArr 1782 416 R) invNeighbors = true :=
  graph_sound (ng := 2) (G := GP) (T := T) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    rfl gens_eq rows (fun k hk => imgs k (by omega)) (CFSG.KC.Pack.allN_spec tree)
    (CFSG.KC.Pack.allN_spec sym0) root_eq

theorem nbr_eq : invNbr = rowsArr 1782 416 R := by
  rw [invNbr]
  exact graph.1

theorem adj : adjOK 1782 #[b0Arr, b1Arr] invNbr invNeighbors = true := by
  rw [nbr_eq]
  exact graph.2

theorem symm :
    ∀ x < 1782, ∀ y ∈ invNbr[x]!, x ∈ invNbr[y]! := by
  intro x hx y hy
  have hA := adjFacts_of_adjOK adj
  have hy' : y < 1782 := (hA.point ⟨x, hx⟩).lt y hy
  obtain ⟨m, hm, hmx⟩ := suzM_transitive ⟨x, hx⟩
  have hinv : NbrInv invNbr m⁻¹ :=
    hA.inv_of_mem_closure (fun _ hk => rep_bPair hk) (suzM_eq_closure_gens ▸ suzM.inv_mem hm)
  have hx0 : m⁻¹ ⟨x, hx⟩ = 0 := by rw [← hmx, perm_inv_apply']
  have h1 := (hinv ⟨x, hx⟩ ⟨y, hy'⟩).1 hy
  rw [hx0, Fin.val_zero] at h1
  have h2 := hA.root_symm _ h1
  have h3 := (hinv ⟨y, hy'⟩ ⟨x, hx⟩).2
  rw [hx0, Fin.val_zero] at h3
  exact h3 h2

theorem symm' :
    ∀ x < 1782, ∀ y < 1782, y ∈ decodeRow 416 (R x) → x ∈ decodeRow 416 (R y) := by
  intro x hx y hy h
  have := symm x hx y (by rw [nbr_eq, rowsArr_get hx]; exact h)
  rwa [nbr_eq, rowsArr_get hy] at this

@[expose] noncomputable def col (k : Nat) : Array Nat := colOf 1782 (X k) (Q k)

theorem col_size (k : Nat) : (col k).size = 1782 := colOf_size _ _ _

theorem rnd_facts {T k : Nat} (h : rnd T k = true) :
    tabOK 1782 (K (k - 1)) (X (k - 1)) (Q (k - 1)) = true ∧ ordOK 1782 (Q (k - 1)) (O (k - 1)) = true ∧
      roundOK 1782 (X (k - 1)) (Q (k - 1)) (X k) (Q k) T (O (k - 1)) W = true := by
  unfold rnd at h
  obtain ⟨h1, h2⟩ := CFSG.KC.Pack.band_iff.1 h
  obtain ⟨h2, h3⟩ := CFSG.KC.Pack.band_iff.1 h2
  exact ⟨h1, h2, h3⟩

theorem arr_ext {a b : Array Nat} (ha : a.size = 1782) (hb : b.size = 1782)
    (h : ∀ v < 1782, a[v]! = b[v]!) : a = b := by
  refine Array.ext (by rw [ha, hb]) fun v h1 h2 => ?_
  rw [← getElem!_pos _ v h1, ← getElem!_pos _ v h2]
  exact h v (by rwa [ha] at h1)

theorem refineStepT_size (t c : Array Nat) : (refineStepT t c).size = 1782 := by
  rw [refineStepT, Array.size_ofFn]

theorem refineStepT_get (t a : Array Nat) {v : Nat} (hv : v < 1782) :
    (refineStepT t a)[v]! = sigCode (sigCode a[v]! [a[t[v]!]!]) (nbrColours invNbr a v) := by
  rw [refineStepT, getElem!_ofFn_nat _ hv]

theorem round_eq {i k : Nat}
    (hi : i < 4) (h : rnd (GP (3 + i)) k = true) : refineStepT (tArr i) (col (k - 1)) = col k := by
  obtain ⟨htab, hord, hr⟩ := rnd_facts h
  have hs := round_sound (by norm_num) rows symm' masks htab hord (tlt hi) hr
  refine arr_ext (refineStepT_size _ _) (col_size _) fun v hv => ?_
  rw [refineStepT_get _ _ hv, nbr_eq, tArr_eq hi]
  exact hs v hv

theorem ind_eq {k p j : Nat} (h : ind k p j = true) : indivPoint (col (k - 1)) p j = col k := by
  rw [indivPoint, col, col, indiv_sound (CFSG.KC.Pack.allN_spec h)]
  rfl

theorem iter_eq {i a : Nat}
    (hi : i < 4) : ∀ m, (∀ j < m, rnd (GP (3 + i)) (Nat.add a (Nat.add j (nat_lit 1))) = true) →
      refineIterT (tArr i) (col a) m = col (a + m)
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

theorem initColour_size (r : String) (t : Array Nat) : (initColour r t).size = 1782 := by
  rw [initColour, Array.size_ofFn]

theorem initColour_get (r : String) (t : Array Nat) {v : Nat} (hv : v < 1782) :
    (initColour r t)[v]! = if r == "fixed" then (if t[v]! == v then 1 else 0)
      else (if (invNbr[v]!).contains t[v]! then 1 else 0) := by
  rw [initColour, getElem!_ofFn_nat _ hv]

theorem nif_eq (c : Bool) (a b : Nat) : nIf(c, a, b) = if c = true then a else b := by
  cases c <;> rfl

theorem initOK_true {X Q T v : Nat} {M : Nat → Nat} (h : initOK true X Q M T v = true) :
    xg X (rk Q v) = if tg T v = v then 1 else 0 := by
  have e := Nat.eq_of_beq_eq_true h
  rw [e]
  change nIf(Nat.beq (tg T v) v, nat_lit 1, nat_lit 0) = _
  rw [nif_eq]
  by_cases hv : tg T v = v
  · rw [if_pos (by rw [hv]; exact Nat.beq_refl v), if_pos hv]
  · rw [if_neg fun h => hv (Nat.eq_of_beq_eq_true h), if_neg hv]

theorem initOK_false {X Q T v : Nat} {M : Nat → Nat} (h : initOK false X Q M T v = true) :
    xg X (rk Q v) = if (M v).testBit (tg T v) = true then 1 else 0 := by
  have e := Nat.eq_of_beq_eq_true h
  rw [e]
  change nIf(Nat.beq (Nat.land (Nat.shiftRight (M v) (tg T v)) (nat_lit 1)) (nat_lit 1),
    nat_lit 1, nat_lit 0) = _
  rw [nif_eq, beq_bit]

theorem init_fixed {i k : Nat} (hi : i < 4) (hr : invColorRules.getD i "" = "fixed")
    (h : allN 1782 (initOK true (X k) (Q k) M (GP (3 + i))) = true) :
    initColour (invColorRules.getD i "") (tArr i) = col k := by
  refine arr_ext (initColour_size _ _) (col_size _) fun v hv => ?_
  rw [initColour_get _ _ hv, col, colOf_get hv, initOK_true (CFSG.KC.Pack.allN_spec h v hv),
    if_pos (beq_iff_eq.2 hr), tArr_get hi hv]
  by_cases e : tg (GP (3 + i)) v = v
  · rw [if_pos (beq_iff_eq.2 e), if_pos e]
  · rw [if_neg fun h => e (beq_iff_eq.1 h), if_neg e]

theorem init_adj {i k : Nat} (hi : i < 4) (hr : invColorRules.getD i "" ≠ "fixed")
    (h : allN 1782 (initOK false (X k) (Q k) M (GP (3 + i))) = true) :
    initColour (invColorRules.getD i "") (tArr i) = col k := by
  refine arr_ext (initColour_size _ _) (col_size _) fun v hv => ?_
  rw [initColour_get _ _ hv, col, colOf_get hv, initOK_false (CFSG.KC.Pack.allN_spec h v hv),
    if_neg fun h => hr (beq_iff_eq.1 h), tArr_get hi hv, nbr_eq, rowsArr_get hv,
    row_mask (rows v hv)]
  by_cases hm : tg (GP (3 + i)) v ∈ decodeRow 416 (R v)
  · rw [if_pos (List.contains_iff_mem.2 hm), if_pos (decide_eq_true hm)]
  · rw [if_neg fun h => hm (List.contains_iff_mem.1 h), if_neg (by simpa using hm)]

theorem init_eq {i : Nat}
    (hi : i < 4) : initColour (invColorRules.getD i "") (tArr i) = col (caseStart i) := by
  interval_cases i
  · exact init_fixed (by norm_num) rfl init0
  · exact init_fixed (by norm_num) rfl init1
  · exact init_adj (by norm_num) (by decide) init2
  · exact init_fixed (by norm_num) rfl init3

theorem nSteps_le : ∀ i < 4, nSteps i ≤ 9 := by decide

theorem blocks {i s : Nat} (hi : i < 4) (hs : s ≤ nSteps i) : blkB i s = true := by
  have hs10 : s < 10 := by
    have := nSteps_le i hi
    omega
  have h : caseB i s = true := by
    interval_cases i
    · exact Rnd0.all s hs10
    · exact Rnd1.all s hs10
    · exact Rnd2.all s hs10
    · exact Rnd3.all s hs10
  have hb : Nat.ble s (nSteps i) = true := by
    rw [Nat.ble_eq]
    exact hs
  unfold caseB at h
  rw [hb] at h
  exact h

theorem stepPoints_eq : ∀ i < 4, ∀ s < nSteps i, (stepPoints i).getD s 0 = point i s := by
  decide

theorem stepPoints_get {i s : Nat} (hi : i < 4) (hs : s < nSteps i) :
    (stepPoints i).getD s 0 = point i s :=
  stepPoints_eq i hi s hs

theorem point_lt : ∀ i < 4, ∀ s < nSteps i, point i s < 1782 := by
  decide

theorem stage_eq {i : Nat}
    (hi : i < 4) : ∀ s ≤ nSteps i, stageColour i s = col (stageIdx i s)
  | 0, _ => by
    have h := blocks hi (Nat.zero_le _)
    rw [blkB, CFSG.KC.Pack.strictB_eq] at h
    rw [stageColour, init_eq hi]
    exact iter_eq hi _ (rnds_spec h)
  | s + 1, hs => by
    have h := blocks hi hs
    rw [blkB, CFSG.KC.Pack.strictB_eq] at h
    obtain ⟨hind, hr⟩ := CFSG.KC.Pack.band_iff.1 h
    rw [stageColour, stage_eq hi s (by omega), stepPoints_get hi (by omega)]
    have e := ind_eq hind
    have e1 : Nat.add (stageIdx i s) (nat_lit 1) - 1 = stageIdx i s := by
      change stageIdx i s + 1 - 1 = _
      omega
    rw [e1] at e
    rw [e]
    exact iter_eq hi _ (rnds_spec hr)

theorem invRep_eq {i : Nat} (hi : i < 4) : tArr i = invRepArr i := by
  rw [tArr_eq11 hi, invRepArr]
  interval_cases i
  · rw [SuzInv.run_eq0 (k := 0) (by norm_num), Nat.eq_of_beq_eq_true tp0]
  · rw [SuzInv.run_eq1 (k := 0) (by norm_num), Nat.eq_of_beq_eq_true tp1]
  · rw [SuzInv.run_eq2 (k := 0) (by norm_num), Nat.eq_of_beq_eq_true tp2]
  · rw [SuzInv.run_eq3 (k := 0) (by norm_num), Nat.eq_of_beq_eq_true tp3]

theorem classCount_col {k p : Nat} (htab : tabOK 1782 (K k) (X k) (Q k) = true) (hp : p < 1782) :
    classCount (col k) p = cellCntK 1782 (Q k) (rk (Q k) p) := by
  rw [classCount, cellCntK_eq, ← CFSG.Sporadic.FischerOddCore.card_fin_subtype_eq_countP,
    ← Nat.card_eq_finsetCard]
  refine Nat.card_congr (Equiv.subtypeEquivRight fun w => ?_)
  rw [beq_iff_eq, ← colOf_eq_iff (X := X k) htab w.2 hp]
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  rfl

theorem cells {i : Nat} (hi : i < 4)
    {s : Nat} (hs : s < nSteps i) :
    classCount (stageColour i s) ((stepPoints i).getD s 0) ≤ bound i s := by
  have h := CFSG.KC.Pack.allN_spec (Cell.all i hi) s hs
  rw [CFSG.KC.Pack.strictB_eq] at h
  obtain ⟨htab, hle⟩ := CFSG.KC.Pack.band_iff.1 h
  rw [stage_eq hi s hs.le, stepPoints_get hi hs, classCount_col htab (point_lt i hi s hs)]
  exact Nat.le_of_ble_eq_true hle

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

theorem last_eq {i : Nat} (hi : i < 4) :
    stageIdx i (nSteps i) = [37, 71, 100, 136].getD i 0 := by
  interval_cases i <;> rfl

theorem final_nodup {i : Nat}
    (hi : i < 4) : ((stageColour i (nSteps i)).toList.take 1782).Nodup ∧
      (stageColour i (nSteps i)).size = 1782 := by
  rw [stage_eq hi _ le_rfl, last_eq hi]
  refine ⟨?_, col_size _⟩
  interval_cases i
  · exact nodup_of_injOK inj0
  · exact nodup_of_injOK inj1
  · exact nodup_of_injOK inj2
  · exact nodup_of_injOK inj3

theorem facts2301 :
    adjOK 1782 #[b0Arr, b1Arr] invNbr invNeighbors = true ∧
    (∀ x < 1782, invNbr[vArr[x]!]! = imgSorted vArr invNbr[x]!) ∧
    (∀ x < 1782, (invNbr[x]!).length = 416) ∧
    (∀ i < 4, tArr i = invRepArr i) ∧
    (∀ i < 4, ∀ s < (invSteps.getD i []).length,
      classCount (stageColour i s) ((stepPoints i).getD s 0) ≤
        ((invSteps.getD i []).getD s []).getD 1 0) ∧
    (∀ i < 4, ((stageColour i (invSteps.getD i []).length).toList.take 1782).Nodup ∧
      (stageColour i (invSteps.getD i []).length).size = 1782) ∧
    (∀ i < 4, ∀ x ∈ stepPoints i, x < 1782) := by
  refine ⟨adj, fun x hx => ?_, fun x hx => ?_, fun i hi => invRep_eq hi,
    fun i hi s hs => cells hi hs, fun i hi => final_nodup hi, fun i hi => ?_⟩
  · have h := allLt_iff.1 (img_sound (by norm_num) rows v_eq fun x hx => imgs 2 (by norm_num) x hx)
      x hx
    rw [← nbr_eq] at h
    exact beq_iff_eq.1 h
  · rw [nbr_eq, rowsArr_get hx, row_length]
  · interval_cases i <;> decide

end CertificateChecks.KernelSpor.S2301

end
