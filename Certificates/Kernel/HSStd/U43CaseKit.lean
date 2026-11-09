module

public import Certificates.Data.Kernel.U43Case
public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.U43ConfigCheck
public import CFSG.Certificates.Kernel.Spor.MulHSound
public import Certificates.Kernel.Sporadic.OddCore.MulHGlue
import CFSG.Certificates.Kernel.BfsPinAlg
import CFSG.Certificates.Kernel.Spor.PackWord
public import CFSG.Sporadic.SmallOddCore.ClassSimple

public section

namespace CFSG.KC.U43Case

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KS.MulH CFSG.KC.BfsPin
open CFSG.Sporadic.Th.Native CFSG.Sporadic.Schreier.Native CFSG.Sporadic.SmallOddCore
open CFSG.Sporadic.SmallOddCore.Native CFSG.EvenSporadicStandard.HSStd.U43

variable {n w : Nat}

@[expose] noncomputable def tb (n w x : Nat) : Table := tabT (unpack n w x)

abbrev Cn (n w x : Nat) : Prop := canonK n w (mask w) (n * w) x = true

theorem cn_pp {x y : Nat} (hx : Cn n w x) (hy : Cn n w y) : Cn n w (pp n w x y) := canonK_pcomp hx hy

theorem compT_tb {x y : Nat} (hx : Cn n w x) (hy : Cn n w y) :
    compT n (tb n w x) (tb n w y) = tb n w (pp n w x y) := compT_unpack hx hy

theorem idT_tb (hs : szOK n w = true) : idT n = tb n w (pidn n w) := by
  unfold tb
  rw [idT_tabT, idA_eq hs]

theorem cn_id (hs : szOK n w = true) : Cn n w (pidn n w) := (PP.id hs).1

theorem tblEq_tb {x y : Nat} (hx : Cn n w x) (hy : Cn n w y) :
    tblEq n (tb n w x) (tb n w y) = Nat.beq x y := tblEq_unpack hx hy

theorem commTT_tb {x y : Nat} (hx : Cn n w x) (hy : Cn n w y) :
    commTT n (tb n w x) (tb n w y) = commP n w x y := commTT_unpack hx hy

theorem powT_tb (hs : szOK n w = true) {x : Nat} (hx : Cn n w x) : ∀ e,
    powT n e (tb n w x) = tb n w (ppw n w x e) ∧ Cn n w (ppw n w x e)
  | 0 => ⟨idT_tb hs, cn_id hs⟩
  | e + 1 => by
    obtain ⟨h1, h2⟩ := powT_tb hs hx e
    change compT n (tb n w x) (powT n e (tb n w x)) = tb n w (pp n w x (ppw n w x e)) ∧
      Cn n w (pp n w x (ppw n w x e))
    rw [h1, compT_tb hx h2]
    exact ⟨rfl, cn_pp hx h2⟩

theorem ap_compT' (P Q : Table) {i : Nat} (hi : i < n) : ap (compT n P Q) i = ap P (ap Q i) := by
  unfold compT ap
  rw [getElem!_pos _ i (by simpa using hi), Array.getElem_ofFn]

theorem ap_idT' (hn : n < 2 ^ 32) {i : Nat} (hi : i < n) : ap (idT n) i = i := by
  unfold idT ap
  rw [getElem!_pos _ i (by simpa using hi), Array.getElem_ofFn, UInt32.toNat_ofNat',
    Nat.mod_eq_of_lt (by omega)]

theorem apPowW_eq (T : Table) {i : Nat} (hn : n < 2 ^ 32) (hi : i < n) :
    ∀ e, apPowW [T] e i = ap (powT n e T) i
  | 0 => by
    rw [powT, apPowW, ap_idT' hn hi]
  | e + 1 => by
    rw [apPowW, apPowW_eq T hn hi e, powT, ap_compT' _ _ hi]
    unfold apW
    simp only [List.foldr_cons, List.foldr_nil]

theorem powFixW_eq (T : Table) (hn : n < 2 ^ 32) (e : Nat) :
    powFixW n [T] e = tblEq n (powT n e T) (idT n) := by
  rw [powFixW, tblEq, Bool.eq_iff_iff, CFSG.KS.TW.allIn_iff, CFSG.KS.TW.allIn_iff]
  refine forall_congr' fun i => imp_congr_right fun hi => ?_
  rw [apPowW_eq T hn hi e, ap_idT' hn hi]

theorem n32 {x : Nat} (hx : Cn n w x) : n < 2 ^ 32 := by
  have := lt_of_canonK hx
  omega

theorem ordTest3_tb (hs : szOK n w = true) {x : Nat} (hx : Cn n w x) :
    ordTest n 3 (tb n w x) = ord3P n w x := by
  have h : ∀ e, powFixW n [tb n w x] e = Nat.beq (ppw n w x e) (pidn n w) := fun e => by
    rw [powFixW_eq _ (n32 hx), (powT_tb hs hx e).1, idT_tb hs,
      tblEq_tb (powT_tb hs hx e).2 (cn_id hs)]
  have hd : divParts 3 = [1] := by decide
  rw [ordTest, ordW, hd]
  simp only [List.all_cons, List.all_nil, Bool.and_true]
  rw [h, h, ord3P]
  cases Nat.beq (ppw n w x 3) (pidn n w) <;> cases Nat.beq (ppw n w x 1) (pidn n w) <;> rfl

theorem invoOK_tb (hs : szOK n w = true) {x : Nat} (hx : Cn n w x) :
    CFSG.Sporadic.Th.Native.invoOK n (tb n w x) = Nat.beq (pp n w x x) (pidn n w) := by
  have e : CFSG.Sporadic.Th.Native.invoOK n (tb n w x) =
      tblEq n (compT n (tb n w x) (tb n w x)) (idT n) := by
    unfold CFSG.Sporadic.Th.Native.invoOK tblEq
    rw [Bool.eq_iff_iff, CFSG.KS.TW.allIn_iff, CFSG.KS.TW.allIn_iff]
    refine forall_congr' fun i => imp_congr_right fun hi => ?_
    rw [ap_compT' _ _ hi, ap_idT' (n32 hx) hi]
  rw [e, compT_tb hx hx, idT_tb hs, tblEq_tb (cn_pp hx hx) (cn_id hs)]

theorem involOK_tb (hs : szOK n w = true) {x : Nat} (hx : Cn n w x) :
    involOK n (tb n w x) = (Nat.beq (pp n w x x) (pidn n w) && !Nat.beq x (pidn n w)) := by
  unfold involOK
  rw [invoOK_tb hs hx, idT_tb hs, tblEq_tb hx (cn_id hs)]

theorem toList_ofFn' {α : Type} {N : Nat} (f : Nat → α) :
    (Array.ofFn (n := N) fun i => f i.val).toList = (List.range N).map f := by
  rw [Array.toList_ofFn]
  apply List.ext_getElem (by simp)
  intro i h1 h2
  simp

set_option maxRecDepth 400000

theorem cn_cp {g x : Nat} (hg : Cn 820 10 g) (hx : Cn 820 10 x) : Cn 820 10 (cpP 820 10 g x) :=
  cn_pp (cn_pp hg hx) hg

section Conf

variable (hs : szOK 820 10 = true)
include hs

theorem conjT_tb {g x : Nat} (hg : Cn 820 10 g) (hx : Cn 820 10 x) :
    conjT 820 (tb 820 10 g) (tb 820 10 g) (tb 820 10 x) = tb 820 10 (cpP 820 10 g x) := by
  unfold conjT cpP
  rw [compT_tb hg hx, compT_tb (cn_pp hg hx) hg]

theorem cpOf_tb {t c : Nat} (ht : Cn 820 10 t) (hc : Cn 820 10 c) :
    cpOf (tb 820 10 t) (tb 820 10 c) = tb 820 10 (cpP 820 10 t c) := by
  unfold cpOf
  exact conjT_tb hs ht hc

theorem relFree_tb {y c c' : Nat} (hy : Cn 820 10 y) (hc : Cn 820 10 c) (hc' : Cn 820 10 c') :
    relFree (tb 820 10 y) (tb 820 10 c) (tb 820 10 c') = relFreeP 820 10 y c c' := by
  have hp : ∀ x, Cn 820 10 x → ∀ a, powT 820 a (tb 820 10 x) = tb 820 10 (ppw 820 10 x a) :=
    fun x hx a => (powT_tb hs hx a).1
  have hq : ∀ x, Cn 820 10 x → ∀ a, Cn 820 10 (ppw 820 10 x a) := fun x hx a => (powT_tb hs hx a).2
  unfold relFree relFreeP
  simp only [hp y hy, hp c hc, hp c' hc', compT_tb (hq y hy _) (hq c hc _),
    compT_tb (cn_pp (hq y hy _) (hq c hc _)) (hq c' hc' _), idT_tb hs,
    tblEq_tb (cn_pp (cn_pp (hq y hy _) (hq c hc _)) (hq c' hc' _)) (cn_id hs)]

theorem candOK_tb {t y c : Nat} (ht : Cn 820 10 t) (hy : Cn 820 10 y) (hc : Cn 820 10 c) :
    candOK (tb 820 10 t) (tb 820 10 y) (tb 820 10 c) = candP 820 10 t y c := by
  unfold candOK candP
  rw [cpOf_tb hs ht hc, ordTest3_tb hs hc, commTT_tb hc (cn_cp ht hc),
    commTT_tb hy (cn_cp ht hc), relFree_tb hs hy hc (cn_cp ht hc)]

theorem kOK_tb {t c k : Nat} (ht : Cn 820 10 t) (hc : Cn 820 10 c) (hk : Cn 820 10 k) :
    kOK (tb 820 10 t) (tb 820 10 c) (tb 820 10 k) = kP 820 10 t c k := by
  unfold kOK kP
  rw [cpOf_tb hs ht hc, cpOf_tb hs ht hk, involOK_tb hs hk, commTT_tb hk (cn_cp ht hc),
    commTT_tb hk (cn_cp ht hk), conjT_tb hs hk hc, compT_tb (cn_cp hk hc) hc, idT_tb hs,
    tblEq_tb (cn_pp (cn_cp hk hc) hc) (cn_id hs)]
  rfl

omit hs in
theorem clsRecArr_tb {k : Nat} {G GI T : Nat → Nat} {gG gGinv : Array Table} {x : Table}
    {par : Array (ℕ × ℕ)} (hG : TabsOK 820 10 k G gG) (hGI : TabsOK 820 10 k GI gGinv)
    (hx : x = tb 820 10 (T 0)) (hT : ∀ i < par.size + 1, Cn 820 10 (T i))
    (hpar : ∀ i < par.size, par[i]!.1 ≤ i ∧ par[i]!.2 < k ∧
      T (i + 1) = pp 820 10 (pp 820 10 (G par[i]!.2) (T par[i]!.1)) (GI par[i]!.2)) :
    clsRecArr gG gGinv x par = Array.ofFn (n := par.size + 1) fun i => tb 820 10 (T i.val) := by
  have key : (clsRecArr gG gGinv x par).size = par.size + 1 ∧
      ∀ j < par.size + 1, (clsRecArr gG gGinv x par)[j]! = tb 820 10 (T j) := by
    unfold clsRecArr
    refine Array.foldl_induction (motive := fun (i : ℕ) (a : Array Table) => a.size = i + 1 ∧
      ∀ j < i + 1, a[j]! = tb 820 10 (T j)) ?_ ?_
    · refine ⟨rfl, fun j hj => ?_⟩
      have hj0 : j = 0 := by omega
      subst hj0
      exact hx
    · rintro ⟨i, hi⟩ b ⟨hsz, hb⟩
      change b.size = i + 1 at hsz
      change ∀ j < i + 1, b[j]! = tb 820 10 (T j) at hb
      have hp := hpar i hi
      rw [getElem!_pos par i hi] at hp
      obtain ⟨h1, h2, h3⟩ := hp
      simp only [Fin.getElem_fin]
      refine ⟨by rw [Array.size_push, hsz], fun j hj => ?_⟩
      by_cases hji : j < b.size
      · rw [getElem!_pos _ j (by rw [Array.size_push]; omega), Array.getElem_push_lt hji,
          ← getElem!_pos b j hji]
        exact hb j (by omega)
      · have hj' : j = b.size := by omega
        subst hj'
        rw [getElem!_pos _ _ (by rw [Array.size_push]; omega), Array.getElem_push_eq, hsz,
          hb _ (by omega), (hG.2 _ h2).1, (hGI.2 _ h2).1, h3]
        have cg := (hG.2 _ h2).2
        have cgi := (hGI.2 _ h2).2
        have cx := hT _ (by omega : par[i].1 < par.size + 1)
        change compT 820 (compT 820 (tb 820 10 _) (tb 820 10 _)) (tb 820 10 _) = _
        rw [compT_tb cg cx, compT_tb (cn_pp cg cx) cgi]
  refine Array.ext (by rw [key.1, Array.size_ofFn]) fun j h1 h2 => ?_
  rw [← getElem!_pos _ j h1, key.2 j (by rw [key.1] at h1; exact h1), Array.getElem_ofFn]

variable {N : Nat} {Y : Nat → Nat} (hY : ∀ i < N, Cn 820 10 (Y i))
include hY

theorem solList_tb {d : CaseData} {t y : Nat} (ht : Cn 820 10 t) (hy : Cn 820 10 y)
    (hT : d.Tt = tb 820 10 t) (hy0 : d.y0 = tb 820 10 y)
    (hE : yEnum d = Array.ofFn (n := N) fun i => tb 820 10 (Y i.val)) :
    solList d = (solsP 820 10 t y N Y).map fun p => (tb 820 10 (Y p.1), tb 820 10 (Y p.2)) := by
  unfold solList solsP
  rw [hE, toList_ofFn' (fun i => tb 820 10 (Y i)), hT, hy0, List.filter_map,
    List.filter_congr (q := fun i => candP 820 10 t y (Y i)) fun i hi => by
      simp only [Function.comp_apply]
      exact candOK_tb hs ht hy (hY i (List.mem_range.1 hi)),
    List.flatMap_map, List.map_flatMap]
  refine List.flatMap_congr fun i hi => ?_
  have hi' := List.mem_range.1 (List.mem_filter.1 hi).1
  rw [List.filter_map, List.filter_congr (q := fun j => kP 820 10 t (Y i) (Y j)) fun j hj => by
      simp only [Function.comp_apply]
      exact kOK_tb hs ht (hY i hi') (hY j (List.mem_range.1 hj)),
    List.map_map, List.map_map]
  rfl

theorem cent5Of_tb {d : CaseData} {t : Nat} (ht : Cn 820 10 t) (hT : d.Tt = tb 820 10 t)
    (hE : yEnum d = Array.ofFn (n := N) fun i => tb 820 10 (Y i.val)) {c k : Nat}
    (hc : Cn 820 10 c) (hk : Cn 820 10 k) :
    cent5Of d (tb 820 10 c, tb 820 10 k) = cent5P 820 10 t N Y c k := by
  unfold cent5Of cent5P
  rw [hE, toList_ofFn' (fun i => tb 820 10 (Y i)), hT, List.filter_map, List.length_map]
  congr 1
  refine List.filter_congr fun i hi => ?_
  have hi' := hY i (List.mem_range.1 hi)
  simp only [Function.comp_apply]
  rw [cpOf_tb hs ht hc, cpOf_tb hs ht hk, commTT_tb hi' hc, commTT_tb hi' (cn_cp ht hc),
    commTT_tb hi' hk, commTT_tb hi' (cn_cp ht hk)]

end Conf

end CFSG.KC.U43Case

end
