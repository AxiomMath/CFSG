module

public import Certificates.Kernel.Sporadic.OddCore.CentGlue

public section

namespace CFSG.KS.MulH

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KC.BfsPin
open CFSG.Sporadic.Th.Native CFSG.Sporadic.Schreier.Native

theorem apTab_unpack {n w X i : Nat} (hX : canonK n w (mask w) (n * w) X = true) (hi : i < n) :
    ap (tabT (unpack n w X)) i = pg w (mask w) X i := by
  rw [ap_tabT _ (unpack_lt hX), CFSG.KC.Misc.PairCount.unpack_get hi]

theorem apW_unpack {n w X : Nat} (hX : canonK n w (mask w) (n * w) X = true) :
    ∀ L : List Nat, (∀ Y ∈ L, canonK n w (mask w) (n * w) Y = true) →
      (∀ i < n, apW ((L.map fun Y => tabT (unpack n w Y)) ++ [tabT (unpack n w X)]) i =
        pg w (mask w) (L.foldr (pcomp n w (mask w)) X) i) ∧
      canonK n w (mask w) (n * w) (L.foldr (pcomp n w (mask w)) X) = true
  | [], _ => ⟨fun i hi => apTab_unpack hX hi, hX⟩
  | Y :: L, h => by
    obtain ⟨ih, hc⟩ := apW_unpack hX L fun Z hZ => h Z (List.mem_cons_of_mem _ hZ)
    have hY := h Y List.mem_cons_self
    refine ⟨fun i hi => ?_, canonK_pcomp hY hc⟩
    have e : apW ((List.map (fun Y => tabT (unpack n w Y)) (Y :: L)) ++
        [tabT (unpack n w X)]) i = ap (tabT (unpack n w Y))
          (apW ((L.map fun Y => tabT (unpack n w Y)) ++ [tabT (unpack n w X)]) i) := rfl
    rw [e, ih i hi, List.foldr_cons, pg_pcomp' hY hc hi, apTab_unpack hY (pg_lt' hc hi)]

theorem apPowW_of_apW {n w X : Nat} {ws : List Table} (hX : canonK n w (mask w) (n * w) X = true)
    (hw : ∀ i < n, apW ws i = pg w (mask w) X i) :
    ∀ e, ∀ i < n, apPowW ws e i = apPowW [tabT (unpack n w X)] e i ∧
      apPowW [tabT (unpack n w X)] e i < n
  | 0, i, hi => ⟨rfl, hi⟩
  | e + 1, i, hi => by
    obtain ⟨h1, h2⟩ := apPowW_of_apW hX hw e i hi
    have e1 : apPowW [tabT (unpack n w X)] (e + 1) i =
        ap (tabT (unpack n w X)) (apPowW [tabT (unpack n w X)] e i) := rfl
    rw [apPowW, h1, hw _ h2, e1, apTab_unpack hX h2]
    exact ⟨rfl, pg_lt' hX h2⟩

theorem ordW_of_apW {n w X : Nat} {ws : List Table} (hX : canonK n w (mask w) (n * w) X = true)
    (hw : ∀ i < n, apW ws i = pg w (mask w) X i) (m : Nat) :
    ordW n ws m = ordTest n m (tabT (unpack n w X)) := by
  have hf : ∀ e, powFixW n ws e = powFixW n [tabT (unpack n w X)] e := by
    intro e
    unfold powFixW
    rw [Bool.eq_iff_iff, CFSG.KS.TW.allIn_iff, CFSG.KS.TW.allIn_iff]
    refine forall_congr' fun i => imp_congr_right fun hi => ?_
    rw [(apPowW_of_apW hX hw e i hi).1]
  unfold ordTest ordW
  simp only [hf]

end CFSG.KS.MulH

end
