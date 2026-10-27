module

public import Certificates.Data.Kernel.GH74Ev
public import Certificates.Kernel.Sporadic.OddCore.CentGlue
import CFSG.Certificates.Kernel.Spor.RawOrbEval

public section

namespace CFSG.KS.GH74

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KS.MulH
open CFSG.Sporadic.Th.Native CFSG.Sporadic.Schreier.Native

variable {n w : Nat}

theorem beq_iff_pg {p q : Nat} (hp : canonK n w (mask w) (n * w) p = true)
    (hq : canonK n w (mask w) (n * w) q = true) :
    Nat.beq p q = true ↔ ∀ i < n, pg w (mask w) p i = pg w (mask w) q i := by
  rw [← tblEq_unpack hp hq]
  unfold tblEq
  rw [CFSG.KS.TW.allIn_iff]
  refine forall_congr' fun i => imp_congr_right fun hi => ?_
  rw [ap_tabT _ (unpack_lt hp), ap_tabT _ (unpack_lt hq), CFSG.KC.Misc.PairCount.unpack_get hi,
    CFSG.KC.Misc.PairCount.unpack_get hi, beq_iff_eq]

theorem nat_beq_iff (a b : Nat) : Nat.beq a b = true ↔ a = b :=
  ⟨Nat.eq_of_beq_eq_true, fun h => h ▸ Nat.beq_refl a⟩

theorem pcommK_eq {p q : Nat} (hp : canonK n w (mask w) (n * w) p = true)
    (hq : canonK n w (mask w) (n * w) q = true) :
    pcommK n w p q = Nat.beq (pcomp n w (mask w) p q) (pcomp n w (mask w) q p) := by
  apply Bool.eq_iff_iff.2
  rw [beq_iff_pg (CFSG.KC.BfsPin.canonK_pcomp hp hq) (CFSG.KC.BfsPin.canonK_pcomp hq hp)]
  unfold pcommK
  rw [CFSG.KS.Raw.Orb.allN_iff]
  refine forall_congr' fun i => imp_congr_right fun hi => ?_
  rw [nat_beq_iff, pg_pcomp' hp hq hi, pg_pcomp' hq hp hi]

theorem pcomm2K_eq {a b q : Nat} (ha : canonK n w (mask w) (n * w) a = true)
    (hb : canonK n w (mask w) (n * w) b = true) (hq : canonK n w (mask w) (n * w) q = true) :
    pcomm2K n w a b q = Nat.beq (pcomp n w (mask w) (pcomp n w (mask w) a b) q)
      (pcomp n w (mask w) q (pcomp n w (mask w) a b)) := by
  have hab := CFSG.KC.BfsPin.canonK_pcomp ha hb
  apply Bool.eq_iff_iff.2
  rw [beq_iff_pg (CFSG.KC.BfsPin.canonK_pcomp hab hq) (CFSG.KC.BfsPin.canonK_pcomp hq hab)]
  unfold pcomm2K
  rw [CFSG.KS.Raw.Orb.allN_iff]
  refine forall_congr' fun i => imp_congr_right fun hi => ?_
  rw [nat_beq_iff, pg_pcomp' hab hq hi, pg_pcomp' hq hab hi, pg_pcomp' ha hb hi,
    pg_pcomp' ha hb (pg_lt' hq hi)]

theorem apPowW_eq {z : Nat} (hz : canonK n w (mask w) (n * w) z = true) :
    ∀ e, ∀ i < n, apPowW [tabT (unpack n w z)] e i = ppt w z e i ∧ ppt w z e i < n
  | 0, i, hi => ⟨rfl, hi⟩
  | e + 1, i, hi => by
    obtain ⟨h1, h2⟩ := apPowW_eq hz e i hi
    have e1 : apPowW [tabT (unpack n w z)] (e + 1) i =
        ap (tabT (unpack n w z)) (apPowW [tabT (unpack n w z)] e i) := rfl
    have e2 : ppt w z (e + 1) i = pg w (mask w) z (ppt w z e i) := rfl
    rw [e1, e2, h1, ap_tabT _ (unpack_lt hz), CFSG.KC.Misc.PairCount.unpack_get h2]
    exact ⟨rfl, pg_lt' hz h2⟩

theorem powFixW_eq {z : Nat} (hz : canonK n w (mask w) (n * w) z = true) (e : Nat) :
    powFixW n [tabT (unpack n w z)] e = pfixK n w e z := by
  apply Bool.eq_iff_iff.2
  unfold powFixW pfixK
  rw [CFSG.KS.TW.allIn_iff, CFSG.KS.Raw.Orb.allN_iff]
  refine forall_congr' fun i => imp_congr_right fun hi => ?_
  rw [(apPowW_eq hz e i hi).1, nat_beq_iff, beq_iff_eq]

theorem ord5K_eq {z : Nat} (hz : canonK n w (mask w) (n * w) z = true) :
    ordTest n 5 (tabT (unpack n w z)) = ord5K n w z := by
  unfold ordTest ordW ord5K
  rw [show divParts 5 = [1] from rfl, powFixW_eq hz, List.all_cons, List.all_nil, powFixW_eq hz]
  cases pfixK n w 5 z <;> cases pfixK n w 1 z <;> rfl

theorem strictB_eq (y : Nat) (k : Nat → Bool) : strictB y k = k y := by
  cases y <;> rfl

theorem cent5At_eq (cnt : Nat) (T : Nat → Nat) (t v z : Nat) :
    cent5At n w cnt T t v z = bIf(ord5K n w z, cent5Body n w cnt T v z (pidn n w)
      (pcomp n w (mask w) z (pidn n w))
      (pcomp n w (mask w) z (pcomp n w (mask w) z (pidn n w)))
      (pcomp n w (mask w) z (pcomp n w (mask w) z (pcomp n w (mask w) z (pidn n w))))
      (pcomp n w (mask w) z (pcomp n w (mask w) z (pcomp n w (mask w) z
        (pcomp n w (mask w) z (pidn n w)))))
      (pcomp n w (mask w) t (pidn n w))
      (pcomp n w (mask w) t (pcomp n w (mask w) z (pidn n w)))
      (pcomp n w (mask w) t (pcomp n w (mask w) z (pcomp n w (mask w) z (pidn n w))))
      (pcomp n w (mask w) t (pcomp n w (mask w) z (pcomp n w (mask w) z
        (pcomp n w (mask w) z (pidn n w)))))
      (pcomp n w (mask w) t (pcomp n w (mask w) z (pcomp n w (mask w) z
        (pcomp n w (mask w) z (pcomp n w (mask w) z (pidn n w)))))), true) := by
  unfold cent5At
  simp only [strictB_eq]

theorem cent5Body_of {cnt : Nat} {T : Nat → Nat} {t v z : Nat} (h5 : ord5K n w z = true)
    (h : cent5At n w cnt T t v z = true) : cent5Body n w cnt T v z (pidn n w)
      (pcomp n w (mask w) z (pidn n w))
      (pcomp n w (mask w) z (pcomp n w (mask w) z (pidn n w)))
      (pcomp n w (mask w) z (pcomp n w (mask w) z (pcomp n w (mask w) z (pidn n w))))
      (pcomp n w (mask w) z (pcomp n w (mask w) z (pcomp n w (mask w) z
        (pcomp n w (mask w) z (pidn n w)))))
      (pcomp n w (mask w) t (pidn n w))
      (pcomp n w (mask w) t (pcomp n w (mask w) z (pidn n w)))
      (pcomp n w (mask w) t (pcomp n w (mask w) z (pcomp n w (mask w) z (pidn n w))))
      (pcomp n w (mask w) t (pcomp n w (mask w) z (pcomp n w (mask w) z
        (pcomp n w (mask w) z (pidn n w)))))
      (pcomp n w (mask w) t (pcomp n w (mask w) z (pcomp n w (mask w) z
        (pcomp n w (mask w) z (pcomp n w (mask w) z (pidn n w)))))) = true := by
  rw [cent5At_eq, h5] at h
  exact h

end CFSG.KS.GH74

end
