module

public import Certificates.Kernel.Sporadic.OddCore.MulHGlue
public import CFSG.Certificates.Kernel.Misc.PairCountSound

public section

namespace CFSG.KS.MulH

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KC.BfsPin
open CFSG.Sporadic.Th.Native CFSG.Sporadic.Schreier.Native CFSG.Sporadic.SmallOddCore.Native
open CFSG.Monster.B.Co2.Native

theorem pg_lt' {n w X x : Nat} (hX : canonK n w (mask w) (n * w) X = true) (hx : x < n) :
    pg w (mask w) X x < n := by
  unfold canonK at hX
  simp only [bAnd_iff] at hX
  exact Nat.le_of_ble_eq_true (allN_spec hX.2.2 x hx)

theorem pg_pcomp' {n w p q x : Nat} (hp : canonK n w (mask w) (n * w) p = true)
    (hq : canonK n w (mask w) (n * w) q = true) (hx : x < n) :
    pg w (mask w) (pcomp n w (mask w) p q) x = pg w (mask w) p (pg w (mask w) q x) := by
  have h := congrArg (·[x]!) (compA_unpack hp hq)
  rw [CFSG.KC.Misc.PairCount.unpack_get hx, CertificateChecks.KernelSpor.OddCore.compA_get hx,
    CFSG.KC.Misc.PairCount.unpack_get hx, CFSG.KC.Misc.PairCount.unpack_get (pg_lt' hq hx)] at h
  exact h.symm

theorem invoOK_eq' {n : Nat} (hn : n < 2 ^ 32) (P : Table) :
    CFSG.Sporadic.Th.Native.invoOK n P = tblEq n (compT n P P) (idT n) := by
  unfold CFSG.Sporadic.Th.Native.invoOK tblEq
  rw [Bool.eq_iff_iff, CFSG.KS.TW.allIn_iff, CFSG.KS.TW.allIn_iff]
  refine forall_congr' fun i => imp_congr_right fun hi => ?_
  have h1 : ap (compT n P P) i = ap P (ap P i) := by
    unfold ap compT
    rw [getElem!_pos _ i (by simpa using hi), Array.getElem_ofFn]
  have h2 : ap (idT n) i = i := by
    unfold ap idT
    rw [getElem!_pos _ i (by simpa using hi), Array.getElem_ofFn, UInt32.toNat_ofNat',
      Nat.mod_eq_of_lt (by omega)]
  rw [h1, h2]

theorem involOK_unpack' {n w X : Nat} (hn : n < 2 ^ 32)
    (hid : idT n = tabT (unpack n w (pidn n w))) (hidc : canonK n w (mask w) (n * w) (pidn n w) =
        true)
    (hX : canonK n w (mask w) (n * w) X = true) :
    CFSG.Sporadic.SmallOddCore.involOK n (tabT (unpack n w X)) =
      bAnd(Nat.beq (pcomp n w (mask w) X X) (pidn n w), bIf(Nat.beq X (pidn n w), false, true)) :=
          by
  unfold CFSG.Sporadic.SmallOddCore.involOK
  rw [invoOK_eq' hn, compT_unpack hX hX, hid, tblEq_unpack (canonK_pcomp hX hX) hidc,
    tblEq_unpack hX hidc]
  cases Nat.beq (pcomp n w (mask w) X X) (pidn n w) <;> cases Nat.beq X (pidn n w) <;> rfl

@[expose] def Pows (n w X : Nat) (P : Nat → Nat) : Prop :=
  P 0 = pidn n w ∧ ∀ e, P (e + 1) = pcomp n w (mask w) X (P e)

theorem pows_canon {n w X : Nat} {P : Nat → Nat} (hP : Pows n w X P)
    (hidc : canonK n w (mask w) (n * w) (pidn n w) = true)
    (hX : canonK n w (mask w) (n * w) X = true) : ∀ e, canonK n w (mask w) (n * w) (P e) = true
  | 0 => by rw [hP.1]; exact hidc
  | e + 1 => by rw [hP.2 e]; exact canonK_pcomp hX (pows_canon hP hidc hX e)

theorem powT_unpack {n w X : Nat} {P : Nat → Nat} (hP : Pows n w X P)
    (hid : idT n = tabT (unpack n w (pidn n w))) (hidc : canonK n w (mask w) (n * w) (pidn n w) =
        true)
    (hX : canonK n w (mask w) (n * w) X = true) :
    ∀ e, powT n e (tabT (unpack n w X)) = tabT (unpack n w (P e))
  | 0 => by rw [hP.1]; exact hid
  | e + 1 => by
    rw [powT, powT_unpack hP hid hidc hX e, compT_unpack hX (pows_canon hP hidc hX e), hP.2 e]

theorem apPowW_unpack {n w X : Nat} {P : Nat → Nat} (hP : Pows n w X P)
    (hidA : idA n = unpack n w (pidn n w)) (hidc : canonK n w (mask w) (n * w) (pidn n w) = true)
    (hX : canonK n w (mask w) (n * w) X = true) :
    ∀ e, ∀ i < n, CFSG.Sporadic.Schreier.Native.apPowW [tabT (unpack n w X)] e i =
      pg w (mask w) (P e) i
  | 0, i, hi => by
    have h := congrArg (·[i]!) hidA
    rw [CertificateChecks.KernelSpor.OddCore.idA_get hi, CFSG.KC.Misc.PairCount.unpack_get hi] at h
    rw [hP.1, ← h]
    rfl
  | e + 1, i, hi => by
    have ih := apPowW_unpack hP hidA hidc hX e i hi
    have hc := pows_canon hP hidc hX e
    rw [CFSG.Sporadic.Schreier.Native.apPowW, ih, hP.2 e, pg_pcomp' hX hc hi]
    unfold CFSG.Sporadic.Schreier.Native.apW
    simp only [List.foldr_cons, List.foldr_nil]
    rw [ap_tabT _ (unpack_lt hX), CFSG.KC.Misc.PairCount.unpack_get (pg_lt' hc hi)]

theorem powFixW_unpack {n w X : Nat} {P : Nat → Nat} (hP : Pows n w X P)
    (hidA : idA n = unpack n w (pidn n w)) (hidc : canonK n w (mask w) (n * w) (pidn n w) = true)
    (hX : canonK n w (mask w) (n * w) X = true) (e : Nat) :
    CFSG.Sporadic.Schreier.Native.powFixW n [tabT (unpack n w X)] e = Nat.beq (P e) (pidn n w) := by
  have hc := pows_canon hP hidc hX e
  rw [← eqA_unpack hc hidc, ← hidA]
  unfold CFSG.Sporadic.Schreier.Native.powFixW eqA
  rw [Bool.eq_iff_iff, CFSG.KS.TW.allIn_iff, allLt_iff']
  refine forall_congr' fun i => imp_congr_right fun hi => ?_
  rw [apPowW_unpack hP hidA hidc hX e i hi, CertificateChecks.KernelSpor.OddCore.idA_get hi,
    CFSG.KC.Misc.PairCount.unpack_get hi]

theorem ordTest_unpack {n w X : Nat} {P : Nat → Nat} (hP : Pows n w X P)
    (hidA : idA n = unpack n w (pidn n w)) (hidc : canonK n w (mask w) (n * w) (pidn n w) = true)
    (hX : canonK n w (mask w) (n * w) X = true) (m : Nat) :
    CFSG.Sporadic.Schreier.Native.ordTest n m (tabT (unpack n w X)) =
      (Nat.beq (P m) (pidn n w) &&
        (CFSG.Sporadic.Schreier.Native.divParts m).all fun e => !Nat.beq (P e) (pidn n w)) := by
  unfold CFSG.Sporadic.Schreier.Native.ordTest CFSG.Sporadic.Schreier.Native.ordW
  simp only [powFixW_unpack hP hidA hidc hX]

theorem selOK_unpack {n w X : Nat} {P : Nat → Nat} (hP : Pows n w X P)
    (hid : idT n = tabT (unpack n w (pidn n w))) (hidc : canonK n w (mask w) (n * w) (pidn n w) =
        true)
    (hX : canonK n w (mask w) (n * w) X = true) (ps : List Nat) :
    CFSG.Sporadic.SmallOddCore.selOK n ps (tabT (unpack n w X)) =
      (!Nat.beq X (pidn n w) && ps.any fun p => Nat.beq (P p) (pidn n w)) := by
  unfold CFSG.Sporadic.SmallOddCore.selOK
  simp only [powT_unpack hP hid hidc hX]
  rw [hid]
  simp only [tblEq_unpack, hX, hidc, pows_canon hP hidc hX]

end CFSG.KS.MulH

end
