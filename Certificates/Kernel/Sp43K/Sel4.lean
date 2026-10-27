module

public import Certificates.Data.Kernel.Sp43KSp
public import Certificates.Kernel.Sp43K.Sel3
public import Certificates.Kernel.Sp43K.Data4

public section

namespace CFSG.KD.Sp43K

open CFSG.KC.Sp43K

@[expose] noncomputable def spC (i : Nat) : Bool :=
  let n := ns.getD i ((0, 0), (0, 0))
  spT (gA i) && spT (gB i) && spT n.1.1 && spT n.1.2 && spT n.2.1 && spT n.2.2 &&
    List.rec true (fun c _ ih => spT c.1 && spT c.2.2.1 && spT c.2.2.2.1 && ih) (cs i)

@[expose] noncomputable def sp5C : Bool :=
  spT G5.1 && spT G5.2.1 && spT G5.2.2.1 && spT G5.2.2.2 && spT p0.1 && spT p0.2 &&
    spT h4.1 && spT h4.2.1 && spT h4.2.2.1 && spT h4.2.2.2.1 && spT h4.2.2.2.2 &&
    spT b.1 && spT b.2.1 && spT b.2.2.1 && spT b.2.2.2 && spT m1.1

@[expose] noncomputable def h3C : Bool :=
  m1.1 == oneT <<< 16 && decide (m1.2 < 720) && fldT (mP 3) m1.2 == m1.1

@[expose] noncomputable def h4C : Bool :=
  let p := h4.1
  let u := h4.2.1
  let v := h4.2.2.1
  okT p && p != oneT && mulT (mulT p p) p == oneT &&
    decide (h4q.1 < 1920) && fldT (mP 4) h4q.1 == p &&
    decide (h4q.2.1 < 1920) && fldT (mP 4) h4q.2.1 == u &&
    decide (h4q.2.2 < 1920) && fldT (mP 4) h4q.2.2 == v &&
    okT h4.2.2.2.1 && okT h4.2.2.2.2 &&
    mulT u h4.2.2.2.1 == oneT && mulT v h4.2.2.2.2 == oneT &&
    (conjT u h4.2.2.2.1 p == p || conjT u h4.2.2.2.1 p == mulT p p) &&
    (conjT v h4.2.2.2.2 p == p || conjT v h4.2.2.2.2 p == mulT p p) &&
    lstK u v 48 uvP uvD 0 48 uvR

@[expose] noncomputable def bC : Bool :=
  okT b.2.2.1 && okT b.2.2.2 && mulT b.1 b.2.2.1 == oneT && mulT b.2.1 b.2.2.2 == oneT &&
    lstK b.1 b.2.1 324 bP bD 0 324 bR && bq.length == 4 &&
    (bq.all fun q => decide (q < 81)) &&
    fldT p0P (bq.getD 0 0) == conjT b.1 b.2.2.1 p0.1 &&
    fldT p0P (bq.getD 1 0) == conjT b.1 b.2.2.1 p0.2 &&
    fldT p0P (bq.getD 2 0) == conjT b.2.1 b.2.2.2 p0.1 &&
    fldT p0P (bq.getD 3 0) == conjT b.2.1 b.2.2.2 p0.2

@[expose] noncomputable def n0C : Bool :=
  let n := ns.getD 0 ((0, 0), (0, 0))
  lstK n.1.1 n.2.1 40 nP nD 0 40 nR

end CFSG.KD.Sp43K

end
