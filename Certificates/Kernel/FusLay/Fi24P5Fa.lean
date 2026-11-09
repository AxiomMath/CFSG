module

public import Certificates.Kernel.FusLay.Fi24P5D
public import Certificates.Data.Kernel.OpsLayFillOne
public import CFSG.Certificates.Kernel.Common.Each
public import CFSG.Certificates.Kernel.F3PlanesMul

set_option maxRecDepth 400000

public section

namespace CertificateChecks.KernelFusLay.Fi24P5

meta def wx4 : List (Nat × Nat) := [(49, 1), (49, 1), (49, 1), (49, 1)]
meta def wy4 : List (Nat × Nat) := [(101, 1), (101, 1), (101, 1), (101, 1)]
meta def wh6 : List (Nat × Nat) := [(158, 1), (158, 1), (158, 1), (158, 1), (158, 1), (158, 1)]
meta def wb2 : List (Nat × Nat) := [(1, 1), (1, 1)]
meta def wxy : List (Nat × Nat) := [(49, 1), (101, 1)]
meta def wxy2 : List (Nat × Nat) := [(49, 1), (101, 1), (101, 1)]
meta def wq0 : List (Nat × Nat) := [(0, 1), (49, 1)]
meta def wq59 : List (Nat × Nat) := [(59, 1), (49, 1)]
meta def wq72 : List (Nat × Nat) := [(72, 1), (49, 1)]
meta def wq87 : List (Nat × Nat) := [(87, 1), (49, 1)]
meta def wq100 : List (Nat × Nat) := [(100, 1), (49, 1)]
meta def wq158 : List (Nat × Nat) := [(158, 1), (49, 1)]
meta def wq109 : List (Nat × Nat) := [(109, 1), (49, 1), (101, 1)]
meta def wq114 : List (Nat × Nat) := [(114, 1), (49, 1), (101, 1), (101, 1)]

end CertificateChecks.KernelFusLay.Fi24P5

#lay_wsegs_f CertificateChecks.KernelFusLay.Fi24P5.Vx4 3 781 CertificateChecks.KernelFusLay.Fi24P5.S160
  CertificateChecks.KernelFusLay.Fi24P5.outs CertificateChecks.KernelFusLay.Fi24P5.wx4 1
#lay_wsegs_f CertificateChecks.KernelFusLay.Fi24P5.Vy4 3 781 CertificateChecks.KernelFusLay.Fi24P5.S160
  CertificateChecks.KernelFusLay.Fi24P5.outs CertificateChecks.KernelFusLay.Fi24P5.wy4 1
#lay_wsegs_f CertificateChecks.KernelFusLay.Fi24P5.Vh6 3 781 CertificateChecks.KernelFusLay.Fi24P5.S160
  CertificateChecks.KernelFusLay.Fi24P5.outs CertificateChecks.KernelFusLay.Fi24P5.wh6 1
#lay_wsegs_f CertificateChecks.KernelFusLay.Fi24P5.Vb2 3 781 CertificateChecks.KernelFusLay.Fi24P5.S160
  CertificateChecks.KernelFusLay.Fi24P5.outs CertificateChecks.KernelFusLay.Fi24P5.wb2 2
#lay_wsegs_f CertificateChecks.KernelFusLay.Fi24P5.Vxy 3 781 CertificateChecks.KernelFusLay.Fi24P5.S160
  CertificateChecks.KernelFusLay.Fi24P5.outs CertificateChecks.KernelFusLay.Fi24P5.wxy 2
#lay_wsegs_f CertificateChecks.KernelFusLay.Fi24P5.Vxy2 3 781 CertificateChecks.KernelFusLay.Fi24P5.S160
  CertificateChecks.KernelFusLay.Fi24P5.outs CertificateChecks.KernelFusLay.Fi24P5.wxy2 3
#lay_wsegs_f CertificateChecks.KernelFusLay.Fi24P5.Q0 3 781 CertificateChecks.KernelFusLay.Fi24P5.S160
  CertificateChecks.KernelFusLay.Fi24P5.outs CertificateChecks.KernelFusLay.Fi24P5.wq0 2
#lay_wsegs_f CertificateChecks.KernelFusLay.Fi24P5.Q59 3 781 CertificateChecks.KernelFusLay.Fi24P5.S160
  CertificateChecks.KernelFusLay.Fi24P5.outs CertificateChecks.KernelFusLay.Fi24P5.wq59 2
#lay_wsegs_f CertificateChecks.KernelFusLay.Fi24P5.Q72 3 781 CertificateChecks.KernelFusLay.Fi24P5.S160
  CertificateChecks.KernelFusLay.Fi24P5.outs CertificateChecks.KernelFusLay.Fi24P5.wq72 2
#lay_wsegs_f CertificateChecks.KernelFusLay.Fi24P5.Q87 3 781 CertificateChecks.KernelFusLay.Fi24P5.S160
  CertificateChecks.KernelFusLay.Fi24P5.outs CertificateChecks.KernelFusLay.Fi24P5.wq87 2
#lay_wsegs_f CertificateChecks.KernelFusLay.Fi24P5.Q100 3 781 CertificateChecks.KernelFusLay.Fi24P5.S160
  CertificateChecks.KernelFusLay.Fi24P5.outs CertificateChecks.KernelFusLay.Fi24P5.wq100 2
#lay_wsegs_f CertificateChecks.KernelFusLay.Fi24P5.Q158 3 781 CertificateChecks.KernelFusLay.Fi24P5.S160
  CertificateChecks.KernelFusLay.Fi24P5.outs CertificateChecks.KernelFusLay.Fi24P5.wq158 2
#lay_wsegs_f CertificateChecks.KernelFusLay.Fi24P5.Q109 3 781 CertificateChecks.KernelFusLay.Fi24P5.S160
  CertificateChecks.KernelFusLay.Fi24P5.outs CertificateChecks.KernelFusLay.Fi24P5.wq109 3
#lay_wsegs_f CertificateChecks.KernelFusLay.Fi24P5.Q114 3 781 CertificateChecks.KernelFusLay.Fi24P5.S160
  CertificateChecks.KernelFusLay.Fi24P5.outs CertificateChecks.KernelFusLay.Fi24P5.wq114 4

namespace CertificateChecks.KernelFusLay.Fi24P5

open CFSG.KC.LQT CFSG.KC.OpsLayK CFSG.RankThree.PartOne.CTP.Fus CertificateChecks.KernelFusLay.Fi24

theorem fiv_powK_four (c : Lay) (X : Nat) : powK c X 4 = c.mul (c.mul X X) (c.mul X X) := by
  have e : powK c X 4 = powN c (16 + 1) X 4 := rfl
  rw [e, powN_succ, strictN_val, strictN_val, powN_succ, strictN_val, strictN_val]
  rfl

theorem fiv_powK_five (c : Lay) (X : Nat) :
    powK c X 5 = c.mul X (c.mul (c.mul X X) (c.mul X X)) := by
  have e : powK c X 5 = powN c (16 + 1) X 5 := rfl
  rw [e, powN_succ, strictN_val, strictN_val, powN_succ, strictN_val, strictN_val]
  rfl

theorem fiv_powK_seven (c : Lay) (X : Nat) :
    powK c X 7 = c.mul X (c.mul (c.mul X X) (c.mul (c.mul X X) (c.mul X X))) := by
  have e : powK c X 7 = powN c (16 + 1) X 7 := rfl
  rw [e, powN_succ, strictN_val, strictN_val, powN_succ, strictN_val, strictN_val]
  rfl

theorem fiv_p3 {c : Lay} {X X2 Z : Nat} (h1 : mulEq c X X X2 = true)
    (h2 : mulEq c X X2 Z = true) : powK c X 3 = Z := by
  rw [powK_three, mulEq_eq h1, mulEq_eq h2]

theorem fiv_p5 {c : Lay} {X X2 X4 Z : Nat} (h1 : mulEq c X X X2 = true)
    (h2 : mulEq c X2 X2 X4 = true) (h3 : mulEq c X X4 Z = true) : powK c X 5 = Z := by
  rw [fiv_powK_five, mulEq_eq h1, mulEq_eq h2, mulEq_eq h3]

theorem fiv_p7 {c : Lay} {X X2 X4 X6 Z : Nat} (h1 : mulEq c X X X2 = true)
    (h2 : mulEq c X2 X2 X4 = true) (h3 : mulEq c X2 X4 X6 = true) (h4 : mulEq c X X6 Z = true) :
    powK c X 7 = Z := by
  rw [fiv_powK_seven, mulEq_eq h1, mulEq_eq h2, mulEq_eq h3, mulEq_eq h4]

theorem fiv_e1 {c : Lay} {R : List Nat} {a X : Nat} (h : mulEq c (getR c R a) c.ONE X = true) :
    evalWL c R [(a, 1)] = X := by
  simp only [evalWL, powK_one]
  exact mulEq_eq h

theorem fiv_e4 {c : Lay} {R : List Nat} {a X2 X4 Z : Nat}
    (h1 : mulEq c (getR c R a) (getR c R a) X2 = true) (h2 : mulEq c X2 X2 X4 = true)
    (h3 : mulEq c X4 c.ONE Z = true) : evalWL c R [(a, 4)] = Z := by
  simp only [evalWL, fiv_powK_four]
  rw [mulEq_eq h1, mulEq_eq h2, mulEq_eq h3]

theorem fiv_e11 {c : Lay} {R : List Nat} {a b Y Z : Nat}
    (h1 : mulEq c (getR c R b) c.ONE Y = true) (h2 : mulEq c (getR c R a) Y Z = true) :
    evalWL c R [(a, 1), (b, 1)] = Z := by
  simp only [evalWL, powK_one]
  rw [mulEq_eq h1, mulEq_eq h2]

theorem fiv_e12 {c : Lay} {R : List Nat} {a b Y2 Y Z : Nat}
    (h0 : mulEq c (getR c R b) (getR c R b) Y2 = true) (h1 : mulEq c Y2 c.ONE Y = true)
    (h2 : mulEq c (getR c R a) Y Z = true) : evalWL c R [(a, 1), (b, 2)] = Z := by
  simp only [evalWL, powK_one, powK_two]
  rw [mulEq_eq h0, mulEq_eq h1, mulEq_eq h2]

theorem fiv_ord {c : Lay} {R : List Nat} {n r e : Nat}
    (hr : (decide (r < n) && decide (0 < e) && decide (e < 65536)) = true)
    (h : powK c (getR c R r) e = c.ONE) : factL c R n (.ord r e) = true := by
  simp only [factL]
  rw [hr, h, Nat.beq_refl, Bool.and_self]

theorem fiv_conj {c : Lay} {R : List Nat} {n h : Nat} {u w : CFSG.RankThree.Asc83Table.Native.Word} {U W P : Nat}
    (hok : (decide (h < n) && wordOK n u && wordOK n w) = true) (hU : evalWL c R u = U)
    (hW : evalWL c R w = W) (h1 : mulEq c (getR c R h) U P = true)
    (h2 : mulEq c W (getR c R h) P = true) : factL c R n (.conj h u w) = true := by
  simp only [factL]
  rw [hok, hU, hW, mulEq_eq h1, mulEq_eq h2, Nat.beq_refl, Bool.and_self]

theorem fiv_eq {c : Lay} {R : List Nat} {n : Nat} {u w : CFSG.RankThree.Asc83Table.Native.Word} {P : Nat}
    (hok : (wordOK n u && wordOK n w) = true) (hu : evalWL c R u = P)
    (hw : evalWL c R w = P) : factL c R n (.eq u w) = true := by
  simp only [factL]
  rw [hok, hu, hw, Nat.beq_refl, Bool.and_self]

theorem fiv_ne {c : Lay} {R : List Nat} {n t : Nat} {u w : CFSG.RankThree.Asc83Table.Native.Word} {U W : Nat}
    (hok : (wordOK n u && wordOK n w && decide (t < c.d)) = true) (hu : evalWL c R u = U)
    (hw : evalWL c R w = W) (hv : (!Nat.beq (c.vec (c.unit t) U) (c.vec (c.unit t) W)) = true) :
    factL c R n (.ne u w t) = true := by
  simp only [factL]
  rw [hok, hu, hw, hv, Bool.and_self]

@[expose] noncomputable def pX : List Nat := [getR lay F 49, getR lay F 101, getR lay F 1,
  getR lay F 1, getR lay F 49, Vx4.W2, getR lay F 49, getR lay F 101, Vy4.W2, getR lay F 101,
  getR lay F 49, getR lay F 101, Vx4.W0, getR lay F 0, Vx4.W0, getR lay F 59, getR lay F 49,
  getR lay F 72, getR lay F 49, getR lay F 87, getR lay F 49, getR lay F 100, getR lay F 49,
  getR lay F 158, getR lay F 49, getR lay F 109, Vxy.W0, Vy4.W2, getR lay F 49, getR lay F 114,
  Vxy2.W0, getR lay F 158, Vh6.W4, Vh6.W4, getR lay F 158, getR lay F 0, getR lay F 0,
  getR lay F 59, getR lay F 72, getR lay F 87, getR lay F 100, getR lay F 109, getR lay F 114]

@[expose] noncomputable def pY : List Nat := [lay.ONE, lay.ONE, getR lay F 1, Vb2.W0,
  getR lay F 49, Vx4.W2, Vx4.W0, getR lay F 101, Vy4.W2, Vy4.W0, getR lay F 101, getR lay F 49,
  lay.ONE, getR lay F 49, getR lay F 0, getR lay F 49, getR lay F 59, getR lay F 49,
  getR lay F 72, getR lay F 49, getR lay F 87, getR lay F 49, getR lay F 100, getR lay F 49,
  getR lay F 158, Vxy.W0, getR lay F 109, lay.ONE, Vy4.W2, Vxy2.W0, getR lay F 114,
  getR lay F 158, Vh6.W4, Vh6.W2, Vh6.W0, lay.ONE, getR lay F 0, getR lay F 59, getR lay F 72,
  getR lay F 87, getR lay F 100, getR lay F 109, getR lay F 114]

@[expose] noncomputable def pZ : List Nat := [getR lay F 49, getR lay F 101, Vb2.W0, lay.ONE,
  Vx4.W2, Vx4.W0, lay.ONE, Vy4.W2, Vy4.W0, lay.ONE, Vxy.W0, Vxy.W0, Vx4.W0, Q0.W0, Q0.W0,
  Q59.W0, Q59.W0, Q72.W0, Q72.W0, Q87.W0, Q87.W0, Q100.W0, Q100.W0, Q158.W0, Q158.W0, Q109.W0,
  Q109.W0, Vy4.W2, Vxy2.W0, Q114.W0, Q114.W0, Vh6.W4, Vh6.W2, Vh6.W0, lay.ONE, getR lay F 0,
  lay.ONE, lay.ONE, lay.ONE, lay.ONE, lay.ONE, lay.ONE, lay.ONE]

@[expose] noncomputable def pr (k : Nat) : Bool :=
  mulEq lay (pX.getD k 0) (pY.getD k 0) (pZ.getD k 0)

@[expose] noncomputable def prP (k : Nat) : Bool :=
  CFSG.F3.Planes.fp3MulOK lay (nat_lit 609961) (nat_lit 20) (pX.getD k 0) (pY.getD k 0) (pZ.getD k 0)

#kc_each prP 0 43

theorem fiv_pl {k : Nat} (h : prP k = true) : pr k = true :=
  CFSG.F3.Planes.fp3MulOK_sound lay_ok rfl rfl (by decide) (by decide) rfl (by decide) h

theorem pr0 : pr (nat_lit 0) = true := fiv_pl prP0
theorem pr1 : pr (nat_lit 1) = true := fiv_pl prP1
theorem pr2 : pr (nat_lit 2) = true := fiv_pl prP2
theorem pr3 : pr (nat_lit 3) = true := fiv_pl prP3
theorem pr4 : pr (nat_lit 4) = true := fiv_pl prP4
theorem pr5 : pr (nat_lit 5) = true := fiv_pl prP5
theorem pr6 : pr (nat_lit 6) = true := fiv_pl prP6
theorem pr7 : pr (nat_lit 7) = true := fiv_pl prP7
theorem pr8 : pr (nat_lit 8) = true := fiv_pl prP8
theorem pr9 : pr (nat_lit 9) = true := fiv_pl prP9
theorem pr10 : pr (nat_lit 10) = true := fiv_pl prP10
theorem pr11 : pr (nat_lit 11) = true := fiv_pl prP11
theorem pr12 : pr (nat_lit 12) = true := fiv_pl prP12
theorem pr13 : pr (nat_lit 13) = true := fiv_pl prP13
theorem pr14 : pr (nat_lit 14) = true := fiv_pl prP14
theorem pr15 : pr (nat_lit 15) = true := fiv_pl prP15
theorem pr16 : pr (nat_lit 16) = true := fiv_pl prP16
theorem pr17 : pr (nat_lit 17) = true := fiv_pl prP17
theorem pr18 : pr (nat_lit 18) = true := fiv_pl prP18
theorem pr19 : pr (nat_lit 19) = true := fiv_pl prP19
theorem pr20 : pr (nat_lit 20) = true := fiv_pl prP20
theorem pr21 : pr (nat_lit 21) = true := fiv_pl prP21
theorem pr22 : pr (nat_lit 22) = true := fiv_pl prP22
theorem pr23 : pr (nat_lit 23) = true := fiv_pl prP23
theorem pr24 : pr (nat_lit 24) = true := fiv_pl prP24
theorem pr25 : pr (nat_lit 25) = true := fiv_pl prP25
theorem pr26 : pr (nat_lit 26) = true := fiv_pl prP26
theorem pr27 : pr (nat_lit 27) = true := fiv_pl prP27
theorem pr28 : pr (nat_lit 28) = true := fiv_pl prP28
theorem pr29 : pr (nat_lit 29) = true := fiv_pl prP29
theorem pr30 : pr (nat_lit 30) = true := fiv_pl prP30
theorem pr31 : pr (nat_lit 31) = true := fiv_pl prP31
theorem pr32 : pr (nat_lit 32) = true := fiv_pl prP32
theorem pr33 : pr (nat_lit 33) = true := fiv_pl prP33
theorem pr34 : pr (nat_lit 34) = true := fiv_pl prP34
theorem pr35 : pr (nat_lit 35) = true := fiv_pl prP35
theorem pr36 : pr (nat_lit 36) = true := fiv_pl prP36
theorem pr37 : pr (nat_lit 37) = true := fiv_pl prP37
theorem pr38 : pr (nat_lit 38) = true := fiv_pl prP38
theorem pr39 : pr (nat_lit 39) = true := fiv_pl prP39
theorem pr40 : pr (nat_lit 40) = true := fiv_pl prP40
theorem pr41 : pr (nat_lit 41) = true := fiv_pl prP41
theorem pr42 : pr (nat_lit 42) = true := fiv_pl prP42

theorem fiv_o2 {c : Lay} {R : List Nat} {n r : Nat}
    (hr : (decide (r < n) && decide (0 < 2) && decide (2 < 65536)) = true)
    (h : mulEq c (getR c R r) (getR c R r) c.ONE = true) : factL c R n (.ord r 2) = true :=
  fiv_ord hr (by rw [powK_two]; exact mulEq_eq h)

@[expose] noncomputable def nv (k : Nat) : Bool :=
  [!Nat.beq (lay.vec (lay.unit 0) Vxy.W0) (lay.vec (lay.unit 0) lay.ONE),
    !Nat.beq (lay.vec (lay.unit 0) Vxy2.W0) (lay.vec (lay.unit 0) lay.ONE),
    !Nat.beq (lay.vec (lay.unit 0) (getR lay F 49)) (lay.vec (lay.unit 0) lay.ONE)].getD k false

#kc_each nv 0 3

theorem fa0 : fa 0 = true := fiv_o2 (c := lay) (R := F) (n := fusD2Fi24N) (r := 0) rfl pr36
theorem fa5 : fa 5 = true :=
  fiv_ne (c := lay) (R := F) (n := fusD2Fi24N) (t := 0) (u := [(49, 1)]) (w := []) rfl
    (fiv_e1 pr0) rfl nv2
theorem fa6 : fa 6 = true := fa0
theorem fa8 : fa 8 = true := fa5
theorem fa9 : fa 9 = true := fiv_o2 (c := lay) (R := F) (n := fusD2Fi24N) (r := 59) rfl pr37
theorem fa11 : fa 11 = true := fa5
theorem fa12 : fa 12 = true := fiv_o2 (c := lay) (R := F) (n := fusD2Fi24N) (r := 72) rfl pr38
theorem fa14 : fa 14 = true := fa5
theorem fa15 : fa 15 = true := fiv_o2 (c := lay) (R := F) (n := fusD2Fi24N) (r := 87) rfl pr39
theorem fa17 : fa 17 = true := fa5
theorem fa18 : fa 18 = true := fiv_o2 (c := lay) (R := F) (n := fusD2Fi24N) (r := 100) rfl pr40
theorem fa20 : fa 20 = true := fa5
theorem fa21 : fa 21 = true := fiv_o2 (c := lay) (R := F) (n := fusD2Fi24N) (r := 109) rfl pr41
theorem fa24 : fa 24 = true := fiv_o2 (c := lay) (R := F) (n := fusD2Fi24N) (r := 114) rfl pr42
theorem fa29 : fa 29 = true := fa5

theorem fa1 : fa 1 = true :=
  fiv_ord (c := lay) (R := F) (n := fusD2Fi24N) (r := 1) (e := 3) rfl (fiv_p3 pr2 pr3)

theorem fa2 : fa 2 = true :=
  fiv_ord (c := lay) (R := F) (n := fusD2Fi24N) (r := 49) (e := 5) rfl (fiv_p5 pr4 pr5 pr6)

theorem fa3 : fa 3 = true :=
  fiv_ord (c := lay) (R := F) (n := fusD2Fi24N) (r := 101) (e := 5) rfl (fiv_p5 pr7 pr8 pr9)

theorem fa4 : fa 4 = true :=
  fiv_eq (c := lay) (R := F) (n := fusD2Fi24N) (u := [(49, 1), (101, 1)])
    (w := [(101, 1), (49, 1)]) rfl (fiv_e11 pr1 pr10) (fiv_e11 pr0 pr11)

theorem fa7 : fa 7 = true :=
  fiv_conj (c := lay) (R := F) (n := fusD2Fi24N) (h := 0) (u := [(49, 1)]) (w := [(49, 4)]) rfl
    (fiv_e1 pr0) (fiv_e4 pr4 pr5 pr12) pr13 pr14

theorem fa10 : fa 10 = true :=
  fiv_conj (c := lay) (R := F) (n := fusD2Fi24N) (h := 59) (u := [(49, 1)]) (w := [(49, 1)]) rfl
    (fiv_e1 pr0) (fiv_e1 pr0) pr15 pr16

theorem fa13 : fa 13 = true :=
  fiv_conj (c := lay) (R := F) (n := fusD2Fi24N) (h := 72) (u := [(49, 1)]) (w := [(49, 1)]) rfl
    (fiv_e1 pr0) (fiv_e1 pr0) pr17 pr18

theorem fa16 : fa 16 = true :=
  fiv_conj (c := lay) (R := F) (n := fusD2Fi24N) (h := 87) (u := [(49, 1)]) (w := [(49, 1)]) rfl
    (fiv_e1 pr0) (fiv_e1 pr0) pr19 pr20

theorem fa19 : fa 19 = true :=
  fiv_conj (c := lay) (R := F) (n := fusD2Fi24N) (h := 100) (u := [(49, 1)]) (w := [(49, 1)])
    rfl (fiv_e1 pr0) (fiv_e1 pr0) pr21 pr22

theorem fa22 : fa 22 = true :=
  fiv_conj (c := lay) (R := F) (n := fusD2Fi24N) (h := 109) (u := [(49, 1), (101, 1)])
    (w := [(49, 1), (101, 1)]) rfl (fiv_e11 pr1 pr10) (fiv_e11 pr1 pr10) pr25 pr26

theorem fa23 : fa 23 = true :=
  fiv_ne (c := lay) (R := F) (n := fusD2Fi24N) (t := 0) (u := [(49, 1), (101, 1)]) (w := [])
    rfl (fiv_e11 pr1 pr10) rfl nv0

theorem fa25 : fa 25 = true :=
  fiv_conj (c := lay) (R := F) (n := fusD2Fi24N) (h := 114) (u := [(49, 1), (101, 2)])
    (w := [(49, 1), (101, 2)]) rfl (fiv_e12 pr7 pr27 pr28) (fiv_e12 pr7 pr27 pr28) pr29 pr30

theorem fa26 : fa 26 = true :=
  fiv_ne (c := lay) (R := F) (n := fusD2Fi24N) (t := 0) (u := [(49, 1), (101, 2)]) (w := [])
    rfl (fiv_e12 pr7 pr27 pr28) rfl nv1

theorem fa27 : fa 27 = true :=
  fiv_ord (c := lay) (R := F) (n := fusD2Fi24N) (r := 158) (e := 7) rfl
    (fiv_p7 pr31 pr32 pr33 pr34)

theorem fa28 : fa 28 = true :=
  fiv_conj (c := lay) (R := F) (n := fusD2Fi24N) (h := 158) (u := [(49, 1)]) (w := [(49, 1)])
    rfl (fiv_e1 pr0) (fiv_e1 pr0) pr23 pr24

theorem fa30 : fa 30 = true :=
  fiv_eq (c := lay) (R := F) (n := fusD2Fi24N) (u := [(0, 1)]) (w := [(0, 1)]) rfl
    (fiv_e1 pr35) (fiv_e1 pr35)

end CertificateChecks.KernelFusLay.Fi24P5

end
