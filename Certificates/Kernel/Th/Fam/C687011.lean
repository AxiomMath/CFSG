module

public import Certificates.Kernel.Th.Fam.C687008
public import Certificates.Kernel.Th.Fam.C687011L
import CFSG.Certificates.Kernel.Common.Harness
import CFSG.Certificates.Kernel.Common.Each
import CFSG.Certificates.Kernel.Common.ListSlices
public import CFSG.Certificates.Kernel.Common.ForallTree
meta import CFSG.Certificates.Kernel.Common.ForallTree

public section

set_option maxRecDepth 100000
set_option Elab.async false

namespace CertificateChecks.KernelTh.Fam.F11

open CFSG.KC.Th.Expr CFSG.Sporadic.Th.Recog

@[expose] noncomputable def bq (e f : TE) : Bool := Nat.beq (e.pk thK) (f.pk thK)

@[expose] noncomputable def cm (e f : TE) : Bool := bq (.mul e f) (.mul f e)

@[expose] def cT : TE := wjT 2
@[expose] def dT : TE := wjT 3
@[expose] def eT : TE := wjT 4
@[expose] def sT : TE := wjT 5
@[expose] def tT : TE := wjT 6
@[expose] def uT : TE := wjT 7
@[expose] def uiT : TE := .pow uT 3
@[expose] def x1T : TE := .pow (.mul cT dT) 2
@[expose] def w1T : TE := .mul dT eT
@[expose] def w1iT : TE := .mul eT dT
@[expose] def y1T : TE := .mul (.mul w1T x1T) w1iT
@[expose] def x2T : TE := .mul (.mul uT x1T) uiT
@[expose] def w2T : TE := .mul (.mul uT w1T) uiT
@[expose] def e0T : TE := .mul (.mul dT cT) dT
@[expose] def e1T : TE := .mul (.mul uT e0T) uiT

@[expose] def e8N (n : Nat) : TE :=
  .mul (.mul (.pow .a (n % 2)) (.pow e0T (n / 2 % 2))) (.pow e1T (n / 4))

@[expose] def preN (n : Nat) : TE :=
  .mul (.mul (.pow w1T (n / 6)) (.pow w2T (n / 2 % 3))) (.pow dT (n % 2))

@[expose] def neL : List TE :=
  [cT, .mul (.mul (.mul (.mul dT eT) uT) dT) uiT, .mul (.mul (.mul (.mul dT eT) uT) dT) uT,
    .mul (.mul (.mul dT uT) dT) uT, .mul (.mul (.mul dT uT) dT) uiT]

@[expose] def ceL : List TE :=
  [.one, sT, .pow sT 6, .pow sT 2, .mul sT (.pow tT 2), .pow sT 5, .mul (.pow sT 6) (.pow tT 2)]

@[expose] def ceiL : List TE :=
  [.one, .pow sT 6, sT, .pow sT 5, .mul tT (.pow sT 6), .pow sT 2, .mul tT sT]

@[expose] def cnL : List TE :=
  [.mul (.mul (.mul dT eT) uT) dT, sT, .pow sT 2, .pow sT 3, .mul (.mul (.mul dT eT) dT) tT,
    .mul (.mul sT (.mul (.mul dT eT) dT)) sT]

@[expose] def cniL : List TE :=
  [.mul (.mul (.mul dT uiT) eT) dT, .pow sT 6, .pow sT 5, .pow sT 4,
    .mul (.pow tT 2) (.mul (.mul dT eT) dT), .mul (.mul (.pow sT 6) (.mul (.mul dT eT) dT)) (.pow sT 6)]

@[expose] def tg0 (i : Fin 5) : Nat := [3, 4, 5, 6, 7].getD i.val 0

@[expose] def tg1 (i : Fin 5) : Nat := [5, 2, 3, 3, 2].getD i.val 0

@[expose] noncomputable def pkR : Bool :=
  bq (.mul y1T x1T) (.mul (.pow x1T 3) y1T) && bq (.mul w1T y1T) (.mul (.mul y1T x1T) w1T) &&
    cm x1T x2T && cm x1T w2T && cm w1T x2T && cm w1T w2T

@[expose] noncomputable def pkE : Bool :=
  cm e0T e1T &&
    (List.finRange 8).all fun l =>
      (List.finRange l).all fun l' => bq (e8N l.val) (e8N l'.val) == false

@[expose] noncomputable def pkN : Bool :=
  (List.finRange 5).all fun i =>
    cm (neL.getD i.val .one) tT &&
      bq (.mul (neL.getD i.val .one) e0T) (.mul (e8N (tg0 i)) (neL.getD i.val .one)) &&
      bq (.mul (neL.getD i.val .one) e1T) (.mul (e8N (tg1 i)) (neL.getD i.val .one))

@[expose] noncomputable def pkCE : Bool :=
  (List.finRange 512).all fun k =>
    !cm (.nf k) tT ||
      (List.finRange 18).all fun a =>
        !(cm (.mul (preN a.val) (.nf k)) e0T && cm (.mul (preN a.val) (.nf k)) e1T) ||
          (decide (a = 0) && (List.finRange 8).any fun l => bq (.nf k) (e8N l.val))

@[expose] noncomputable def pkC : Bool :=
  (List.finRange 7).all (fun i =>
      bq (.mul (ceL.getD i.val .one) (ceiL.getD i.val .one)) .one &&
        cm (ceL.getD i.val .one) e0T) &&
    (List.finRange 6).all fun j =>
      bq (.mul (cnL.getD j.val .one) (cniL.getD j.val .one)) .one &&
        cm (cnL.getD j.val .one) e0T

@[expose] noncomputable def pkA : Bool :=
  (List.finRange 512).all fun k =>
    !cm (.nf k) e0T ||
      (List.finRange 4).any (fun l => bq (.nf k) (e8N l.val)) ||
      (List.finRange 6).any (fun j =>
        !cm (.mul (.mul (cnL.getD j.val .one) (.nf k)) (cniL.getD j.val .one)) (.nf k)) ||
      (List.finRange 7).any fun i =>
        (List.finRange 4).any fun l =>
          bq (.mul (.mul (ceL.getD i.val .one) (.nf k)) (ceiL.getD i.val .one)) (.mul e1T (e8N l.val))

@[expose] def pkCEG {E : Type} (mul : E → E → E) (q c : E → E → Bool) (nf : Fin 512 → E)
    (t e0 e1 : E) (pre e8 : Nat → E) (k : Fin 512) : Bool :=
  !c (nf k) t ||
    (List.finRange 18).all fun a =>
      !(c (mul (pre a.val) (nf k)) e0 && c (mul (pre a.val) (nf k)) e1) ||
        (decide (a = 0) && (List.finRange 8).any fun l => q (nf k) (e8 l.val))

@[expose] def pkCG {E : Type} (mul : E → E → E) (q c : E → E → Bool) (one e0 : E)
    (ce cei cn cni : List E) : Bool :=
  (List.finRange 7).all (fun i =>
      q (mul (ce.getD i.val one) (cei.getD i.val one)) one && c (ce.getD i.val one) e0) &&
    (List.finRange 6).all fun j =>
      q (mul (cn.getD j.val one) (cni.getD j.val one)) one && c (cn.getD j.val one) e0

@[expose] def pkAG {E : Type} (mul : E → E → E) (q c : E → E → Bool) (nf : Fin 512 → E)
    (one e0 e1 : E) (e8 : Nat → E) (ce cei cn cni : List E) (k : Fin 512) : Bool :=
  !c (nf k) e0 ||
    (List.finRange 4).any (fun l => q (nf k) (e8 l.val)) ||
    (List.finRange 6).any (fun j =>
      !c (mul (mul (cn.getD j.val one) (nf k)) (cni.getD j.val one)) (nf k)) ||
    (List.finRange 7).any fun i =>
      (List.finRange 4).any fun l =>
        q (mul (mul (ce.getD i.val one) (nf k)) (cei.getD i.val one)) (mul e1 (e8 l.val))

section Map

variable {E E' : Type} (f : E → E') {mul : E → E → E} {q c : E → E → Bool}
  {mul' : E' → E' → E'} {q' c' : E' → E' → Bool} (hm : ∀ a b, f (mul a b) = mul' (f a) (f b))
  (hq : ∀ a b, q a b = q' (f a) (f b)) (hc : ∀ a b, c a b = c' (f a) (f b))
include hm hq hc

theorem pkCEG_map (nf : Fin 512 → E) (t e0 e1 : E) (pre e8 : Nat → E) (k : Fin 512) :
    pkCEG mul q c nf t e0 e1 pre e8 k =
      pkCEG mul' q' c' (fun k => f (nf k)) (f t) (f e0) (f e1) (fun a => f (pre a))
        (fun l => f (e8 l)) k := by
  simp only [pkCEG, hc, hq, hm]

theorem pkCG_map (one e0 : E) (ce cei cn cni : List E) :
    pkCG mul q c one e0 ce cei cn cni =
      pkCG mul' q' c' (f one) (f e0) (ce.map f) (cei.map f) (cn.map f) (cni.map f) := by
  simp only [pkCG, hc, hq, hm, List.getD_map]

theorem pkAG_map (nf : Fin 512 → E) (one e0 e1 : E) (e8 : Nat → E) (ce cei cn cni : List E)
    (k : Fin 512) :
    pkAG mul q c nf one e0 e1 e8 ce cei cn cni k =
      pkAG mul' q' c' (fun k => f (nf k)) (f one) (f e0) (f e1) (fun l => f (e8 l)) (ce.map f)
        (cei.map f) (cn.map f) (cni.map f) k := by
  simp only [pkAG, hc, hq, hm, List.getD_map]

end Map

inductive LX where
  | one
  | a
  | lt (i : Fin 8)
  | nf (k : Fin 512)
  | mul (e f : LX)
  | pow (e : LX) (n : Nat)

@[expose] def LX.toTE : LX → TE
  | .one => .one
  | .a => .a
  | .lt i => wjT i
  | .nf k => .nf k
  | .mul e f => .mul e.toTE f.toTE
  | .pow e n => .pow e.toTE n

@[expose] noncomputable def LX.ev (V : Fin 8 → Nat) : LX → Nat
  | .one => thK.ONE
  | .a => TE.a.pk thK
  | .lt i => V i
  | .nf k => (TE.nf k).pk thK
  | .mul e f => thK.mul (e.ev V) (f.ev V)
  | .pow e n => thK.pow (e.ev V) n

theorem LX.ev_eq {V : Fin 8 → Nat} (hV : ∀ i, V i = (wjT i).pk thK) :
    ∀ x : LX, x.ev V = x.toTE.pk thK
  | .one => rfl
  | .a => rfl
  | .lt i => hV i
  | .nf _ => rfl
  | .mul e f => by
    change thK.mul (e.ev V) (f.ev V) = thK.mul (e.toTE.pk thK) (f.toTE.pk thK)
    rw [ev_eq hV e, ev_eq hV f]
  | .pow e n => by
    change thK.pow (e.ev V) n = thK.pow (e.toTE.pk thK) n
    rw [ev_eq hV e]

@[expose] def e0X : LX := .mul (.mul (.lt 3) (.lt 2)) (.lt 3)
@[expose] def uiX : LX := .pow (.lt 7) 3
@[expose] def e1X : LX := .mul (.mul (.lt 7) e0X) uiX
@[expose] def w1X : LX := .mul (.lt 3) (.lt 4)
@[expose] def w2X : LX := .mul (.mul (.lt 7) w1X) uiX

@[expose] def e8X (n : Nat) : LX :=
  .mul (.mul (.pow .a (n % 2)) (.pow e0X (n / 2 % 2))) (.pow e1X (n / 4))

@[expose] def preX (n : Nat) : LX :=
  .mul (.mul (.pow w1X (n / 6)) (.pow w2X (n / 2 % 3))) (.pow (.lt 3) (n % 2))

@[expose] def ceX : List LX :=
  [.one, .lt 5, .pow (.lt 5) 6, .pow (.lt 5) 2, .mul (.lt 5) (.pow (.lt 6) 2), .pow (.lt 5) 5,
    .mul (.pow (.lt 5) 6) (.pow (.lt 6) 2)]

@[expose] def ceiX : List LX :=
  [.one, .pow (.lt 5) 6, .lt 5, .pow (.lt 5) 5, .mul (.lt 6) (.pow (.lt 5) 6), .pow (.lt 5) 2,
    .mul (.lt 6) (.lt 5)]

@[expose] def cnX : List LX :=
  [.mul (.mul (.mul (.lt 3) (.lt 4)) (.lt 7)) (.lt 3), .lt 5, .pow (.lt 5) 2, .pow (.lt 5) 3,
    .mul (.mul (.mul (.lt 3) (.lt 4)) (.lt 3)) (.lt 6),
    .mul (.mul (.lt 5) (.mul (.mul (.lt 3) (.lt 4)) (.lt 3))) (.lt 5)]

@[expose] def cniX : List LX :=
  [.mul (.mul (.mul (.lt 3) uiX) (.lt 4)) (.lt 3), .pow (.lt 5) 6, .pow (.lt 5) 5, .pow (.lt 5) 4,
    .mul (.pow (.lt 6) 2) (.mul (.mul (.lt 3) (.lt 4)) (.lt 3)),
    .mul (.mul (.pow (.lt 5) 6) (.mul (.mul (.lt 3) (.lt 4)) (.lt 3))) (.pow (.lt 5) 6)]

@[expose] noncomputable def lvL : List Nat :=
  [CFSG.KD.Th687L.lv0, CFSG.KD.Th687L.lv1, CFSG.KD.Th687L.lv2, CFSG.KD.Th687L.lv3,
    CFSG.KD.Th687L.lv4, CFSG.KD.Th687L.lv5, CFSG.KD.Th687L.lv6, CFSG.KD.Th687L.lv7]

@[expose] noncomputable def lvF (i : Fin 8) : Nat := lvL.getD i.val 0

theorem lvOK0 : Nat.beq (lvF 0) ((wjT 0).pk thK) = true := by quickRfl
theorem lvOK1 : Nat.beq (lvF 1) ((wjT 1).pk thK) = true := by quickRfl
theorem lvOK2 : Nat.beq (lvF 2) ((wjT 2).pk thK) = true := by quickRfl
theorem lvOK3 : Nat.beq (lvF 3) ((wjT 3).pk thK) = true := by quickRfl
theorem lvOK4 : Nat.beq (lvF 4) ((wjT 4).pk thK) = true := by quickRfl
theorem lvOK5 : Nat.beq (lvF 5) ((wjT 5).pk thK) = true := by quickRfl
theorem lvOK6 : Nat.beq (lvF 6) ((wjT 6).pk thK) = true := by quickRfl
theorem lvOK7 : Nat.beq (lvF 7) ((wjT 7).pk thK) = true := by quickRfl

@[expose] noncomputable def qV (x y : LX) : Bool := Nat.beq (x.ev lvF) (y.ev lvF)

theorem lv_eq (i : Fin 8) : lvF i = (wjT i).pk thK := by
  match i with
  | ⟨0, _⟩ => exact Nat.eq_of_beq_eq_true lvOK0
  | ⟨1, _⟩ => exact Nat.eq_of_beq_eq_true lvOK1
  | ⟨2, _⟩ => exact Nat.eq_of_beq_eq_true lvOK2
  | ⟨3, _⟩ => exact Nat.eq_of_beq_eq_true lvOK3
  | ⟨4, _⟩ => exact Nat.eq_of_beq_eq_true lvOK4
  | ⟨5, _⟩ => exact Nat.eq_of_beq_eq_true lvOK5
  | ⟨6, _⟩ => exact Nat.eq_of_beq_eq_true lvOK6
  | ⟨7, _⟩ => exact Nat.eq_of_beq_eq_true lvOK7

theorem qV_eq (x y : LX) : qV x y = bq x.toTE y.toTE := by
  rw [qV, bq, LX.ev_eq lv_eq, LX.ev_eq lv_eq]

@[expose] noncomputable def cV (x y : LX) : Bool := qV (.mul x y) (.mul y x)

theorem cV_eq (x y : LX) : cV x y = cm x.toTE y.toTE := by
  rw [cV, qV_eq]
  rfl

theorem qV_fun : qV = fun x y => bq x.toTE y.toTE := funext fun x => funext fun y => qV_eq x y

theorem cV_fun : cV = fun x y => cm x.toTE y.toTE := funext fun x => funext fun y => cV_eq x y

@[expose] noncomputable def pkCEx (k : Fin 512) : Bool :=
  pkCEG LX.mul qV cV LX.nf (.lt 6) e0X e1X preX e8X k

@[expose] noncomputable def pkAx (k : Fin 512) : Bool :=
  pkAG LX.mul qV cV LX.nf .one e0X e1X e8X ceX ceiX cnX cniX k

@[expose] noncomputable def pkCx : Bool := pkCG LX.mul qV cV .one e0X ceX ceiX cnX cniX

theorem ok687011R : pkR = true := by quickRfl

theorem ok687011E : pkE = true := by quickRfl

theorem ok687011N : pkN = true := by quickRfl

@[expose] noncomputable def pkCEf (k : Fin 512) : Bool :=
  pkCEG TE.mul bq cm TE.nf tT e0T e1T preN e8N k

theorem pkCEf_eq (k : Fin 512) : pkCEf k = pkCEx k := by
  rw [pkCEx, qV_fun, cV_fun, pkCEG_map LX.toTE (mul' := TE.mul) (q' := bq) (c' := cm)
    (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl)]
  rfl

@[expose] noncomputable def pkCEs (s : Nat) : Bool :=
  (((List.finRange 512).drop (32 * s)).take 32).all pkCEx

@[expose] noncomputable def pkAf (k : Fin 512) : Bool :=
  pkAG TE.mul bq cm TE.nf .one e0T e1T e8N ceL ceiL cnL cniL k

theorem pkAf_eq (k : Fin 512) : pkAf k = pkAx k := by
  rw [pkAx, qV_fun, cV_fun, pkAG_map LX.toTE (mul' := TE.mul) (q' := bq) (c' := cm)
    (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl)]
  rfl

theorem pkC_eq : pkC = pkCx := by
  change pkCG TE.mul bq cm .one e0T ceL ceiL cnL cniL = pkCx
  rw [pkCx, qV_fun, cV_fun, pkCG_map LX.toTE (mul' := TE.mul) (q' := bq) (c' := cm)
    (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl)]
  rfl

@[expose] noncomputable def pkAs (s : Nat) : Bool :=
  (((List.finRange 512).drop (16 * s)).take 16).all pkAx

#kc_each pkCEs 0 16

#kc_each pkAs 0 32

#kc_forall_tree pkCEs_all (fun s => CertificateChecks.KernelTh.Fam.F11.pkCEs s = true) 16
  CertificateChecks.KernelTh.Fam.F11.pkCEs
#kc_forall_tree pkAs_all (fun s => CertificateChecks.KernelTh.Fam.F11.pkAs s = true) 32
  CertificateChecks.KernelTh.Fam.F11.pkAs

theorem ok687011CE : pkCE = true := by
  change (List.finRange 512).all pkCEf = true
  rw [funext pkCEf_eq]
  exact CFSG.KS.ListSlices.all_chunks pkCEx 32 16 (List.finRange 512) (by simp) pkCEs_all

theorem pkCx_true : pkCx = true := by quickRfl

theorem ok687011C : pkC = true := pkC_eq.trans pkCx_true

theorem ok687011A : pkA = true := by
  change (List.finRange 512).all pkAf = true
  rw [funext pkAf_eq]
  exact CFSG.KS.ListSlices.all_chunks pkAx 16 32 (List.finRange 512) (by simp) pkAs_all

end CertificateChecks.KernelTh.Fam.F11

end
