module

public import Certificates.Kernel.RouteP.Lines.PresW
import CFSG.Certificates.Kernel.Common.Harness
import CFSG.Certificates.Kernel.Common.Repo
import CFSG.Certificates.Kernel.Common.SliceRange

set_option Elab.async false

#kc_repo #kc_ktree CFSG.KD.RouteP.PresLK R "Certificates/Kernel/RouteP/Lines/data/presl.bin" 65536 4 1048576
  18430663107813340512

public section

#kc_slice_range CFSG.KD.RouteP.plckL CFSG.KD.RouteP.PresLC.p 0 159
#kc_slice_range CFSG.KD.RouteP.plckL CFSG.KD.RouteP.PresLC.p 160 179
#kc_slice_range CFSG.KD.RouteP.plckL CFSG.KD.RouteP.PresLC.p 180 199
#kc_slice_range CFSG.KD.RouteP.plckL CFSG.KD.RouteP.PresLC.p 200 219
#kc_slice_range CFSG.KD.RouteP.plckL CFSG.KD.RouteP.PresLC.p 220 260
#kc_slice_range CFSG.KD.RouteP.plckL CFSG.KD.RouteP.PresLC.p 260 740
#kc_slice_range CFSG.KD.RouteP.bgckL CFSG.KD.RouteP.PresLC.b 0 39
#kc_slice_range CFSG.KD.RouteP.bgckL CFSG.KD.RouteP.PresLC.b 40 79

end

namespace CFSG.KD.RouteP.PresLK

open CFSG.KC.Loop CFSG.KC.RouteP CFSG.KD.RouteP

theorem strictN_eq (y : Nat) (k : Nat → Nat) : strictN y k = k y := by cases y <;> rfl

theorem walkK_append (NW : Nat → Nat → Nat) (KA KB : Nat → Nat) (a b : List Int) (c : Nat) :
    walkK NW KA KB (a ++ b) c = walkK NW KA KB b (walkK NW KA KB a c) := by
  induction a generalizing c with
  | nil => rfl
  | cons z a ih =>
    change strictN (stepK NW KA KB z c) (walkK NW KA KB (a ++ b)) =
      walkK NW KA KB b (strictN (stepK NW KA KB z c) (walkK NW KA KB a))
    rw [strictN_eq, strictN_eq, ih]

theorem wordKOK_two {w a b : List Int} {c₁ j : Nat} (hw : w = a ++ b)
    (ha : Nat.beq (walkK NWP KAP KBP a (nat_lit 0)) c₁ = true)
    (hb : Nat.beq (walkK NWP KAP KBP b c₁) (mk (KAP j) (KBP j)) = true) : wordKOK NWP KAP KBP w j = true := by
  subst hw
  unfold wordKOK
  rw [walkK_append, Nat.eq_of_beq_eq_true ha]
  exact hb

theorem plckL_shift {g i j : Nat} (hi : Nat.div g 20 = i) (hk : Nat.mod g 20 = 19) (hj : 2 + i = j)
    (h : wordKOK NWP KAP KBP PresW.PX.toArray[i]! j = true) : plckL g = true := by
  subst hj
  unfold plckL lineXOK
  rw [hi, hk]
  exact h

theorem bgckL_shift {g i j : Nat} (hi : Nat.div g 20 = i) (hk : Nat.mod g 20 = 19) (hj : bgT i = j)
    (h : wordKOK NWP KAP KBP PresW.BX.toArray[i]! j = true) : bgckL g = true := by
  subst hj
  unfold bgckL lineXOK
  rw [hi, hk]
  exact h

def p7a : List Int := [4, -9, -8, -4, -7, -6, -8, -5, -5, 7, 7, -9, -9, 8, -5, -5, 3, -6, 5, 3, -6, -7, 6, 7, -8, 7, -6, -4, 9, 3, -5, -6, -6, 8, 6, 7, -5, 8, -7, -6, 4, -5, 3, 7, 4, -9, 6, -9, -8, -9, 4, 5, 3, -5, -6, 5, 5, 7, -8, 6, 3, 6, -8, 5, 3, 9, -7, 4, 8, 5, 4, 9, 3, 8, 7, 7, 3, 6, -5]

def p7b : List Int := [9, -8, -4, -8, -4, -4, 7, 4, -5, 7, 4, 6, 6, 9, -4, -5, -6, 3, 8, -4, -9, -8, -7, -5, -8, 4, 3, 6, -7, -8, 5, -8, -9, -9, 6, 3, -7, 6, -4, 9, 9, 6, -4, -9, 6, 8, 4, 5, 3, 6, 4, 4, 3, 4, 3, 8, 8, 8, -9, 3, 8, -4, 3, 6, -5, 7, -6, -8, 5, 9, 8, 8, 8, -9, -7, -9, -9, -7]

theorem p7w : PresW.PX.toArray[7]! = p7a ++ p7b := by decide +kernel

theorem p159a : Nat.beq (walkK NWP KAP KBP p7a (nat_lit 0)) (mk (R 0) (R 1)) = true := by
  quickRfl

theorem p159b : Nat.beq (walkK NWP KAP KBP p7b (mk (R 0) (R 1)))
    (mk (KAP 9) (KBP 9)) = true := by
  quickRfl

public theorem _root_.CFSG.KD.RouteP.PresLC.p159 : plckL (nat_lit 159) = true :=
  plckL_shift (i := 7) (j := 9) rfl rfl rfl (wordKOK_two p7w p159a p159b)

def p8a : List Int := [5, -8, -10, -8, -7, -7, -6, 10, 5, -4, -4, -5, -4, -6, 8, 3, 7, -10, -8, -6, 5, 7, 3, -10, 4, -5, 3, 8, -7, -4, 9, 9, -7, -6, 10, -9, -7, 10, -9, 10, 4, -6, -5, -10, 8, 10, -9, 3, -4, 7, -6, -4, 9, 4, -9, 6, 8, 7, 5, 8, 3, -9, 10, 9, 5, 9, -7, -5, -10, -7, 3, 4, 3, -10, -8, 10, 10, 7, 3, -8, -7, 6, 5, 8, -10, 6, -10, 7, -9]

def p8b : List Int := [-7, -7, 3, 8, 9, -5, 8, 6, -8, 7, -10, -10, -7, 3, 9, 6, 5, 6, 4, 10, -7, 6, -8, 4, -10, 7, -5, -10, 6, -5, 7, -5, -6, 3, -8, 3, -8, -10, -6, 10, -5, -6, 10, 8, -7, 5, -7, 6, 8, -6, 4, 8, -9, 5, 8, 4, -10, -6, 4, -10, 8, 8, 4, -10, 3, -8, 5, 9, 8, -9, -5, -7, -8, -8, -10, 9, -7, -7, -10, -9, -10, 9, -10, -9, -9, -10, -9, -10, -9]

theorem p8w : PresW.PX.toArray[8]! = p8a ++ p8b := by decide +kernel

theorem p179a : Nat.beq (walkK NWP KAP KBP p8a (nat_lit 0)) (mk (R 2) (R 3)) = true := by
  quickRfl

theorem p179b : Nat.beq (walkK NWP KAP KBP p8b (mk (R 2) (R 3)))
    (mk (KAP 10) (KBP 10)) = true := by
  quickRfl

public theorem _root_.CFSG.KD.RouteP.PresLC.p179 : plckL (nat_lit 179) = true :=
  plckL_shift (i := 8) (j := 10) rfl rfl rfl (wordKOK_two p8w p179a p179b)

def p9a : List Int := [-10, -11, -5, 6, 11, -8, 5, -4, -8, 4, -5, -7, -4, 6, 9, 6, -9, -6, -6, 3, -6, 3, -10, -5, -8, -7, 4, 6, 5, 11, 6, -9, 3, -6, -4, 8, -6, -9, -9, -9, 4, 5, 3, -10, -8, 6, 8, -5, 6, -9, 7, 9, 5, -9, -11, -6, 8, -11, 5, -6, 3, -10, 4, -8, 6, -4, 3, -11, 4, -10, -8, 9, 4, 8, 9, 6, 7, 3, 10, 7, 7, 7, -8, 5, 7, -9, 3]

def p9b : List Int := [6, -8, -4, 9, 11, -5, -4, 8, 11, 9, 4, 9, 9, 4, 5, -9, 5, 10, -4, -10, 3, 11, -4, 6, -9, 3, 6, 7, 11, -4, -8, -4, -4, -7, 4, 7, 5, 5, 7, -4, 10, -7, -10, -10, 11, -6, 9, 7, 4, -8, 3, -9, 3, 11, -9, -7, -7, -8, -6, -8, -8, 10, -5, -9, -6, -10, -7, -5, -4, 9, -5, 11, 8, -10, -5, 8, 7, 8, 11, -9, -7, 10, -9, 11, 10, 9, 9]

theorem p9w : PresW.PX.toArray[9]! = p9a ++ p9b := by decide +kernel

theorem p199a : Nat.beq (walkK NWP KAP KBP p9a (nat_lit 0)) (mk (R 4) (R 5)) = true := by
  quickRfl

theorem p199b : Nat.beq (walkK NWP KAP KBP p9b (mk (R 4) (R 5)))
    (mk (KAP 11) (KBP 11)) = true := by
  quickRfl

public theorem _root_.CFSG.KD.RouteP.PresLC.p199 : plckL (nat_lit 199) = true :=
  plckL_shift (i := 9) (j := 11) rfl rfl rfl (wordKOK_two p9w p199a p199b)

def p10a : List Int := [-4, -5, 7, 7, -11, 5, -11, 4, -7, 3, -10, 3, 4, 10, 5, 9, -12, -6, -9, 8, 12, 5, 6, 4, 7, -8, 7, -9, 3, 4, 6, 5, 4, -8, 5, -6, 5, -8, -4, 9, -7, -4, -10, 9, 3, -11, 10, 7, -12, -11, 9, -7, -8, 12, 12, 12, 11, -5, -7, 3, -8, 5, 4, 3, -5, 9, 5, 6, 3, 8, 6, 12, -9, -9, 12, 12, 8, 8, -6, -7, 5, -11, 4, 4]

def p10b : List Int := [-11, -4, 9, 6, 5, -12, -12, -11, 9, 3, 5, 9, 6, 6, 5, -7, 3, 10, -5, -7, -6, 3, 8, -6, -11, 5, 3, 12, 10, 4, -11, -9, -8, -8, -8, -4, 7, -12, 6, 4, -9, -10, 3, 4, 6, -4, -11, 4, -12, 3, 9, 11, 12, 4, 4, 10, -9, 5, -9, -4, -10, -9, 7, 7, 9, 10, 10, -7, -4, -8, -6, 12, 5, 10, 7, 8, -7, -12, -7, 10, 10, 9, -10]

theorem p10w : PresW.PX.toArray[10]! = p10a ++ p10b := by decide +kernel

theorem p219a : Nat.beq (walkK NWP KAP KBP p10a (nat_lit 0)) (mk (R 6) (R 7)) = true := by
  quickRfl

theorem p219b : Nat.beq (walkK NWP KAP KBP p10b (mk (R 6) (R 7)))
    (mk (KAP 12) (KBP 12)) = true := by
  quickRfl

public theorem _root_.CFSG.KD.RouteP.PresLC.p219 : plckL (nat_lit 219) = true :=
  plckL_shift (i := 10) (j := 12) rfl rfl rfl (wordKOK_two p10w p219a p219b)

def b1a : List Int := [36, -35, 31, -37, 34, -33, 32, -31, 39, -38, -29, 30, -31, 36, -35, 31, -37, 34, -33, 32, -31, 39, -38, -29, 30, -31, 36, -35, 31, -37, 34, -33, 32, -31, 39, -38, -29, 30, -31, 36, -35, 31, -37, 34, -33, 32, -31, 39, -38, -29, 30, -31, 36, -35, 31, -37, 34, -33, 32, -31, 39, -38, -29, 30, -31, 36, -35, 31, -37, 34, -33, 32, -31, 39, -38, -29, 30, -31, 36, -35, 31, -37, 34, -33, 32, -31, 39, -38, -29, 30, -31, 36, -35, 31, -37, 34, -33, 32, -31, 39, -38, -29, 30, -31, 36, -35, 31, -37, 34, -33, 32]

def b1b : List Int := [-31, 39, -38, -29, 30, -31, 36, -35, 31, -37, 34, -33, 32, -31, 39, -38, -29, 30, -31, 36, -35, 31, -37, 34, -33, 32, -31, 39, -38, -29, 30, -31, 36, -35, 31, -37, 34, -33, 32, -31, 39, -38, -29, 30, -31, 36, -35, 31, -37, 34, -33, 32, -31, 39, -38, -29, 30, -31, 36, -35, 31, -37, 34, -33, 32, -31, 39, -38, -29, 30, -31, 36, -35, 31, -37, 34, -33, 32, -31, 39, -38, -29, 30, -31, 36, -35, 31, -37, 34, -33, 32, -31, 39, -38, -29, 30, -31, 36, -35, 31, -37, 34, -33, 32, -31, 39, -38, -29, 30, -31]

theorem b1w : PresW.BX.toArray[1]! = b1a ++ b1b := by decide +kernel

theorem b39a : Nat.beq (walkK NWP KAP KBP b1a (nat_lit 0)) (mk (R 12) (R 13)) = true := by
  quickRfl

theorem b39b : Nat.beq (walkK NWP KAP KBP b1b (mk (R 12) (R 13)))
    (mk (KAP 40) (KBP 40)) = true := by
  quickRfl

public theorem _root_.CFSG.KD.RouteP.PresLC.b39 : bgckL (nat_lit 39) = true :=
  bgckL_shift (i := 1) (j := 40) rfl rfl rfl (wordKOK_two b1w b39a b39b)

def b3a : List Int := [41, -40, 33, 36, 30, 39, -29, 34, 35, 34, 36, 29, 31, 32, 33, 35, 36, 31, 33, -38, 32, 30, 36, 39, 29, 33, 34, 33, 31, 33, 32, 36, 37, 33, 36, 30, 39, -29, 34, 35, 34, 36, 29, 31, 32, 33, 35, 36, 31, 33, -38, 32, 30, 36, 39, 29, 33, 34, 33, 31, 33, 32, 36, 37, 33, 36, 30, 39, -29, 34, 35, 34, 36, 29, 31, 32, 33, 35, 36, 31, 33, -38, 32, 30, 36, 39, 29, 33, 34, 33, 31, 33, 32, 36, 37, 33, 36, 30, 39, -29, 34, 35, 34, 36, 29, 31, 32, 33, 35, 36]

def b3b : List Int := [31, 33, -38, 32, 30, 36, 39, 29, 33, 34, 33, 31, 33, 32, 36, 37, 33, 36, 30, 39, -29, 34, 35, 34, 36, 29, 31, 32, 33, 35, 36, 31, 33, -38, 32, 30, 36, 39, 29, 33, 34, 33, 31, 33, 32, 36, 37, 33, 36, 30, 39, -29, 34, 35, 34, 36, 29, 31, 32, 33, 35, 36, 31, 33, -38, 32, 30, 36, 39, 29, 33, 34, 33, 31, 33, 32, 36, 37, 33, 36, 30, 39, -29, 34, 35, 34, 36, 29, 31, 32, 33, 35, 36, 31, 33, -38, 32, 30, 36, 39, 29, 33, 34, 33, 31, 33, 32, 36, 37, 40]

theorem b3w : PresW.BX.toArray[3]! = b3a ++ b3b := by decide +kernel

theorem b79a : Nat.beq (walkK NWP KAP KBP b3a (nat_lit 0)) (mk (R 14) (R 15)) = true := by
  quickRfl

theorem b79b : Nat.beq (walkK NWP KAP KBP b3b (mk (R 14) (R 15)))
    (mk (KAP 1) (KBP 1)) = true := by
  quickRfl

public theorem _root_.CFSG.KD.RouteP.PresLC.b79 : bgckL (nat_lit 79) = true :=
  bgckL_shift (i := 3) (j := 1) rfl rfl rfl (wordKOK_two b3w b79a b79b)

end CFSG.KD.RouteP.PresLK
