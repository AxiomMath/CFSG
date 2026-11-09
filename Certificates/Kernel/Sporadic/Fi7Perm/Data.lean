module

import CFSG.Certificates.Kernel.Common.Repo
import CFSG.Certificates.Kernel.Common.JsonGz
public import Certificates.Kernel.Sporadic.Fi24Kit.Data
public import Certificates.Data.Kernel.Spor.Fi24SevB

#kc_repo #kc_json CFSG.KD.Fi7Perm "Certificates/Kernel/Sporadic/Fi7Perm/data/f7.json" 81281 3647099391235964515 (sl : List (Nat × List Nat × List Nat))

public section

namespace CFSG.KD.Fi7Perm

open CFSG.KC CFSG.KC.Loop CFSG.KC.LceS CFSG.KC.Fi24Net CFSG.KC.Fi24Kit CFSG.KC.Fi24ThreeO
  CFSG.KC.Fi24Sev CFSG.KC.Fi24SevB CFSG.KD.Fi24Net CFSG.KD.Fi24Kit

@[expose] noncomputable def U (k : Nat) : List Nat := findU sl k

@[expose] noncomputable def slCut : List Nat :=
  [0, 15, 24, 35, 41, 47, 52, 56, 57, 61, 66, 108, 119, 126, 132, 138, 145, 151, 158, 164, 170, 176,
    182, 188, 194, 199, 204, 205, 209, 210, 215, 216, 221, 226, 232, 238, 244, 250, 256, 261, 266,
    272, 278, 281, 283, 287, 289, 293, 296, 300, 302, 307, 309, 312, 314, 320, 326, 332, 337, 342,
    347, 353, 358, 364, 370, 374, 378, 383, 389, 395, 400, 405, 410, 415, 420, 426, 432, 438, 442,
    461, 471, 479, 486, 493, 499, 504, 510, 515, 521, 527, 532, 538, 544, 550, 556, 561, 566, 571,
    576, 577, 581, 583, 585, 591, 597, 603, 609, 614, 619, 625, 630, 635, 640, 646, 650, 653, 656,
    658, 660, 662, 667, 672, 678, 684, 690, 696, 702, 708, 714, 720, 725, 727, 729, 734, 737, 741,
    744, 747, 749, 752, 755, 757, 763, 769, 774, 779, 785, 791, 796, 802, 808, 809, 810, 811, 812,
    813, 814, 815, 816, 820, 825, 831, 837, 842, 848, 853, 859, 864, 870, 876, 882, 887, 892, 898,
    904, 910, 916, 921, 926, 930, 931, 932, 933]

@[expose] noncomputable def slQ (i : Nat) : List (Nat × List Nat × List Nat) :=
  (sl.drop (nthD (nat_lit 0) slCut i)).take
    (Nat.sub (nthD (nat_lit 0) slCut (Nat.succ i)) (nthD (nat_lit 0) slCut i))

@[expose] noncomputable def bigL : List Nat :=
  [7, 26, 28, 30, 151, 152, 153, 154, 155, 156, 157, 179, 180]

@[expose] noncomputable def slBig (i : Nat) : Bool :=
  List.rec (motive := fun _ => Bool) false (fun k _ ih => orB (Nat.beq i k) ih) bigL

@[expose] noncomputable def slc (i : Nat) : Bool :=
  Bool.rec (motive := fun _ => Bool)
    (Bool.rec (motive := fun _ => Bool) (slIn NW NT sl (slQ i)) (slInB NW NT sl (slQ i)) (slBig i))
    true (Nat.beq i (nat_lit 180))

@[expose] noncomputable def slcL (i : Nat) : Bool :=
  allL (fun e => allL (fun z => andB (Nat.ble (nat_lit 2) z) (orB (Nat.ble z (nat_lit 5))
    (andB (Nat.blt (Nat.sub (Nat.shiftRight z (nat_lit 1)) (nat_lit 3)) e.1)
      (hasU sl (Nat.sub (Nat.shiftRight z (nat_lit 1)) (nat_lit 3)))))) e.2.1) (slQ i)

@[expose] noncomputable def slcP (i b : Nat) : Bool :=
  allL (fun e => Nat.beq (ptCB NW NT (expU sl e.2.1) b) (ptCB NW NT e.2.2 b)) (slQ i)

@[expose] noncomputable def fEq : Bool :=
  eqOK NW NT [(U (nat_lit 1203), U (nat_lit 0)), (U (nat_lit 1204), U (nat_lit 1)),
    (U (nat_lit 1085) ++ U (nat_lit 67), U (nat_lit 67) ++ U (nat_lit 1085)),
    (U (nat_lit 1086) ++ U (nat_lit 67), U (nat_lit 67) ++ U (nat_lit 1086)),
    (U (nat_lit 1082) ++ U (nat_lit 66), U (nat_lit 66) ++ U (nat_lit 1082)),
    (U (nat_lit 1083) ++ U (nat_lit 66), U (nat_lit 66) ++ U (nat_lit 1083)),
    (U (nat_lit 1084) ++ U (nat_lit 66), U (nat_lit 66) ++ U (nat_lit 1084)),
    (pw (U (nat_lit 1205)) (nat_lit 4), [])]

@[expose] noncomputable def fNe : Bool := neOK NW NT [(pw (U (nat_lit 1205)) (nat_lit 2), [])]

end CFSG.KD.Fi7Perm

end
