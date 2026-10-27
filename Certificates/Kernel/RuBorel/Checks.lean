module

public import Certificates.Kernel.RuSz.Checks
public import Certificates.Kernel.SporSch.Ru.JOrb
public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Rows.RuBorelInputs
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelRuBorel

open CFSG.KC.Enum CFSG.KS CFSG.KC.Misc.RuInv CFSG.KS.MoveK CertificateChecks.KernelSporSch
  CertificateChecks.KernelRuSz CFSG.EvenSporadicStandard.Induction.RuSz

@[expose] def rWords : List String :=
  ["abbabbabbbaba", "bbbabbabbbababbab", "bbabbbabbabbababbaba", "bbababbbabbababbabbbabab"]

@[expose] noncomputable def wP (w : String) : Nat := wordST SP (invP SP) TP (invP TP) (parseW w)

@[expose] noncomputable def x0P : Nat := wP x0Word

@[expose] noncomputable def commB (R X : Nat) : Bool := Nat.beq (mulP R X) (mulP X R)

@[expose] noncomputable def comm4 (R0 R1 R2 R3 X : Nat) : Bool :=
  bAnd(commB R0 X, bAnd(commB R1 X, bAnd(commB R2 X, commB R3 X)))

@[expose] noncomputable def centB : Bool :=
  strictB x0P fun X =>
  strictB (wP (rWords.getD 0 "")) fun R0 => strictB (wP (rWords.getD 1 "")) fun R1 =>
  strictB (wP (rWords.getD 2 "")) fun R2 => strictB (wP (rWords.getD 3 "")) fun R3 =>
    bAnd(Nat.beq (mulP X X) idP, bAnd(!(Nat.beq (apP X 2) 2), bAnd(comm4 R0 R1 R2 R3 X,
      borelGens.all fun w => strictB (wP w) fun W =>
        strictB (mulP (mulP (invP W) X) W) fun Y => comm4 R0 R1 R2 R3 Y)))

@[expose] def orbRows : List (Nat × Nat × Nat) :=
  [(2, 0, 1172), (2, 1, 650), (2, 2, 1601), (2, 3, 2668), (1172, 0, 1268), (1172, 1, 3724),
    (1172, 2, 573), (1172, 3, 4009), (650, 2, 3695), (650, 3, 629), (1601, 0, 2355),
    (1601, 2, 3811), (1601, 3, 2817), (2668, 0, 1334), (2668, 2, 1913), (2668, 3, 2654),
    (1268, 0, 434), (1268, 1, 622), (1268, 2, 2662), (1268, 3, 3367), (3724, 2, 1850),
    (573, 0, 1809), (573, 2, 2682), (573, 3, 3830), (4009, 0, 2862), (4009, 2, 969),
    (4009, 3, 1347), (3695, 0, 2800), (3695, 2, 402), (3695, 3, 2267), (629, 2, 1215),
    (629, 3, 3880), (2355, 2, 2685), (2355, 3, 1454), (3811, 2, 3866), (3811, 3, 2004),
    (2817, 0, 3273), (2817, 3, 2240), (1334, 2, 244), (1334, 3, 3027), (1913, 0, 1522),
    (1913, 3, 2661), (2654, 3, 3776), (434, 2, 3054), (434, 3, 2364), (2662, 0, 1116),
    (2662, 3, 1811), (3367, 0, 3499), (3367, 2, 2381), (1850, 2, 2220), (1850, 3, 2640),
    (2682, 2, 2765), (2682, 3, 3173), (2862, 2, 3938), (969, 3, 1962), (1347, 3, 709),
    (402, 3, 3024), (2267, 3, 1409), (1215, 0, 187), (3880, 3, 1916), (1454, 0, 1273),
    (2004, 0, 1858), (3273, 2, 777)]

@[expose] noncomputable def sel4 (R0 R1 R2 R3 j : Nat) : Nat :=
  nIf(Nat.beq j 0, R0, nIf(Nat.beq j 1, R1, nIf(Nat.beq j 2, R2, R3)))

@[expose] noncomputable def orbRowsB (rows : List (Nat × Nat × Nat)) : Bool :=
  strictB (wP (rWords.getD 0 "")) fun R0 => strictB (wP (rWords.getD 1 "")) fun R1 =>
  strictB (wP (rWords.getD 2 "")) fun R2 => strictB (wP (rWords.getD 3 "")) fun R3 =>
    rows.all fun c => Nat.beq (apP (sel4 R0 R1 R2 R3 c.2.1) c.1) c.2.2

@[expose] noncomputable def orbB : Bool := orbRowsB orbRows

@[expose] noncomputable def fixWB (h0 h1 h2 k : String) : Bool :=
  strictB (wP h0) fun H0 => strictB (wP h1) fun H1 => strictB (wP h2) fun H2 =>
    bAnd(Nat.beq (apP H0 0) 0, bAnd(Nat.beq (apP H1 0) 0, bAnd(Nat.beq (apP H2 0) 0,
      bAnd((List.range 4060).filter (fun x =>
        bAnd(Nat.beq (apP H0 x) x, bAnd(Nat.beq (apP H1 x) x, Nat.beq (apP H2 x) x))) ==
        [0, 1, 3645, 3692], Nat.beq (apP (wP k) 0) 1))))

@[expose] noncomputable def fixB : Bool :=
  fixWB (hBWords.getD 0 "") (hBWords.getD 1 "") (hBWords.getD 2 "") k1Word

@[expose] noncomputable def wordJ (v : List Nat) : Nat :=
  List.rec (motive := fun _ => Nat) idP (fun j _ ih => strictN ih fun X => mulP (RuJO.S j) X) v

@[expose] def qWord : List Nat := [9, 5, 13, 12]

@[expose] def pathSteps : List (Nat × Nat × Nat) :=
  [(1, 0, 3616), (2, 3616, 245), (1, 245, 896), (1, 3616, 3275), (1, 3275, 2631), (2, 2631, 1),
    (1, 1, 3739)]

@[expose] def tailRows : List (Nat × List Nat × Nat) :=
  [(10, [17, 15], 2), (213, [14], 3), (439, [16, 17, 16], 2), (736, [15], 3),
    (1004, [17, 16, 16], 2), (1051, [16, 17, 15], 3), (1139, [17, 16, 15], 3),
    (1150, [15, 14], 3), (1244, [16, 16, 14], 3), (1269, [16, 16, 16], 2),
    (1356, [17, 17, 17], 2), (1413, [17, 15, 14], 2), (1447, [17], 2), (1511, [17, 17, 16], 2),
    (1578, [16, 17], 3), (1844, [17, 17], 3), (1936, [17, 16, 16, 16], 3),
    (2049, [16, 15, 14], 2), (2069, [17, 17, 14], 3), (2208, [17, 17, 17, 16], 3),
    (2572, [17, 16, 17], 2), (2587, [16, 16, 16, 14], 2), (2681, [16, 17, 16, 16], 3),
    (2819, [16, 16], 3), (3072, [17, 17, 16, 17], 3), (3089, [17, 17, 17, 14], 2),
    (3163, [17, 16], 3), (3223, [16, 14], 2), (3296, [17, 14], 2), (3397, [16, 15], 2),
    (4047, [16], 2)]

@[expose] noncomputable def tailRowB (X1 : Nat) (c : Nat × List Nat × Nat) : Bool :=
  strictB (wordJ c.2.1) fun T =>
    bAnd(Nat.beq (apP T 0) 0, bAnd(Nat.beq (apP T 1) 1, bAnd(Nat.beq (apP T 2) 2,
      bAnd(Nat.beq (apP T 3) c.1, !(Nat.beq (apP T (apP X1 c.2.2)) (apP X1 (apP T c.2.2)))))))

@[expose] noncomputable def tailB : Bool :=
  strictB (wordJ qWord) fun Q => strictB (wP n1Word) fun N1 => strictB (wP n2Word) fun N2 =>
    bAnd(Nat.beq (apP Q 0) 0, bAnd(Nat.beq (apP Q 1) 896, bAnd(Nat.beq (apP Q 2) 3739,
      bAnd(pathSteps.all (fun c => Nat.beq (apP (nIf(Nat.beq c.1 1, N1, N2)) c.2.1) c.2.2),
        strictB (mulP (mulP (invP Q) N1) Q) fun X1 => tailRows.all (tailRowB X1)))))

theorem cent_ok : centB = true := by quickRfl
theorem orb_ok : orbB = true := by quickRfl
theorem fix_ok : fixB = true := by quickRfl
theorem tail_ok : tailB = true := by quickRfl

end CertificateChecks.KernelRuBorel

end
