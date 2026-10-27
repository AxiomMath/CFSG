module

public import Certificates.Kernel.Sporadic.OddCore.SuzMcD
public import Certificates.Kernel.Sporadic.OddCore.SuzMGF
public import Certificates.Kernel.Sporadic.OddCore.SuzRKZ
public import Certificates.Kernel.Sporadic.OddCore.SuzC1ED
public import Certificates.Kernel.Sporadic.L2.Defs2
import CFSG.Certificates.Kernel.Common.Harness
import CFSG.Certificates.Kernel.Common.EachUnfold

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSpor.SuzMcK

open CFSG.KC.Enum CFSG.KS CFSG.KS.Prim CertificateChecks.KernelSpor
open CFSG.Sporadic.SuzRecog.MixedCellData

local notation "pc" => pcomp 1782 11 (mask 11)
local notation "cn" => canonK 1782 11 (mask 11) (1782 * 11)
local notation "ie" => invEqK 1782 11 (mask 11) (1782 * 11)
local notation "Idn" => pidn 1782 11

@[expose] noncomputable def wK (w : List Nat) : Nat := SuzTwCF.wordK SuzMcG SuzMcGI w

@[expose] noncomputable def wget (D : List (List Nat)) (i : Nat) : List Nat :=
  List.rec (motive := fun _ => Nat → List Nat) (fun _ => [])
    (fun x _ ih i => Nat.rec (motive := fun _ => List Nat) x (fun i' _ => ih i') i) D i

@[expose] noncomputable def pget (D : List (List Nat × List Nat)) (i : Nat) :
    List Nat × List Nat :=
  List.rec (motive := fun _ => Nat → List Nat × List Nat) (fun _ => ([], []))
    (fun x _ ih i => Nat.rec (motive := fun _ => List Nat × List Nat) x (fun i' _ => ih i') i) D i

@[expose] noncomputable def T1 : Nat := SuzTP 1
@[expose] noncomputable def RHO : Nat := SuzTwG 2
@[expose] noncomputable def W0 : Nat := SuzTwG 6
@[expose] noncomputable def W1 : Nat := SuzMcW 0
@[expose] noncomputable def W2 : Nat := SuzMcW 1
@[expose] noncomputable def P1 : Nat := L2A 342
@[expose] noncomputable def S : Nat := SuzMcG 5
@[expose] noncomputable def SI : Nat := SuzMcGI 5
@[expose] noncomputable def TAU : Nat := SuzMcG 6
@[expose] noncomputable def C (k : Nat) : Nat := L2EL.F (Nat.add 13 k)
@[expose] noncomputable def CI (k : Nat) : Nat := L2EI (Nat.add 13 k)
@[expose] noncomputable def CP (k : Nat) : Nat := L2EL.F (Nat.add 17 k)
@[expose] noncomputable def CPI (k : Nat) : Nat := L2EI (Nat.add 17 k)
@[expose] noncomputable def X : Nat := SuzMcX 0
@[expose] noncomputable def XI : Nat := SuzMcX 1
@[expose] noncomputable def M (k j : Nat) : Nat := SuzMcM (Nat.add (Nat.mul 4 k) j)
@[expose] noncomputable def Y (k j : Nat) : Nat := SuzMcY (Nat.add (Nat.mul 4 k) j)
@[expose] noncomputable def YI (k j : Nat) : Nat := SuzMcYI (Nat.add (Nat.mul 4 k) j)
@[expose] noncomputable def D (k i : Nat) : Nat := SuzMcD (Nat.add (Nat.mul 8 k) i)

@[expose] noncomputable def cmK (G H : Nat) : Bool := Nat.beq (pc G H) (pc H G)

@[expose] noncomputable def inR0K (Z : Nat) : Bool := Nat.beq Z W0 || Nat.beq Z W1 || Nat.beq Z W2

@[expose] noncomputable def nR0K (G GI : Nat) : Bool :=
  inR0K (pc G (pc W0 GI)) && inR0K (pc G (pc W1 GI))

theorem kBind : (Nat.beq (SuzMcG 0) (SuzTwG 0) && Nat.beq (SuzMcG 1) (SuzTwG 1) &&
    Nat.beq (SuzMcG 2) (SuzTwG 2) && Nat.beq (SuzMcG 3) (SuzTwG 3) &&
    Nat.beq (SuzMcG 4) (SuzTwG 4) && Nat.beq (SuzMcG 5) (L2EL.F 12) &&
    Nat.beq (SuzMcG 6) (SuzMGG 4) && Nat.beq (SuzMcG 7) (SuzTwG 6) &&
    Nat.beq (SuzMcGI 0) (SuzTwGI 0) && Nat.beq (SuzMcGI 1) (SuzTwGI 1) &&
    Nat.beq (SuzMcGI 2) (SuzTwGI 2) && Nat.beq (SuzMcGI 3) (SuzTwGI 3) &&
    Nat.beq (SuzMcGI 4) (SuzTwGI 4) && Nat.beq (SuzMcGI 5) (L2EI 12) &&
    Nat.beq (SuzMcGI 6) (SuzMGGI 4) && Nat.beq (SuzMcGI 7) (SuzTwGI 6)) = true := by
  quickRfl

theorem kPin : (Nat.beq W1 (pc RHO (pc W0 (SuzTwGI 2))) && Nat.beq W2 (pc W0 W1) &&
    Nat.beq (SuzMcE 0) (pc (CI 0) (pc S (CP 0))) && Nat.beq (SuzMcE 2) (pc (CI 2) (pc S (CP 2))) &&
    ie (SuzMcE 0) (SuzMcEI 0) && ie (SuzMcE 2) (SuzMcEI 2) && cn (SuzMcEI 0) && cn (SuzMcEI 2) &&
    Nat.beq X (wK xW) && ie X XI && cn XI) = true := by
  quickRfl

@[expose] noncomputable def pinD (dw : List (List Nat)) (k i : Nat) : Bool :=
  Nat.beq (wK (wget dw i)) (D k i)

theorem kD0a : allBlk 0 (pinD deltaW0 0) 6 = true := by quickRfl
theorem kD0b : allBlk 6 (pinD deltaW0 0) 5 = true := by quickRfl
theorem kD0c : allBlk 11 (pinD deltaW0 0) 5 = true := by quickRfl
theorem kD2a : allBlk 0 (pinD deltaW2 2) 6 = true := by quickRfl
theorem kD2b : allBlk 6 (pinD deltaW2 2) 5 = true := by quickRfl
theorem kD2c : allBlk 11 (pinD deltaW2 2) 5 = true := by quickRfl

@[expose] noncomputable def pinM (bw : List (List Nat)) (k j : Nat) : Bool :=
  Nat.beq (wK (wget bw j)) (M k j) && Nat.beq (Y k j) (pc (CPI k) (pc (M k j) (CP k))) &&
    ie (Y k j) (YI k j) && cn (YI k j)

theorem kM0a : allBlk 0 (pinM boundW0 0) 3 = true := by quickRfl
theorem kM0b : allBlk 3 (pinM boundW0 0) 2 = true := by quickRfl
theorem kM2a : allBlk 0 (pinM boundW2 2) 3 = true := by quickRfl
theorem kM2b : allBlk 3 (pinM boundW2 2) 3 = true := by quickRfl

theorem kM1 : (Nat.beq (M 0 1) T1 && Nat.beq (M 2 1) T1) = true := by quickRfl

theorem kComm : (cmK (SuzTwG 0) T1 && cmK (SuzTwG 0) RHO && cmK (SuzTwG 1) T1 &&
    cmK (SuzTwG 1) RHO && cmK (SuzTwG 3) RHO && nR0K (SuzTwG 3) (SuzTwGI 3) &&
    cmK (SuzTwG 4) RHO && nR0K (SuzTwG 4) (SuzTwGI 4)) = true := by
  quickRfl

@[expose] noncomputable def rH1 (i : Nat) : Bool := Nat.beq (wK (wget relsH1 i)) Idn

@[expose] noncomputable def rH2 (i : Nat) : Bool := Nat.beq (wK (wget relsH2 i)) Idn

@[expose] noncomputable def rA (i : Nat) : Bool :=
  Nat.beq (wK (pget relsA i).1) (wK (pget relsA i).2)

@[expose] noncomputable def rE (i : Nat) : Bool :=
  strictB (wK (pget edge i).1) fun U => cmK U P1 && Nat.beq (wK (pget edge i).2) (pc S (pc U SI))

theorem kH1a : allBlk 0 rH1 3 = true := by quickRfl
theorem kH1b : allBlk 3 rH1 3 = true := by quickRfl
theorem kH1c : (rH1 6 && Nat.beq (wK sq) (pc S S)) = true := by quickRfl
theorem kH2a : allBlk 0 rH2 5 = true := by quickRfl
theorem kH2b : allBlk 5 rH2 3 = true := by quickRfl
@[expose] noncomputable def kAF (i : Nat) : Bool := rA i

@[expose] noncomputable def kEF (i : Nat) : Bool := rE i

#kc_each_unfold kAF 0 8 as CertificateChecks.KernelSpor.SuzMcK.kA
#kc_each_unfold kEF 0 5 as CertificateChecks.KernelSpor.SuzMcK.kE

theorem kCell0 : (Nat.beq (wK cW0) (C 0) && Nat.beq (wK cpW0) (CP 0) &&
    Nat.beq (wK eW0) (SuzMcE 0) && Nat.beq (D 0 1) (pc T1 P1)) = true := by
  quickRfl

theorem kCell2 : (Nat.beq (wK cW2) (C 2) && Nat.beq (wK cpW2) (CP 2) &&
    Nat.beq (wK eW2) (SuzMcE 2) && Nat.beq (D 2 1) (pc T1 P1)) = true := by
  quickRfl

theorem kGen : (Nat.beq (wK kGenAW) (SuzRKG 0) && Nat.beq (wK kGenBW) (SuzRKG 1) &&
    Nat.beq (pc S (pc T1 SI)) P1 && Nat.beq (pc S (pc P1 SI)) T1) = true := by
  quickRfl

@[expose] noncomputable def chkM (k j : Nat) : Bool :=
  cmK (M k j) P1 && inR0K (pc (Y k j) (pc W0 (YI k j))) && inR0K (pc (Y k j) (pc W1 (YI k j))) &&
    cmK (pc (SuzMcE k) (pc (Y k j) (SuzMcEI k))) T1 && cmK (pc S (pc (M k j) SI)) T1

theorem kB0a : allBlk 0 (chkM 0) 3 = true := by quickRfl
theorem kB0b : allBlk 3 (chkM 0) 2 = true := by quickRfl
theorem kB2a : allBlk 0 (chkM 2) 3 = true := by quickRfl
theorem kB2b : allBlk 3 (chkM 2) 3 = true := by quickRfl

@[expose] noncomputable def kwK (W : Nat → Nat) (k nk i : Nat) : Bool :=
  strictB (SuzRKT i) fun t => strictB (W (Nat.add (Nat.mul 1728 k) i)) fun w =>
  bIf(Nat.beq (Nat.mod w 2) 1,
    strictB (Nat.div w 2) (fun d => bAnd(Nat.blt d 16, Nat.beq t (D k d))),
    strictB (Nat.mod (Nat.div w 2) 8) fun j => strictB (Nat.div w 16) fun x =>
      bAnd(Nat.blt j nk, bAnd(Nat.blt x 1782, SuzRKZ.movK t (M k j) x)))

theorem kScan0 : allN 3456 (kwK SuzMcKW 0 5) = true := by quickRfl
theorem kScan2 : allN 3456 (kwK SuzMcKW 2 6) = true := by quickRfl

theorem kRem : (cmK X W0 && cmK X W1 && Nat.beq (pc X (pc TAU XI)) (pc TAU T1) &&
    Nat.beq (pc X X) Idn) = true := by
  quickRfl

@[expose] noncomputable def vwK (W : Nat → Nat) (v : Nat) : Bool :=
  strictB (SuzC1EV.T v) fun t => strictB (W v) fun w =>
  bIf(Nat.beq (Nat.mod w 2) 1,
    strictB (Nat.div w 2) (fun x => bAnd(Nat.blt x 1782, SuzRKZ.movK t W1 x)),
    strictB (Nat.div w 2) (fun p => bAnd(Nat.blt p (SuzMcN 0), Nat.beq (SuzMcVC p) v)))

theorem kV : allN 512 (vwK SuzMcVW) = true := by quickRfl

@[expose] noncomputable def vcK (p : Nat) : Bool :=
  bIf(Nat.blt p (SuzMcN 0), cmK (SuzC1EV.T (SuzMcVC p)) X, true)

theorem kVN : Nat.ble (SuzMcN 0) 520 = true := by quickRfl

@[expose] noncomputable def kVCF (k : Nat) : Bool := allBlk (20 * k) vcK 20

#kc_each_unfold kVCF 0 26 as CertificateChecks.KernelSpor.SuzMcK.kVC

@[expose] noncomputable def badK (k n u : Nat) : Bool :=
  strictB (pc (C k) (pc X (CI k))) fun A => strictB (pc (CP k) (pc X (CPI k))) fun B =>
  strictB (pc SI (pc A S)) fun A' =>
    Nat.beq (pc A' (pc (D k n) B)) (nIf(Nat.beq u 0, Idn, pc T1 P1)) && cmK A P1 && cmK A' T1

theorem kBad0 : (badK 0 15 0 && badK 2 7 0) = true := by quickRfl
theorem kBad1 : (badK 0 8 1 && badK 2 8 1) = true := by quickRfl

theorem neg_scan : Bool.not (allN 3456 (kwK (fun _ => 1) 0 5)) = true := by quickRfl

theorem neg_wit : Bool.not (kwK (fun _ => 0) 0 5 0) = true := by quickRfl

theorem neg_v : Bool.not (allN 512 (vwK (fun _ => 2))) = true := by quickRfl

theorem neg_pin : Bool.not (Nat.beq (wK (wget boundW0 3)) (M 0 2)) = true := by quickRfl

theorem neg_comm : Bool.not (cmK X TAU) = true := by quickRfl

end CertificateChecks.KernelSpor.SuzMcK

end
