module

public import Certificates.Kernel.HSStd.PumpH39Data
public import Certificates.Kernel.HSStd.PumpU3Checks
public import Certificates.Data.Kernel.ConjOrb
public import Certificates.Kernel.LocalComp.L39Data
import CFSG.Certificates.Kernel.Common.Harness

set_option maxRecDepth 400000

public section

namespace CertificateChecks.KernelHSStd.PumpH39

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KC.BfsPin CertificateChecks.KernelLC.L39
open CFSG.EvenSporadicStandard.HSStd.PumpTC7
open CFSG.KC.LocalComp.ExcDeriv (fixCntK)

@[expose] def wsOf (j : Nat) : List (List Int) := ((exclTab.getD j none).map (·.1)).getD []

@[expose] noncomputable def repP (j : Nat) : Nat := LR.E (lget LR.OFF j)

@[expose] noncomputable def gensK (ws : List (List Int)) (ng : Nat) (G : Nat → Nat) : Bool :=
  Nat.beq ws.length ng &&
    allN ng (fun j => wordEqK 182 8 (mask 8) (pidn 182 8) LT.S LT.SI 7 (ws.getD j []) (G j)) &&
    allN ng (fun k => permOK 182 8 (mask 8) (182 * 8) (G k) (pinvS 182 8 (mask 8) (G k)))

@[expose] noncomputable def commK (ng : Nat) (G : Nat → Nat) (r : Nat) : Bool :=
  allN ng (fun j => Nat.beq (pcomp 182 8 (mask 8) (G j) r) (pcomp 182 8 (mask 8) r (G j)))

theorem gS2 : gensK s2Words S2.ng S2.G = true := by quickRfl
theorem gE0 : gensK (wsOf 0) E0.ng E0.G = true := by quickRfl
theorem gE1 : gensK (wsOf 1) E1.ng E1.G = true := by quickRfl
theorem gE3 : gensK (wsOf 3) E3.ng E3.G = true := by quickRfl
theorem gE5 : gensK (wsOf 5) E5.ng E5.G = true := by quickRfl
theorem gE7 : gensK (wsOf 7) E7.ng E7.G = true := by quickRfl
theorem gE9 : gensK (wsOf 9) E9.ng E9.G = true := by quickRfl
theorem gE10 : gensK (wsOf 10) E10.ng E10.G = true := by quickRfl

theorem nums : (Nat.beq S2.N 128 && Nat.beq E0.N 128 && Nat.beq E1.N 128 && Nat.beq E3.N 13 &&
    Nat.beq E5.N 13 && Nat.beq E7.N 128 && Nat.beq E9.N 7 && Nat.beq E10.N 7 &&
    Nat.beq X.ng 2 && Nat.beq X.N 7280 && Nat.beq PumpU3.U.N 729) = true := by quickRfl

theorem kS2 : keysSK 182 8 tKeys S2.N S2.T ((List.range 128).map S2K) = true := by quickRfl
theorem kE0 : keysSK 182 8 tKeys E0.N E0.T ((List.range 128).map E0K) = true := by quickRfl
theorem kE1 : keysSK 182 8 tKeys E1.N E1.T ((List.range 128).map E1K) = true := by quickRfl
theorem kE3 : keysSK 182 8 tKeys E3.N E3.T ((List.range 13).map E3K) = true := by quickRfl
theorem kE5 : keysSK 182 8 tKeys E5.N E5.T ((List.range 13).map E5K) = true := by quickRfl
theorem kE7 : keysSK 182 8 tKeys E7.N E7.T ((List.range 128).map E7K) = true := by quickRfl
theorem kE9 : keysSK 182 8 tKeys E9.N E9.T ((List.range 7).map E9K) = true := by quickRfl
theorem kE10 : keysSK 182 8 tKeys E10.N E10.T ((List.range 7).map E10K) = true := by quickRfl

theorem fixS2 : allN S2.N (fun i =>
    !Nat.beq (pcomp 182 8 (mask 8) (S2.T i) (S2.T i)) (pidn 182 8) ||
      Nat.beq (S2.T i) (pidn 182 8) || Nat.beq (fixCntK 8 (mask 8) (S2.T i) 182) 22) = true := by
  quickRfl

theorem gX : (Nat.beq (X.G 0) (LT.S 0) && Nat.beq (X.G 1) (LT.S 1) && Nat.blt X.r0 X.N &&
    wordEqK 182 8 (mask 8) (pidn 182 8) LT.S LT.SI 7 x1Word (X.T X.r0) &&
    permOK 182 8 (mask 8) (182 * 8) (X.T X.r0) (pinvS 182 8 (mask 8) (X.T X.r0))) = true := by
  quickRfl

theorem wU : allN PumpU3.U.N (fun i => !Nat.beq (fixCntK 8 (mask 8) (PumpU3.U.T i) 182) 20 ||
    (Nat.blt (XW i) X.N && Nat.beq (X.T (XW i)) (PumpU3.U.T i))) = true := by quickRfl

theorem cE : (allN 11 (fun j => permOK 182 8 (mask 8) (182 * 8) (repP j)
      (pinvS 182 8 (mask 8) (repP j))) &&
    commK E0.ng E0.G (repP 0) && commK E1.ng E1.G (repP 1) && commK E3.ng E3.G (repP 3) &&
    commK E5.ng E5.G (repP 5) && commK E7.ng E7.G (repP 7) && commK E9.ng E9.G (repP 9) &&
    commK E10.ng E10.G (repP 10)) = true := by quickRfl

theorem sX : allN X.N (fun i =>
    !Nat.beq (pcomp 182 8 (mask 8) (X.T i) (repP 2)) (pcomp 182 8 (mask 8) (repP 2) (X.T i)) &&
    !Nat.beq (pcomp 182 8 (mask 8) (X.T i) (repP 4)) (pcomp 182 8 (mask 8) (repP 4) (X.T i)) &&
    !Nat.beq (pcomp 182 8 (mask 8) (X.T i) (repP 6)) (pcomp 182 8 (mask 8) (repP 6) (X.T i)) &&
    !Nat.beq (pcomp 182 8 (mask 8) (X.T i) (repP 8)) (pcomp 182 8 (mask 8) (repP 8) (X.T i))) =
    true := by quickRfl

end CertificateChecks.KernelHSStd.PumpH39

end
