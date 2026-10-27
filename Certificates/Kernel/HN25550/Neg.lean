module

public import Certificates.Kernel.HN25550.Checks
public import Certificates.Data.Kernel.HNMultK
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CFSG.KD.HN25550

open CFSG.KC.Enum CFSG.KS CFSG.KS.Prim CFSG.KS.PEnum CFSG.KS.PNode CFSG.KC.HNMult
open CertificateChecks.KernelSpor

theorem neg_enum : Bool.not (penumSlK 1100 11 (mask 11) (1100 * 11) false (fun _ => EP.G 0)
    (fun _ => EP.G 0) 4 EP.cnt EP.T EP.PL EP.POS EP.SRT EP.SRI 0 32) = true := by quickRfl

theorem neg_gen : Bool.not (genK 0 [3]) = true := by quickRfl

theorem neg_sift : Bool.not (inD (HSG 10)) = true := by quickRfl

theorem neg_par : Bool.not (nodesK 1100 11 (mask 11) EP.T EP.PL [0, 0, 1, 1] INV NW 0) = true := by
  quickRfl

theorem neg_inv : Bool.not (nodesK 1100 11 (mask 11) EP.T EP.PL PP INV.tail NW 0) = true := by
  quickRfl

theorem neg_wit : Bool.not (nodesK 1100 11 (mask 11) EP.T EP.PL PP INV
    (NW.map fun x => nIf(Nat.beq x 0, 0, 1101)) 0) = true := by quickRfl

theorem neg_irel : Bool.not (sqPathsK EP.PL PR INV IREL.tail) = true := by quickRfl

theorem neg_rel : Bool.not (relW RB mul 46 CFSG.KD.OrdHN.ONE (List.append (IREL.headD []) [1])) =
    true := by quickRfl

theorem neg_s2rel : Bool.not (relW RB mul 46 CFSG.KD.OrdHN.ONE S2W.dropLast) = true := by quickRfl

theorem neg_s2 : Bool.not (Nat.beq (parK PP (pathK EP.PL (INV.headD 0) (INV.headD 0))) 0) = true := by
  quickRfl

end CFSG.KD.HN25550

end
