module

public import Certificates.Kernel.HN25550.Data
public import Certificates.Kernel.HN25550.Enum
public import Certificates.Kernel.Sporadic.OddCore.HN2092C
public import Certificates.Data.Kernel.Spor.PNode
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CFSG.KD.HN25550

open CFSG.KC.Enum CFSG.KS CFSG.KS.Prim CFSG.KS.Raw CFSG.KS.PEnum CFSG.KS.PNode
open CertificateChecks.KernelSpor

@[expose] noncomputable def sGI (s : Nat) : Nat := pinvS 1100 11 (mask 11) (HSG s)

@[expose] noncomputable def inD (G : Nat) : Bool :=
  siftK 1100 11 (mask 11) (1100 * 11) (pidn 1100 11) HSD.LR HSD.TRI HSD.BP 4 0 G

@[expose] noncomputable def ckE (s : Nat) : Bool :=
  penumSlK 1100 11 (mask 11) (1100 * 11) false EP.G EP.G 4 EP.cnt EP.T EP.PL EP.POS EP.SRT EP.SRI
    (Nat.mul s (nat_lit 32)) (nat_lit 32)

@[expose] noncomputable def genK (i : Nat) (w : List Int) : Bool :=
  wordEqK 1100 11 (mask 11) (pidn 1100 11) HSG sGI 12 w (EP.G i)

theorem hd_ok : bAnd(Nat.beq EP.cnt 1024, bAnd(Nat.beq EP.k 4, bAnd(Nat.beq CNT 1024,
    bAnd(penumHdK (pidn 1100 11) EP.cnt 1024 EP.T EP.PL,
    bAnd(genK 0 [11], bAnd(genK 1 [3], bAnd(genK 2 [6, 2], genK 3 [2, 11, 2, 11, 6]))))))) =
    true := by
  quickRfl

theorem pw_ok : pWI = PW.map (fun w => w.map fun s => ((s + 1 : Nat) : Int)) ∧
    PW.all (fun w => w.all fun s => s ∈ G6S) ∧ G6S = [1, 2, 5, 10] ∧ SG.length = 12 ∧
    G6S.map (fun s => SG.getD s 0) = [0, 0, 1, 1] ∧
    PP = PW.map (fun w => (w.map fun s => SG.getD s 0).sum % 2) := by
  decide +kernel

theorem sift_ok : bAnd(inD (HSG 1), bAnd(inD (HSG 2),
    inD (pcomp 1100 11 (mask 11) (HSG 10) (sGI 5)))) = true := by
  quickRfl

theorem nodes_ok : bAnd(Nat.beq (CFSG.KC.Ord.lenL NW) 1024,
    nodesK 1100 11 (mask 11) EP.T EP.PL PP INV NW 0) = true := by
  quickRfl

theorem inv_ok : sqPathsK EP.PL PR INV IREL = true := by
  quickRfl

theorem s2_ok : bAnd(Nat.blt S2N 1024, bAnd(Nat.beq (parK PP (pathK EP.PL S2N S2N)) 0,
    eqLK S2W (List.append (pathCodes EP.PL PR S2N)
      (List.append (pathCodes EP.PL PR S2N) [0])))) = true := by
  quickRfl

end CFSG.KD.HN25550

end
