module

public import Certificates.Kernel.S63K.IData
public import Certificates.Kernel.S63K.HBind
public import Certificates.Data.Kernel.S63K.ConjTree
public import Certificates.Data.Kernel.SporSch.Co1Bfs
public import Certificates.Data.D4HexLinkCheck
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelS63.LK

open CFSG.KC.S63K CFSG.KC.Enum CFSG.KS CFSG.KS.SporSch.M24 CertificateChecks.KernelS63

@[expose] noncomputable def PAR (i : Nat) : Nat := Nat.div (ID.ZQ i) 8
@[expose] noncomputable def LAB (i : Nat) : Nat := Nat.mod (ID.ZQ i) 8
@[expose] noncomputable def W (n : Nat) : Nat := HD.im (Nat.mod n 8) (Nat.div n 8)

@[expose] noncomputable def fixF (j : Nat) : Bool :=
  CFSG.D4Hex.sortKey (HD.im j 0) (HD.im j 1) (HD.im j 5) == CFSG.D4Hex.lineKey 0 1 5

@[expose] noncomputable def flagF : Bool :=
  (allN 8 fun j => HD.im j 0 == 0 || fixF j) && [0, 1, 2, 6].all fun j => HD.im j 0 == 0 && fixF j

theorem zbfs : bfsK (cjStepK ID.G) ID.ZP PAR LAB W ID.ZS 8 (819 + 1) 819 (ID.ZP 0) = true := by
  quickRfl

theorem base : bAnd(Nat.beq (HD.lp 0 1) 1, Nat.beq (HD.lp 0 2) 5) = true := by quickRfl

theorem flag : flagF = true := by quickRfl

theorem neg : bAnd(bIf(Nat.beq (bfsRunK (cjStepK ID.G) ID.ZP PAR LAB (fun n => W (n + 1)) 8 820 820
      0 1) 819, false, true),
    bAnd(bIf(Nat.beq (bfsRunK (cjStepK ID.G) ID.ZP (fun i => PAR i + 1) LAB W 8 820 820 0 1) 819,
      false, true),
    bIf(CFSG.D4Hex.sortKey (HD.im 0 0) (HD.im 0 1) (HD.im 0 5) == CFSG.D4Hex.lineKey 0 1 6, false,
      true))) = true := by
  quickRfl

end CertificateChecks.KernelS63.LK

end
