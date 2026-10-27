module

public import Certificates.Kernel.MaxD2.HSU35E.Data
public import Certificates.Kernel.MaxD2.HSW0.Data
public import Certificates.Kernel.MaxD2.HSP.Enum
public import Certificates.Kernel.MaxD2.HSP.Data
public import Certificates.Kernel.MaxD2.HSOver.Data
public import Certificates.Kernel.MaxD2.HSU.Enum
public import Certificates.Kernel.MaxD2.HSU.Data
public import Certificates.Data.Kernel.MaxD2.Block
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelMaxD2.HSU35E

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KS.MaxD2 CFSG.KS.PEnum CFSG.KS.Row

@[expose] noncomputable def zz : Nat := HSU.RE.T (r32 HSU.ZP 1)

@[expose] noncomputable def blkK : Bool :=
  blockK 100 7 OM (HSU.GP 0) 0 && (blockK 100 7 OM (HSU.GP 1) 0 &&
  blockK 100 7 OM (HSP.NE.G 2) 1)

@[expose] noncomputable def cuQ (g gi k : Nat) : Nat :=
  pcomp 100 7 (mask 7) (pcomp 100 7 (mask 7) (pcomp 100 7 (mask 7)
    (pcomp 100 7 (mask 7) g (HSU.RE.T k)) (HSU.TT 0)) gi) (HSU.TT 1)

@[expose] noncomputable def cuK (g gi : Nat) : Bool :=
  allN HSU.RE.cnt fun k => bIf(Nat.beq (pw 100 7 (cuQ g gi k) 5) (pidn 100 7), false, true)

@[expose] noncomputable def mvK (REP REPI : Nat → Nat) (r : Nat) : Bool :=
  bIf(Nat.beq zz (pidn 100 7), false, true) &&
    allN r fun i => movesK 100 7 4 (REP (Nat.succ i)) (REPI (Nat.succ i)) zz

theorem ch19850_om : (rowBitK 100 OM && Nat.beq (r32 OM 0) 1) = true := by quickRfl
theorem ch19850_blk : blkK = true := by quickRfl
theorem ch19850_cu : cuK (HSU.REP 1) (HSU.REPI 1) = true := by quickRfl
theorem ch19831_mv : mvK HSP.REP HSP.REPI 19 = true := by quickRfl
theorem ch19832_mv : mvK HSOver.REP HSOver.REPI 14 = true := by quickRfl

end CertificateChecks.KernelMaxD2.HSU35E

end
