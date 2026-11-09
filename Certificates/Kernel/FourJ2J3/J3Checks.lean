module

public import Certificates.Kernel.FourJ2J3.J3Data
public import Certificates.Data.Kernel.FourJoinedK
public import Certificates.Data.Kernel.FourJBfsB
public import Certificates.Kernel.SporSch.PairJ3.Chain
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelFourJ.J3

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KC.BfsPin CFSG.KC.FourJ CFSG.KC.FourJB CertificateChecks.KernelFourJ
open CertificateChecks.KernelSporSch

@[expose] noncomputable def l4J : Nat → Nat := let4 (PJ3.S 0) (PJ3.S 1) (PJ3.SI 0) (PJ3.SI 1)

@[expose] noncomputable def actJ (k x : Nat) : Nat := chaseT 13 l4J J3D.SO J3D.SL k x

@[expose] noncomputable def ctJ (a x : Nat) : Nat := treeCh actJ J3D.BPAR J3D.BLAB J3D.N a x

@[expose] noncomputable def cgJ (t x : Nat) : Nat := chaseT 13 l4J J3D.IO J3D.IL t x

@[expose] noncomputable def czJ (k x : Nat) : Nat := chaseT 13 l4J J3D.NO J3D.NL k x

@[expose] noncomputable def cziJ (k x : Nat) : Nat := chaseT 13 l4J J3D.NO J3D.BZIL k x

@[expose] noncomputable def cuJ (t x : Nat) : Nat := chasePT (pmX J3D.nX czJ cziJ) J3D.UO J3D.UL t x

theorem nums : (Nat.beq J3D.N 128 && Nat.beq J3D.m 73) = true := by quickRfl

theorem letC : (canonK 6156 13 (mask 13) (6156 * 13) (PJ3.S 0) &&
    canonK 6156 13 (mask 13) (6156 * 13) (PJ3.S 1) &&
    canonK 6156 13 (mask 13) (6156 * 13) (PJ3.SI 0) &&
    canonK 6156 13 (mask 13) (6156 * 13) (PJ3.SI 1)) = true := by quickRfl

theorem letW : (wordEqK 6156 13 (mask 13) (pidn 6156 13) PJ3.S PJ3.SI 5 [1] (PJ3.S 0) &&
    wordEqK 6156 13 (mask 13) (pidn 6156 13) PJ3.S PJ3.SI 5 [2] (PJ3.S 1) &&
    wordEqK 6156 13 (mask 13) (pidn 6156 13) PJ3.S PJ3.SI 5 [-1] (PJ3.SI 0) &&
    wordEqK 6156 13 (mask 13) (pidn 6156 13) PJ3.S PJ3.SI 5 [-2] (PJ3.SI 1)) = true := by quickRfl

theorem letInv :invBK [0, 1, 3, 2, 5766] 5 (pg 13 (mask 13) (PJ3.S 0)) (pg 13 (mask 13) (PJ3.SI 0))
    (pg 13 (mask 13) (PJ3.S 1)) (pg 13 (mask 13) (PJ3.SI 1)) = true := by quickRfl

theorem bfsB : bfsBK [0, 1, 3, 2, 5766] 5 4 J3D.ng J3D.N actJ J3D.BPAR J3D.BLAB J3D.BPOS J3D.BIM
    J3D.BSRT = true := by quickRfl

theorem mt : mtBK J3D.N J3D.ng J3D.BPAR J3D.BLAB J3D.BPOS J3D.BMT = true := by quickRfl

theorem klein : kleinMK J3D.N J3D.m J3D.BMT J3D.PX J3D.PY J3D.PXY = true := by quickRfl

theorem tree : treeMK J3D.N J3D.m J3D.nBig J3D.BMT J3D.PX J3D.PY J3D.PAR = true := by quickRfl

theorem comp : compMK J3D.N J3D.m J3D.BMT J3D.PX J3D.PY J3D.PXY J3D.INV J3D.FM = true := by
  quickRfl

theorem iso : isoBK [0, 1, 3, 2, 5766] 5 J3D.BIM ctJ cgJ J3D.m J3D.nBig J3D.PX J3D.PY J3D.IJ =
    true := by quickRfl

theorem norm : normBK [0, 1, 3, 2, 5766] 5 J3D.BIM ctJ czJ cziJ J3D.N J3D.nBig J3D.nX J3D.BMT
    J3D.PX J3D.PY J3D.NJ J3D.NCX J3D.NCY = true := by quickRfl

theorem gen : genBK [0, 1, 3, 2, 5766] 5 (pg 13 (mask 13) (PJ3.S 0)) (pg 13 (mask 13) (PJ3.S 1))
    cuJ = true := by quickRfl

end CertificateChecks.KernelFourJ.J3

end
