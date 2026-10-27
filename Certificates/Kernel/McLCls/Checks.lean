module

public import Certificates.Kernel.McLCls.Tabs
public import Certificates.Kernel.Census.McLChain
public import Certificates.Data.Kernel.McLCls
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelMcLCls

open CFSG.KC.Enum CFSG.KS CFSG.KS.Prim CFSG.KC.M305 CertificateChecks.KernelLC.McLC

@[expose] noncomputable def hL (j : Nat) : Nat := Nat.rec (motive := fun _ => Nat) (MC.F 5)
  (fun _ _ => MC.F 6) j

@[expose] noncomputable def mL (j : Nat) : Nat := Nat.rec (motive := fun _ => Nat) (CT.F 4)
  (fun _ _ => CT.F 5) j

@[expose] noncomputable def bs : List Nat := [MC.F 4, CT.F 0, CT.F 1, CT.F 2]

@[expose] def hWd : List (List Nat) := [[1, 1, 1, 1, 1, 1, 1],
  [1, 0, 1, 0, 1, 1, 1, 0, 1, 1, 0, 1, 1, 0, 1, 1, 1, 1, 1, 1, 0],
  [0, 1, 1, 0, 1, 1, 1, 0, 1, 1, 0, 1],
  [1, 1, 1, 1, 1, 1, 0, 1, 1, 1, 1, 0, 1, 1, 1, 0, 1],
  [0, 1, 1, 1, 1, 1, 0, 1, 1, 0, 1, 1, 0, 1, 1, 1, 0, 1, 0, 1, 0, 1, 0],
  [1, 1, 1, 1, 0, 1, 1, 1, 1, 0, 1, 0, 1, 1, 1, 0, 1, 0],
  [1, 1, 1, 1, 1, 0, 1, 1, 0, 1, 1, 0, 1, 1, 0, 1, 1, 0, 1, 1, 1, 0, 1, 0]]

@[expose] noncomputable def hTb : List Nat := [MC.F 4, CT.F 0, CT.F 1, CT.F 2, CT.F 6, CT.F 7,
  CT.F 8]

@[expose] def oWd : List (List Nat) := [[], [1], [0, 1], [1, 1], [1, 0, 1], [0, 1, 1], [1, 1, 1],
  [1, 1, 0, 1], [1, 1, 1, 1], [1, 1, 1, 0, 1], [1, 1, 1, 1, 1], [1, 1, 1, 1, 0, 1],
  [0, 1, 1, 1, 1, 1], [1, 1, 1, 1, 1, 1], [1, 0, 1, 1, 1, 1, 1]]

@[expose] def mWd : List (List Nat) := [[1, 1, 0, 0, 0, 0, 1, 1, 0, 1, 0, 1, 0, 1, 1],
  [0, 1, 1, 0, 0, 1, 1, 0, 0, 1, 1, 0, 0, 1, 1, 0], [0, 0, 0, 0, 0, 0, 0],
  [1, 1, 1, 0, 0, 0, 0, 1, 1, 0, 1, 0, 1, 0, 1]]

@[expose] def nrmC : List (List Nat) := [[15, 14, 4, 7], [8, 2, 12, 7]]

@[expose] def oS : List Nat := [0, 26, 208, 213, 227, 260, 270]

@[expose] def xWd : List (List Nat) := [[1, 1, 1, 1, 0], [1, 1], [1, 0, 1, 0, 1, 0, 1, 0, 1, 0],
  [0, 1, 0, 1, 0, 1, 0, 1, 0, 1]]

@[expose] def nthW (L : List (List Nat)) (i : Nat) : List Nat :=
  (List.rec (motive := fun _ => Nat → List Nat) (fun _ => [])
    (fun x _ ih j => Nat.rec (motive := fun _ => List Nat) x (fun j' _ => ih j') j) L) i

@[expose] noncomputable def pOK (p q : Nat) : Bool :=
  bAnd(canonK 275 9 (mask 9) (275 * 9) p, bAnd(canonK 275 9 (mask 9) (275 * 9) q,
    invEqK 275 9 (mask 9) (275 * 9) p q))

theorem perms : bAnd(allN 9 (fun k => pOK (CT.F k) (CI k)), bAnd(pOK (MC.F 0) (MI 0),
    bAnd(pOK (MC.F 4) (MI 1), bAnd(pOK (MC.F 5) (MI 2), pOK (MC.F 6) (MI 3))))) = true := by
  quickRfl

@[expose] noncomputable def siftC (X : Nat) : Bool :=
  CFSG.KS.Raw.siftK 275 9 (mask 9) (275 * 9) (pidn 275 9) CertificateChecks.KernelCensus.McLC.LR
    CertificateChecks.KernelCensus.McLC.TRI CertificateChecks.KernelCensus.McLC.BP 5 0 X

theorem sift0 : siftC (CT.F 3) = true := by
  quickRfl

theorem sift1 : siftC (CT.F 4) = true := by
  quickRfl

theorem sift2 : siftC (CT.F 5) = true := by
  quickRfl

theorem basis : m305basis bs = true := by
  quickRfl

theorem fix : m305fix bs (m305mask CFSG.SectionRank.QTK.Insp443.McLCls.oPts) = true := by
  quickRfl

theorem hWords : m305words hL hWd hTb = true := by
  quickRfl

theorem orbO : m305dist (oWd.map fun wd => m305img oS (m305word hL wd)) = true := by
  quickRfl

theorem mWords : m305words mL mWd bs = true := by
  quickRfl

theorem nrm : bAnd(m305nrm bs (CT.F 4) (nthW nrmC 0), bAnd(m305nrm bs (CT.F 5) (nthW nrmC 1),
    bIf(Nat.beq (m305mul (CT.F 4) (MC.F 4)) (m305mul (MC.F 4) (CT.F 4)), false, true))) = true := by
  quickRfl

end CertificateChecks.KernelMcLCls

end
