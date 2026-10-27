module

public import Certificates.Data.Kernel.O8.Lin434
public import Certificates.Kernel.OmegaEight.SA3002K
public import Certificates.Kernel.O8Minus434.Base
public meta import Certificates.Data.Item434OmegaMinus
public meta import Certificates.Kernel.Sporadic.RawGen
public meta import Certificates.Kernel.O8Minus434.Base
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelO8M434

open CFSG.KC.Enum CFSG.KC.O8 CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CertificateChecks.KernelO8
open CFSG.RankThree.PartTwo.Sec4.Item434OmegaMinus

@[expose] noncomputable def ZK (i : Nat) : Nat := linK NSM NIM (zCols.getD i [])

@[expose] noncomputable def TK : Nat := linK NSM NIM tCols

@[expose] noncomputable def SK (k : Nat) : Nat := linK NSM NIM (sCols.getD k [])

@[expose] noncomputable def vK (a b c : Nat) : Nat :=
  pcM (pcM (ppwM (ZK 0) a) (ppwM (ZK 1) b)) (ppwM (ZK 2) c)

@[expose] def allCols : List (List Nat) := tCols :: (zCols ++ sCols)

@[expose] noncomputable def eltK (c : List Nat) : Bool :=
  bAnd(cnM (linK NSM NIM c), bAnd(pmM (linK NSM NIM c), bAnd(cnM (pinvM (linK NSM NIM c)),
    siftK 136 8 (mask 8) (136 * 8) (pidn 136 8) OmM.LR OmM.TRI OmM.BP 7 0 (linK NSM NIM c))))

theorem kLin : List.all allCols (linLtK NSM) = true := by quickRfl

theorem kElt : List.all allCols eltK = true := by quickRfl

theorem kPow : allN 3 (fun i => allN 3 fun a => cnM (ppwM (ZK i) a)) = true := by quickRfl

theorem kWreath : bAnd(allN 3 (fun i => Nat.beq (ppwM (ZK i) 3) pidM),
    bAnd(allN 3 (fun i => allN 3 fun j => Nat.beq (pcM (ZK i) (ZK j)) (pcM (ZK j) (ZK i))),
    bAnd(Nat.beq (ppwM TK 3) pidM,
    bAnd(allN 3 (fun i => Nat.beq (cjM TK (ZK i)) (ZK (Nat.mod (Nat.add i 1) 3))),
    allN 3 (fun a => allN 3 fun b => allN 3 fun c =>
      bAnd(bIf(Nat.beq (Nat.add a (Nat.add b c)) 0, true, bIf(Nat.beq (vK a b c) pidM, false, true)),
        bIf(Nat.beq (vK a b c) TK, false, true))))))) = true := by
  quickRfl

theorem kCent : bAnd(allN 3 (fun k => Nat.beq (ppwM (SK k) 5) pidM),
    allN 3 (fun k => allN 3 fun i =>
      bIf(Nat.beq i k, true, Nat.beq (pcM (SK k) (ZK i)) (pcM (ZK i) (SK k))))) = true := by
  quickRfl

end CertificateChecks.KernelO8M434

#ks_rawchain CertificateChecks.KernelO8M434.G 136 8 17 CFSG.RankThree.PartTwo.Sec4.Item434OmegaMinus.genS
  CertificateChecks.KernelO8M434.genBaseA 3 CFSG.RankThree.PartTwo.Sec4.Item434OmegaMinus.genWords

namespace CertificateChecks.KernelO8M434

open CFSG.KC.Enum

theorem kGenS : allN 3 (fun j => Nat.beq (G.S j) (SK j)) = true := by quickRfl

end CertificateChecks.KernelO8M434

end
