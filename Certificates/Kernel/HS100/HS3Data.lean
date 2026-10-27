module

public import Certificates.Kernel.LocalComp.BfsGen
public import Certificates.Kernel.Misc.Perm.HexCmd
public import Certificates.Kernel.SporSch.Th.GenV4
public import Certificates.Kernel.HS100.ChainData
public import Certificates.Data.Kernel.BfsPinBase
public import Certificates.Data.Kernel.Misc.ArrEnum
public import Certificates.Data.Kernel.Misc.ChainTail
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Wilson.ThetaSpor.HSThreeData
meta import CFSG.LocalAnalysis.AGLEmbeddingD2.Wilson.ThetaSpor.HSThreeData
meta import Certificates.Kernel.Sporadic.RawGen
import CFSG.Certificates.Kernel.Common.Harness

namespace CertificateChecks.KernelHS100.HS3E

open CFSG.AGLEmbeddingD2.Wilson.ThetaSpor

meta def all3 : Array (Array Nat) := #[hsX, hsC3] ++ hsGs ++ hsConjs.toArray

meta def gC : List (Array Nat) := hsGs.toList

meta def gP : List (Array Nat) := [hsX, hsC3]

meta def gF : List (Array Nat) := [hsR0, hsR1]

meta def keyOf (a : Array Nat) : Nat := [0, 1, 2, 3, 4].foldr (fun p acc => a[p]! + 100 * acc) 0

meta def keyOrder (gs : List (Array Nat)) : List Nat :=
  let pts := (CFSG.KC.BfsGen.search 100 7 gs.toArray).1
  ((Array.range pts.size).qsort fun a b => keyOf pts[a]! < keyOf pts[b]!).toList

meta def kC : List Nat := keyOrder gC
meta def kP : List Nat := keyOrder gP

meta def comp (t u : Array Nat) : Array Nat := u.map fun i => t[i]!

meta def inv (t : Array Nat) : Array Nat := Id.run do
  let mut r := Array.replicate t.size 0
  for i in [0:t.size] do
    r := r.set! t[i]! i
  return r

meta def wits : Array Nat :=
  let pts := (CFSG.KC.BfsGen.search 100 7 gP.toArray).1
  pts.map fun y =>
    ((List.range 8).find? fun j =>
      let g := hsConjs.toArray[j]!
      comp g (comp y (inv g)) == hsX).getD 0

meta def witsA : Array (Array Nat) := wits.map fun j => #[j]

meta def blkA : Array (Array Nat) := #[hsBlk]

meta def repA : Array (Array Nat) := #[hsRep]

end CertificateChecks.KernelHS100.HS3E

public section

set_option maxRecDepth 400000

#kmisc_packarrs CertificateChecks.KernelHS100.H3 CertificateChecks.KernelHS100.HS3E.all3 7
#lc_bfs CertificateChecks.KernelHS100.CC CertificateChecks.KernelHS100.HS3E.gC 100 7
#lc_bfs CertificateChecks.KernelHS100.PC CertificateChecks.KernelHS100.HS3E.gP 100 7
#lc_bfs CertificateChecks.KernelHS100.FC CertificateChecks.KernelHS100.HS3E.gF 5 3
#kss_natlist CertificateChecks.KernelHS100.CC.SKT CertificateChecks.KernelHS100.HS3E.kC
#kss_natlist CertificateChecks.KernelHS100.PC.SKT CertificateChecks.KernelHS100.HS3E.kP
#kmisc_packarrs CertificateChecks.KernelHS100.W3 CertificateChecks.KernelHS100.HS3E.witsA 4
#kmisc_packarrs CertificateChecks.KernelHS100.HB CertificateChecks.KernelHS100.HS3E.blkA 3
#kmisc_packarrs CertificateChecks.KernelHS100.HR CertificateChecks.KernelHS100.HS3E.repA 7

namespace CertificateChecks.KernelHS100

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KC.BfsPin CFSG.KC.Misc.ArrEnum CFSG.KC.Misc.ChainTail
open CFSG.AGLEmbeddingD2.Wilson.ThetaSpor CFSG.Monster.B.Co2.Native CFSG.Monster.B.Co2
open CFSG.Monster.B.Mathieu CFSG.RankThree.Native

@[expose] noncomputable def CC.SK : List Nat := (List.range 360).map CC.SKT

@[expose] noncomputable def PC.SK : List Nat := (List.range 9).map PC.SKT

theorem CC.keys : keysSK 100 7 [0, 1, 2, 3, 4] CC.N CC.T CC.SK = true := by quickRfl

theorem PC.keys : keysSK 100 7 [0, 1, 2, 3, 4] PC.N PC.T PC.SK = true := by quickRfl

theorem HS3.sizes : (Nat.beq CC.N 360 && Nat.beq PC.N 9 && Nat.beq FC.N 120) = true := by quickRfl

theorem HS3.bX : arrBind hsX 100 7 (H3 0) = true := by quickRfl

theorem HS3.bC3 : arrBind hsC3 100 7 (H3 1) = true := by quickRfl

theorem HS3.bGs : (allN 2 fun k => arrBind hsGs[k]! 100 7 (H3 (k + 2))) = true := by quickRfl

theorem HS3.bConjs : (allN 8 fun j => arrBind (hsConjs.getD j #[]) 100 7 (H3 (j + 4))) = true := by
  quickRfl

theorem HS3.perm : allN 12
    (fun j => permOK 100 7 (mask 7) (100 * 7) (H3 j) (pinvS 100 7 (mask 7) (H3 j))) = true := by
  quickRfl

theorem HS3.gensC : (allN 2 fun k => Nat.beq (CC.G k) (H3 (k + 2))) = true := by quickRfl

theorem HS3.gensP : (Nat.beq (PC.G 0) (H3 0) && Nat.beq (PC.G 1) (H3 1)) = true := by quickRfl

theorem HS3.bF : (arrBind hsR0 5 3 (FC.G 0) && arrBind hsR1 5 3 (FC.G 1)) = true := by quickRfl

theorem HS3.permF : allN 2
    (fun j => permOK 5 3 (mask 3) (5 * 3) (FC.G j) (pinvS 5 3 (mask 3) (FC.G j))) = true := by
  quickRfl

theorem HS3.sift : allN 12 (fun j => Nat.beq (Nat.shiftRight (H3 j) (100 * 7)) 0 &&
    allN 100 (fun t => Nat.blt (pg 7 (mask 7) (H3 j) t) 100) &&
    siftK 100 7 (mask 7) (100 * 7) (pidn 100 7) HC.LR HC.TRI HC.BP 5 0 (H3 j)) = true := by
  quickRfl

@[expose] noncomputable def pw100 (p e : ℕ) : ℕ := ppow 100 7 (mask 7) (pidn 100 7) p e

@[expose] noncomputable def br3 (k : ℕ) : Bool :=
  ptailBranchK 100 7 HC.LR HC.TR HC.BP (H3 0) (pw100 (H3 0)) hsRels 360 CC.T 5 k

theorem HS3.rc : Nat.beq (rcnt (HC.LR 0)) 100 = true := by quickRfl

theorem HS3.br : allN 100 br3 = true := by quickRfl

@[expose] noncomputable def conjK (p q : ℕ) : ℕ :=
  pcomp 100 7 (mask 7) p (pcomp 100 7 (mask 7) q (pinvS 100 7 (mask 7) p))

theorem HS3.conj : allN 9 (fun k => Nat.blt (W3 k) 8 && (Nat.beq (PC.T k) (pidn 100 7) ||
    Nat.beq (conjK (H3 (W3 k + 4)) (PC.T k)) (H3 0))) = true := by quickRfl

@[expose] noncomputable def ug (n w P x : ℕ) : ℕ := if x < n then pg w (mask w) P x else 0

theorem HS3.bBlk : (arrBind hsBlk 100 3 (HB 0) && arrBind hsRep 5 7 (HR 0)) = true := by quickRfl

@[expose] noncomputable def blkK (P : ℕ) : Bool :=
  allN 100 (fun p => !(hsF.contains p) || (hsF.contains (ug 100 7 P p) &&
      ug 100 3 (HB 0) (ug 100 7 P p) ==
        ug 100 3 (HB 0) (ug 100 7 P (ug 5 7 (HR 0) (ug 100 3 (HB 0) p))))) &&
    (!(allN 100 (fun p => !(hsF.contains p) || ug 100 3 (HB 0) (ug 100 7 P p) == ug 100 3 (HB 0) p))
      || Nat.beq (pw100 P 3) (pidn 100 7))

theorem HS3.blk : allN 360 (fun k => blkK (CC.T k)) = true := by quickRfl

theorem HS3.x3 : (Nat.beq (pw100 (H3 0) 3) (pidn 100 7) && !Nat.beq (H3 0) (pidn 100 7)) = true := by
  quickRfl

theorem HS3.comm : allN 2 (fun k => Nat.beq (pcomp 100 7 (mask 7) (H3 (k + 2)) (H3 0))
    (pcomp 100 7 (mask 7) (H3 0) (H3 (k + 2)))) = true := by quickRfl

theorem HS3.lit2 : (allN 100 (fun i => (ug 100 7 (H3 0) i == i) == hsF.contains i) &&
    allN 100 (fun i => if hsF.contains i then decide (ug 100 3 (HB 0) i < 5)
      else ug 100 3 (HB 0) i == 5) &&
    allN 5 (fun b => hsF.contains (ug 5 7 (HR 0) b) &&
      ug 100 3 (HB 0) (ug 5 7 (HR 0) b) == b)) = true := by quickRfl

theorem HS3.lit3 : (allN 5 (fun b => ug 100 3 (HB 0) (ug 100 7 (H3 2) (ug 5 7 (HR 0) b)) ==
      ug 5 3 (FC.G 0) b) &&
    allN 5 (fun b => ug 100 3 (HB 0) (ug 100 7 (H3 3) (ug 5 7 (HR 0) b)) ==
      ug 5 3 (FC.G 1) b)) = true := by quickRfl

end CertificateChecks.KernelHS100

end
