module

public import Certificates.Kernel.LocalComp.BfsGen
public import Certificates.Kernel.Misc.Perm.HexCmd
public import Certificates.Kernel.SporSch.Th.GenV4
public import Certificates.Kernel.HS100.ChainData
public import Certificates.Data.Kernel.BfsPinBase
public import Certificates.Data.Kernel.Misc.ArrEnum
public import Certificates.Data.Kernel.WordArrK
public import Certificates.Data.GrSLitL34FactsFourCubeWit
meta import Certificates.Data.GrSLitL34FactsFourCubeWit
meta import Certificates.Kernel.Sporadic.RawGen
import CFSG.Certificates.Kernel.Common.Harness

namespace CertificateChecks.KernelHS100.CubeE

open CFSG.ComponentClassification.GrSLit.L34Facts.FourCube

meta def keyOf (n : Nat) (ps : List Nat) (a : Array Nat) : Nat :=
  ps.foldr (fun p acc => a[p]! + n * acc) 0

meta def keyOrder (n w : Nat) (ps : List Nat) (gs : List (Array Nat)) : List Nat :=
  let pts := (CFSG.KC.BfsGen.search n w gs.toArray).1
  ((Array.range pts.size).qsort fun a b => keyOf n ps pts[a]! < keyOf n ps pts[b]!).toList

meta def gHA : Array (Array Nat) := hsWit
meta def gTA : Array (Array Nat) := t32Gens
meta def gH : List (Array Nat) := hsWit.toList
meta def gO : List (Array Nat) := onWit.toList
meta def kH : List Nat := keyOrder 100 7 [0, 1, 2, 3, 4] gH
meta def kO : List Nat := keyOrder 32 6 [0, 5, 1] gO

end CertificateChecks.KernelHS100.CubeE

public section

set_option maxRecDepth 400000

#kmisc_packarrs CertificateChecks.KernelHS100.QW CertificateChecks.KernelHS100.CubeE.gHA 7
#kmisc_packarrs CertificateChecks.KernelHS100.QT CertificateChecks.KernelHS100.CubeE.gTA 6
#lc_bfs CertificateChecks.KernelHS100.QH CertificateChecks.KernelHS100.CubeE.gH 100 7
#lc_bfs CertificateChecks.KernelHS100.QO CertificateChecks.KernelHS100.CubeE.gO 32 6
#kss_natlist CertificateChecks.KernelHS100.QH.SKT CertificateChecks.KernelHS100.CubeE.kH
#kss_natlist CertificateChecks.KernelHS100.QO.SKT CertificateChecks.KernelHS100.CubeE.kO

namespace CertificateChecks.KernelHS100

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KC.BfsPin CFSG.KC.Misc.ArrEnum CFSG.KC.WordArr
open CFSG.ComponentClassification.GrSLit.L34Facts.FourCube

@[expose] noncomputable def QH.SK : List Nat := (List.range 512).map QH.SKT

@[expose] noncomputable def QO.SK : List Nat := (List.range 512).map QO.SKT

theorem QH.keys : keysSK 100 7 [0, 1, 2, 3, 4] QH.N QH.T QH.SK = true := by quickRfl

theorem QO.keys : keysSK 32 6 [0, 5, 1] QO.N QO.T QO.SK = true := by quickRfl

theorem Cube.sizes : (Nat.beq QH.N 512 && Nat.beq QO.N 512) = true := by quickRfl

theorem Cube.bW : (allN 5 fun k => arrBind hsWit[k]! 100 7 (QW k)) = true := by quickRfl

theorem Cube.bT : (allN 6 fun k => arrBind t32Gens[k]! 32 6 (QT k)) = true := by quickRfl

theorem Cube.permW : allN 5
    (fun j => permOK 100 7 (mask 7) (100 * 7) (QW j) (pinvS 100 7 (mask 7) (QW j))) = true := by
  quickRfl

theorem Cube.permT : allN 6
    (fun j => permOK 32 6 (mask 6) (32 * 6) (QT j) (pinvS 32 6 (mask 6) (QT j))) = true := by
  quickRfl

theorem Cube.gensH : (allN 5 fun k => Nat.beq (QH.G k) (QW k)) = true := by quickRfl

theorem Cube.gensO : (allN 5 fun k =>
    Nat.beq (QO.G k) (wordFK 32 6 QT (onWitWords.getD k []))) = true := by quickRfl

theorem Cube.sift : allN 5 (fun j => Nat.beq (Nat.shiftRight (QW j) (100 * 7)) 0 &&
    allN 100 (fun t => Nat.blt (pg 7 (mask 7) (QW j) t) 100) &&
    siftK 100 7 (mask 7) (100 * 7) (pidn 100 7) HC.LR HC.TRI HC.BP 5 0 (QW j)) = true := by
  quickRfl

theorem Cube.relsH : (qRels 0).all (fun wd => Nat.beq (wordFK 100 7 QW wd) (pidn 100 7)) = true := by
  quickRfl

theorem Cube.relsO : (qRels d1).all (fun wd => Nat.beq (wordFK 32 6 QO.G wd) (pidn 32 6)) =
    true := by
  quickRfl

end CertificateChecks.KernelHS100

end
