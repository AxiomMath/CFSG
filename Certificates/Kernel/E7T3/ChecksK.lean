module

public import Certificates.Data.Kernel.E7T3.Defs
public import Certificates.Kernel.E7T3.Data
import CFSG.Certificates.Kernel.Common.EachTrue
import CFSG.Certificates.Kernel.Common.ForallChunks

public section

namespace CertificateChecks.KernelE7T3K

open CFSG.RankThree.PartOne.KE CFSG.RankThree.Lattice CFSG.Blueprint.Chevalley CFSG.KC.E7T3
  CFSG.KD.E7T3

set_option maxRecDepth 100000

#kc_each CertificateChecks.KernelE7T3K ch14976kG
  (fun i => goodK s0 s1 s2 s3 roots (e7T3Certs.getD i default) (rl.getD i [])) 0 78

#kc_forall_chunks ch14976k_good
  (fun i => goodK s0 s1 s2 s3 roots (e7T3Certs.getD i default) (rl.getD i []) = true) 78
  CertificateChecks.KernelE7T3K.ch14976kG 1

#kc_each CertificateChecks.KernelE7T3K ch14976kR (fun _ => rootsK roots) 0 1

#kc_each CertificateChecks.KernelE7T3K ch14976kD
  (fun _ => (roots.map fun q => decL (loK q)) == Tag.E7.artifactRoots) 0 1

#kc_each CertificateChecks.KernelE7T3K ch14976kS
  (fun _ => s0.map decL == e7StdRoots (e7T3Nodes 0) && s1.map decL == e7StdRoots (e7T3Nodes 1) &&
    s2.map decL == e7StdRoots (e7T3Nodes 2) && s3.map decL == e7StdRoots (e7T3Nodes 3) &&
    validK s0 && validK s1 && validK s2 && validK s3) 0 1

#kc_each CertificateChecks.KernelE7T3K ch14976kF
  (fun j => allNK j fun i => flatK (ecross (e7T3G i) (e7T3G j))) 0 21

#kc_forall_chunks ch14976k_flats
  (fun j => (allNK j fun i => flatK (ecross (e7T3G i) (e7T3G j))) = true) 21
  CertificateChecks.KernelE7T3K.ch14976kF 1

theorem ch14976k_len : e7T3Certs.length = 78 ∧ rl.length = 78 := by decide +kernel

theorem ch14976k_det : CFSG.LieType.Chevalley.laplaceDet 7
    (toMat 7 (lcols 7 e7T3ColsList)) = 1 := by decide +kernel

theorem ch14976k_inv : lmul 7 (lcols 7 e7T3ColsList) e7T3BinvList = lid 7 := by decide +kernel

theorem ch14976k_fix : lmulVec 7 e7T3WList e7T3FList = e7T3FList := by decide +kernel

theorem ch14976k_rows : RowsOK (fun i : Fin 21 => e7T3G i) := by decide +kernel

theorem ch14976k_cover : ∀ l ∈ Tag.E7.artifactRoots, ∃ i : Fin 21, RowIs l i := by decide +kernel

theorem ch14976k_singles : ∀ k : Fin 21, ∃ c ∈ e7T3Certs, c.cls = [k.val] := by decide +kernel

theorem ch14976k_negD4 : ∀ c ∈ e7T3Certs, ∀ cm ∈ c.comps, cm.kind = 2 →
    ∀ l ∈ e7StdRoots (e7T3Nodes 2),
      lmulVec 7 (e7wl (e7T3NegD4 ++ cm.u)) (e7T3Perm 2 cm.rot l) =
        vneg 7 (lmulVec 7 (e7wl cm.u) (e7T3Perm 2 cm.rot l)) := by decide +kernel

theorem ch14976k_kinds : ∀ c ∈ e7T3Certs, c.comps.map E7T3Comp.kind ∈
    ([[0], [1], [2], [3], [0, 1]] : List (List ℕ)) := by decide +kernel

theorem ch14976k_e0 : ∀ c ∈ e7T3Certs, c.comps.map E7T3Comp.kind = [1] →
    [1, 0, 0, 0, 0, 0, 0] ∉ c.rootList := by decide +kernel

theorem ch14976k_size : ∀ c ∈ e7T3Certs, c.rootList.length ≤ 30 := by decide +kernel

theorem ch14976k_n1 :
    goodK s0 s1 s2 s3 roots (e7T3Certs.getD 0 default) (rl.getD 1 []) = false := by
  decide +kernel

theorem ch14976k_n2 : decide (CFSG.LieType.Chevalley.laplaceDet 7
    (toMat 7 (lcols 7 e7T3ColsList)) = -1) = false := by decide +kernel

theorem ch14976k_n3 : decide ((e7T3Certs.getD 0 default).cls = [1]) = false := by decide +kernel

end CertificateChecks.KernelE7T3K

end
