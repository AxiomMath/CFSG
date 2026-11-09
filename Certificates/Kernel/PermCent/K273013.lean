module

public import CFSG.GH74.KGroups.L33Inputs
public import Certificates.Data.Kernel.PermCent.CV
import CFSG.Certificates.Kernel.Common.Each
import CFSG.Certificates.Kernel.Common.IdxChunks

public section

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace CertificateChecks.KernelPermCent

open CFSG.GH74.KGroups.L33 CFSG.Certificates.Kernel.PkCV

@[expose] noncomputable def k273013B (j : Nat) : Bool :=
  (((elemsC QA).drop (j * 1404)).take 1404).all fun g =>
    !(orderIsP g 26 [2, 13]) && !(orderIsP g 39 [3, 13])

#kc_each k273013B 0 8

theorem k273013 :
    (elemsC QA).all (fun g => !(orderIsP g 26 [2, 13]) && !(orderIsP g 39 [3, 13])) = true := by
  refine CFSG.KC.IdxChunks.all_chunks_of _ 1404 8 _ (by decide +kernel) fun j hj => ?_
  match j, hj with
  | 0, _ => exact k273013B0
  | 1, _ => exact k273013B1
  | 2, _ => exact k273013B2
  | 3, _ => exact k273013B3
  | 4, _ => exact k273013B4
  | 5, _ => exact k273013B5
  | 6, _ => exact k273013B6
  | 7, _ => exact k273013B7
  | k + 8, h => exact absurd h (by omega)

end CertificateChecks.KernelPermCent
