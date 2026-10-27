module

public import Certificates.Kernel.HNFFib.Facts
public import Certificates.Kernel.HNFO4.Chk0
public import Certificates.Kernel.HNFO4.Chk1
public import Certificates.Kernel.HNFO4.Chk2
public import Certificates.Kernel.HNFO4.Chk3
public import Certificates.Kernel.HNFO4.Chk4
public import Certificates.Kernel.HNFO4.Chk5
public import Certificates.Kernel.HNFO4.Chk6
public import Certificates.Kernel.HNFO4.Chk7
public import Certificates.Kernel.HNFO4.Chk8
public import Certificates.Kernel.HNFO4.Dist
public import CFSG.Certificates.Kernel.HNFDfsSound
public import CFSG.LocalAnalysis.EvenSporadicStandard.Solomon78.HNFOrb
import CFSG.Certificates.Kernel.Common.ForallTree
import CFSG.Certificates.Kernel.Fam.HNSeed.Checks.K

public section

namespace CertificateChecks.KernelHNFO4

open CFSG.EvenSporadicStandard.Solomon78

#kc_forall_tree walks (fun i => CFSG.KD.HNFO4.chkW hnfW1 hnfW2 hnfRepWords[4]! i = true) 69
  CFSG.KD.HNFO4.c

open CFSG.Sporadic.HNSchreier CFSG.KC.HNF26720 CFSG.KC.HNF26729 CFSG.KS.HNF26729 CFSG.KS.HNFFib
open CFSG.KS.HNLocal CertificateChecks.KernelHNF26720 CertificateChecks.KernelHNF26729
open CertificateChecks.KernelHNFFib

theorem bound4 : 35200 ≤ (conjOrb hnfC0 (hnfRep hnfRepWords[4]!)).ncard := by
  have hfin : Finite ↥JH := Finite.of_injective ρJ ρJ_injective
  have cBi' : CFSG.KS.Ord.Canon 5 133 13 CFSG.KD.HNF26729.Bi := cBi
  exact CFSG.KS.HNFDfs.dfs_sound CFSG.KD.FamHNSeed.consts cA cB cBi' walks CFSG.KD.HNFO4.dist ρJ
    hnfC0 _ (ρ_rep (by norm_num)) fun w hw => ⟨_, mem_C0 hw, ρ_stab w hw, ρ_gen_inv hw⟩

end CertificateChecks.KernelHNFO4

end
