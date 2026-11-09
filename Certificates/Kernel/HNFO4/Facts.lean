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
public import Certificates.Kernel.HNFO4.Chk9
public import Certificates.Kernel.HNFO4.Chk10
public import Certificates.Kernel.HNFO4.Chk11
public import Certificates.Kernel.HNFO4.Chk12
public import Certificates.Kernel.HNFO4.Chk13
public import Certificates.Kernel.HNFO4.Chk14
public import Certificates.Kernel.HNFO4.Chk15
public import Certificates.Kernel.HNFO4.Chk16
public import Certificates.Kernel.HNFO4.Chk17
public import Certificates.Kernel.HNFO4.Chk18
public import Certificates.Kernel.HNFO4.Chk19
public import Certificates.Kernel.HNFO4.Chk20
public import Certificates.Kernel.HNFO4.Chk21
public import Certificates.Kernel.HNFO4.Chk22
public import Certificates.Kernel.HNFO4.Chk23
public import Certificates.Kernel.HNFO4.Chk24
public import Certificates.Kernel.HNFO4.Chk25
public import Certificates.Kernel.HNFO4.Chk26
public import Certificates.Kernel.HNFO4.Chk27
public import Certificates.Kernel.HNFO4.Chk28
public import Certificates.Kernel.HNFO4.Chk29
public import Certificates.Kernel.HNFO4.Chk30
public import Certificates.Kernel.HNFO4.Chk31
public import Certificates.Kernel.HNFO4.Chk32
public import Certificates.Kernel.HNFO4.Chk33
public import Certificates.Kernel.HNFO4.Chk34
public import Certificates.Kernel.HNFO4.Chk35
public import Certificates.Kernel.HNFO4.Chk36
public import Certificates.Kernel.HNFO4.Chk37
public import Certificates.Kernel.HNFO4.Chk38
public import Certificates.Kernel.HNFO4.Chk39
public import Certificates.Kernel.HNFO4.Chk40
public import Certificates.Kernel.HNFO4.Chk41
public import Certificates.Kernel.HNFO4.Chk42
public import Certificates.Kernel.HNFO4.Chk43
public import Certificates.Kernel.HNFO4.Chk44
public import Certificates.Kernel.HNFO4.Chk45
public import Certificates.Kernel.HNFO4.Chk46
public import Certificates.Kernel.HNFO4.Chk47
public import Certificates.Kernel.HNFO4.Chk48
public import Certificates.Kernel.HNFO4.Chk49
public import Certificates.Kernel.HNFO4.Chk50
public import Certificates.Kernel.HNFO4.Chk51
public import Certificates.Kernel.HNFO4.Chk52
public import Certificates.Kernel.HNFO4.Chk53
public import Certificates.Kernel.HNFO4.Dist
public import CFSG.Certificates.Kernel.HNFDfsSound
public import CFSG.LocalAnalysis.EvenSporadicStandard.Solomon78.HNFOrb
import CFSG.Certificates.Kernel.Common.ForallTree
import CFSG.Certificates.Kernel.Fam.HNSeed.Checks.K

public section

namespace CertificateChecks.KernelHNFO4

open CFSG.EvenSporadicStandard.Solomon78

#kc_forall_tree walksL (fun i => CFSG.KD.HNFO4.chkL i = true) 486 CFSG.KD.HNFO4.c

theorem walks : ∀ i < 486, CFSG.KD.HNFO4.chkW hnfW1 hnfW2 hnfRepWords[4]! i = true := fun i hi => by
  have h := walksL i hi
  exact (CFSG.KD.HNFO4.chkW_eq i).trans h

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
