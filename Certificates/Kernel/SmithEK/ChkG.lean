module

public import Certificates.Kernel.SmithEK.GChk
public import Certificates.Kernel.SmithEK.GRowsA
public import Certificates.Kernel.SmithEK.GRowsB
public import Certificates.Kernel.SmithEK.ChkD2
public import Certificates.Kernel.SmithEK.ChkC
public import CFSG.Certificates.Kernel.SmithEK.GSound
import CFSG.Certificates.Kernel.Common.ForallTree
public import Certificates.Kernel.SmithEK.ChkP
public import Certificates.Kernel.UnitarySix.Letters

public section

namespace CertificateChecks.KernelSmithEK

open CFSG.SmithE CFSG.SmithE.K

#kc_forall_tree grows_all (fun c => gramChunkK wd.W pb.P (27 * c) 27 = true) 33
  CertificateChecks.KernelSmithEK.c21260gram_

theorem chkPlanes_eq : chkPlanes = true :=
  chkPlanes_of uPts_eq pts_length pb_len (fun _ hi => pb_get hi) c21260planes

theorem chkGram_eq : chkGram = true := by
  refine chkGram_of uPts_eq pts_length pb_len (fun _ hi => pb_get hi) wd_len
    (fun _ hi => wtArr_wd hi) (fun i hi => ?_)
  have hc : i / 27 < 33 := by omega
  have h1 : 27 * (i / 27) ≤ i := by omega
  have h2 : i < 27 * (i / 27) + 27 := by omega
  exact gramChunkK_sound (grows_all (i / 27) hc) h1 h2

theorem chkFormInv_eq : chkFormInv = true := by
  obtain ⟨hl, hc⟩ := bounds_of c21260conj
  exact chkFormInv_of tvArr_cs hl (fun k hk => (hc k hk).1) c21260form

end CertificateChecks.KernelSmithEK
