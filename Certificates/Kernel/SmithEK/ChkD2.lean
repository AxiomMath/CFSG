module

public import Certificates.Kernel.SmithEK.MPinsA
public import Certificates.Kernel.SmithEK.MPinsB
public import Certificates.Kernel.SmithEK.MRowsA
public import Certificates.Kernel.SmithEK.MRowsB
public import Certificates.Kernel.SmithEK.ChkUA
public import Certificates.Kernel.SmithEK.Span
public import CFSG.Certificates.Kernel.SmithEK.MSound
import CFSG.Certificates.Kernel.Common.ForallTree
public import CFSG.Fischer.HermitianEquiv
public import Certificates.Data.CFSGNative.Fischer.Xi22

public section

namespace CertificateChecks.KernelSmithEK

open CFSG.SmithE CFSG.SmithE.K

#kc_forall_tree mpins_all (fun c => ptChunkK wd.M pb.P pts.L (27 * c) 27 = true) 33
  CertificateChecks.KernelSmithEK.c21266pin_

#kc_forall_tree mrows_all (fun c => d2ChunkK pb.P (27 * c) 27 = true) 33
  CertificateChecks.KernelSmithEK.c21266row_

theorem pb_len : pb.P.length = 891 := by
  decide +kernel

theorem pb_get {i : Nat} (hi : i < 891) : pb.P.getD i 0 = ptBits (wMask i) pts.L := by
  rw [wMask_eq_wd hi]
  have hc : i / 27 < 33 := by omega
  have h1 : 27 * (i / 27) ≤ i := by omega
  have h2 : i < 27 * (i / 27) + 27 := by omega
  exact ptChunkK_sound (mpins_all (i / 27) hc) h1 h2

theorem chkDist2_eq : chkDist2 = true := by
  refine chkDist2_of uPts_eq pts_length pb_len (fun _ hi => pb_get hi) (fun i hi => ?_)
  have hc : i / 27 < 33 := by omega
  have h1 : 27 * (i / 27) ≤ i := by omega
  have h2 : i < 27 * (i / 27) + 27 := by omega
  exact d2ChunkK_sound (mrows_all (i / 27) hc) h1 h2

end CertificateChecks.KernelSmithEK
