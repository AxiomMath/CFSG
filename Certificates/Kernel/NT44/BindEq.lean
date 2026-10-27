module

public import Certificates.Kernel.NT44.Bind
import CFSG.Certificates.Kernel.Misc.RowsBind

public section

namespace CertificateChecks.KernelNT44

open CFSG.GH74.GLS.NT44.PermutationNative CFSG.KS.Raw CFSG.KC.Misc.ArrEnum

theorem nt44_ks_eq : ks () = ((List.range 2).map fun i => unpack 2688 12 (nt44KS i)).toArray :=
  rowsBind_arr rfl nt44_ks

theorem nt44_p0_eq : p0 () = ((List.range 9).map fun i => unpack 2688 12 (nt44P0 i)).toArray :=
  rowsBind_arr rfl nt44_p0

theorem nt44_lifts_eq :
    lifts () = ((List.range 256).map fun i => unpack 2688 12 (nt44L i)).toArray :=
  rowsBind_arr (by simp only [lifts, Array.size_append, List.size_toArray, List.length_cons,
    List.length_nil]) nt44_lifts

theorem nt44_sk_eq : sk () = ((List.range 7).map fun i => unpack 448 9 (nt44SK i)).toArray :=
  rowsBind_arr rfl nt44_sk

theorem nt44_sp_eq : sp () = ((List.range 10).map fun i => unpack 448 9 (nt44SP i)).toArray :=
  rowsBind_arr rfl nt44_sp

end CertificateChecks.KernelNT44

end
