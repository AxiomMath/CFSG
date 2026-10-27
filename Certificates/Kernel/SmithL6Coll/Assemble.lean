module

public import Certificates.Kernel.SmithL6Coll.Search0
public import Certificates.Kernel.SmithL6Coll.Search1
public import Certificates.Kernel.SmithL6Coll.Search2
public import Certificates.Kernel.SmithL6Coll.Search3
public import Certificates.Kernel.SmithL6Coll.Rows0
public import Certificates.Kernel.SmithL6Coll.Rows1
public import Certificates.Kernel.SmithL6Coll.Rows2
public import Certificates.Kernel.SmithL6Coll.Rows3
public import CFSG.Certificates.Kernel.SmithL6CollSound
import CFSG.Certificates.Kernel.Common.ForallChunks

public section

namespace CertificateChecks.KernelSmithL6Coll

open CFSG.SmithL6 CFSG.SmithL6.CollK

#kc_forall_chunks topAll (fun k => top k = true) 49 CertificateChecks.KernelSmithL6Coll.top 1

#kc_forall_chunks rowsAll (fun k => rows k = true) 31 CertificateChecks.KernelSmithL6Coll.rows 1

theorem rtop_length : rtop.length = 49 := by decide +kernel

theorem LM_length : LM.length = 651 := by decide +kernel

theorem LM_fst : LM.map (·.1) = rtop.flatten :=
  List.map_fst_zip (by decide +kernel : rtop.flatten.length ≤ tfm.length)

theorem chkColl_holds : chkColl = true := by
  refine chkColl_of_rowK LM ?_ ?_
  · rw [LM_fst]
    exact collL_eq rtop rtop_length topAll
  · intro a ha
    rw [LM_length] at ha
    have h31 : a / 21 < 31 := by omega
    have hk := rowsAll (a / 21) h31
    unfold rows rowsK at hk
    rw [List.all_eq_true] at hk
    have := hk (a % 21) (List.mem_range.mpr (Nat.mod_lt _ (by omega)))
    rwa [Nat.div_add_mod] at this

end CertificateChecks.KernelSmithL6Coll
