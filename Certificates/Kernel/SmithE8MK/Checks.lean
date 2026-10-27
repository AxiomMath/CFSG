module

public import Certificates.Data.Kernel.SmithE8MK
public import Certificates.Kernel.SmithE8MK.Data

public section

namespace CertificateChecks.KernelSmithE8MK

open CFSG.SmithE8M CFSG.SmithE8M.K

theorem rows_ok : rowsOK rows edges = true := by decide +kernel

theorem chk28_ok : chk28 rows pos t28 = true := by decide +kernel

theorem chk26_ok : chk26 rows pos nra t26 = true := by decide +kernel

theorem pos_eq : e8mPos () = pos := by decide +kernel

theorem nra_eq : pos.filter (fun v => !e8mIsRA v) = nra := by decide +kernel

theorem ra_length : ((List.range 126).filter e8mIsRA).length = 27 := by decide +kernel

theorem ra_pos : ((List.range 126).filter e8mIsRA).all e8mIsPos = true := by decide +kernel

theorem c7_le : (List.range 126).all (fun m => decide (e8mRoot m ⟨6, by decide⟩ ≤ 1)) = true := by
  decide +kernel

end CertificateChecks.KernelSmithE8MK
