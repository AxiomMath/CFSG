module

public import Certificates.Data.Kernel.PermCent.L34SevenW
import CFSG.Certificates.Kernel.Common.Each
import CFSG.Certificates.Kernel.Common.Harness
public import CFSG.Certificates.Kernel.Common.ForallTree
meta import CFSG.Certificates.Kernel.Common.ForallTree

public section

set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option Elab.async false

namespace CFSG.Certificates.Kernel.PkCV.L34T

open CFSG.GH74.KGroups.L34

#kc_each sevenS 0 42

#kc_forall_tree sevenS_all (fun s => CFSG.Certificates.Kernel.PkCV.L34T.sevenS s = true) 42
  CFSG.Certificates.Kernel.PkCV.L34T.sevenS

theorem wOK_true : wOK = true := by quickRfl

theorem laOK_true : laOK = true := by quickRfl

theorem lpOK_true : lpOK = true := by quickRfl

theorem lenOK_true : lenOK = true := by quickRfl

theorem k13510 : sevenH = true :=
  sevenH_of_slices wOK_true laOK_true lpOK_true lenOK_true sevenS_all

end CFSG.Certificates.Kernel.PkCV.L34T

end
