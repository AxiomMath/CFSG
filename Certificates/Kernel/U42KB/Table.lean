module

public import Certificates.Data.U42Presentation
public import Certificates.Data.Kernel.Bounds.TableFact
public import CFSG.Certificates.Kernel.Bounds.Checks
public import Certificates.Kernel.Bounds.Assemble
import CFSG.Certificates.Kernel.Bounds.Load
import CFSG.Certificates.Kernel.Bounds.LoadRoot
import CFSG.Certificates.Kernel.Common.Repo
import CFSG.Certificates.Kernel.Common.Harness

open CFSG.HardMathSupport.Dickson.I271.U42Presentation

public section

set_option maxRecDepth 100000

namespace CFSG.KBRoute.K17350

@[expose] def rels : List (List (Nat × Bool)) :=
  u42Words.map fun w => w.map fun l => (l.1.val, l.2)

end CFSG.KBRoute.K17350

#kc_repo #kc_blocked_root CFSG.KBData.K17350.F "Certificates/Kernel/U42KB/data/K17350.F.bin" 12 6 18446744073709551615 425536 16428671081957130492
#kc_repo #kc_blocked_root CFSG.KBData.K17350.D "Certificates/Kernel/U42KB/data/K17350.D.bin" 12 4 65535 52966 13760032492429170159
#kc_repo #kc_items_root CFSG.KBData.K17350.Wd "Certificates/Kernel/U42KB/data/K17350.Wd.items" 1593 4822748405695143803
#kc_repo #kc_items_root CFSG.KBData.K17350.Wd2 "Certificates/Kernel/U42KB/data/K17350.Wd2.items" 2719 12056645730839540911
#kc_repo #kc_items_root CFSG.KBData.K17350.R "Certificates/Kernel/U42KB/data/K17350.R.items" 82 17883732433200055715
#kc_repo #kc_items_root CFSG.KBData.K17350.S "Certificates/Kernel/U42KB/data/K17350.S.items" 4 14007230941556241898
#kc_repo #kc_list_root CFSG.KBData.K17350.wl0 "Certificates/Kernel/U42KB/data/K17350.wl0.items" 1 654013 17960243330384339754
#kc_repo #kc_list_root CFSG.KBData.K17350.cv0 "Certificates/Kernel/U42KB/data/K17350.cv0.items" 1 228414 2836504699500378186

#kb_table CFSG.KBRoute.K17350 T1 K17350 include_bytes "data/K17350.meta" 8373 1381290945701585872 513 CFSG.KBRoute.K17350.rels ""

theorem CFSG.KBRoute.K17350.top :
    CFSG.Certificates.KB.topOk CFSG.KBRoute.K17350.T1.amap (nat_lit 2) = true := by
  quickRfl

#kb_checks K17350 include_bytes "data/K17350.meta" 8373 1381290945701585872 0
#kb_checks K17350 include_bytes "data/K17350.meta" 8373 1381290945701585872 1

#kb_cert CFSG.KBRoute.K17350 T1 K17350 include_bytes "data/K17350.meta" 8373 1381290945701585872 CFSG.KBRoute.K17350.rels

theorem CFSG.KBRoute.K17350.t1 : CFSG.KBRoute.K17350.T1.ok = true := by kb_assemble K17350

theorem CFSG.KBFact.K17350 :
    CFSG.Certificates.KB.TableFact 2 CFSG.KBRoute.K17350.rels CFSG.KBRoute.K17350.T1.words 25920 :=
  CFSG.Certificates.KB.TableFact.intro CFSG.KBRoute.K17350.t1 CFSG.KBRoute.K17350.top

end
