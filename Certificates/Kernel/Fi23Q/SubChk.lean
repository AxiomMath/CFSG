module

import Certificates.Kernel.Fi23Q.SubDefs
import CFSG.Certificates.Kernel.Common.EachTrue
import CFSG.Certificates.Kernel.Common.Repo
import CFSG.Certificates.Kernel.BabyMonster.Load

#bm_bool CFSG.KD.Fi23Q relSK_ok (relSK)
#bm_bool CFSG.KD.Fi23Q fixSK_ok (fixSK)

#kc_repo #kc_each_rows CFSG.KD.Fi23Q npc (fun _ v b q c n W => CFSG.KD.Fi23Q.npK v b q c n W)
  "Certificates/Kernel/Fi23Q/data/np.txt.gz" 5008 2045859103492980691 0 82
