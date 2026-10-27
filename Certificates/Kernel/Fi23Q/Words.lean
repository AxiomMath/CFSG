module

import Certificates.Kernel.Fi23Q.WordDefs
import CFSG.Certificates.Kernel.Common.EachTrue
import CFSG.Certificates.Kernel.Common.Repo
import CFSG.Certificates.Kernel.BabyMonster.Load

#kc_repo #kc_each_rows CFSG.KD.Fi23Q cw (fun q c n W => CFSG.KD.Fi23Q.wordK q c n W)
  "Certificates/Kernel/Fi23Q/data/words.txt.gz" 8481 91643479740879414 0 198

#bm_bool CFSG.KD.Fi23Q zK_ok (zK)
#bm_bool CFSG.KD.Fi23Q t2K_ok (t2K)
