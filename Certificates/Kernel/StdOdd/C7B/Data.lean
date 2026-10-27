module

public import Certificates.Kernel.StdOdd.CentRef
public import CFSG.Monster.Existence.StdOdd.Cert.RepsInputs
import CFSG.Certificates.Kernel.Common.Repo
import CFSG.Certificates.Kernel.Common.Harness
public import Certificates.Kernel.StdOdd.C7B.Slp

public section

namespace CFSG.KD.StdOdd.Cent

open CFSG.KC.StdOdd.Orbit CFSG.Monster.Existence.StdOdd.Cert

#kc_repo #kc_natBin CFSG.KD.StdOdd.Cent.C7B CP "Certificates/Kernel/StdOdd/data/c7B/cp.bin" 378456 5588478473120375150
#kc_repo #kc_natBin CFSG.KD.StdOdd.Cent.C7B HW "Certificates/Kernel/StdOdd/data/c7B/hw.bin" 164968 1892361894895071316
#kc_repo #kc_natBin CFSG.KD.StdOdd.Cent.C7B R0 "Certificates/Kernel/StdOdd/data/c7B/r0.bin" 696 403150499296050576
#kc_repo #kc_natBin CFSG.KD.StdOdd.Cent.C7B CK "Certificates/Kernel/StdOdd/data/c7B/ck.bin" 1872 13278649076843148669
#kc_repo #kc_natBin CFSG.KD.StdOdd.Cent.C7B CC "Certificates/Kernel/StdOdd/data/c7B/cc.bin" 756912 11135723795341246873
#kc_repo #kc_natBin CFSG.KD.StdOdd.Cent.C7B RK "Certificates/Kernel/StdOdd/data/c7B/rk.bin" 81432 584595078464223337
#kc_repo #kc_natBin CFSG.KD.StdOdd.Cent.C7B fp1 "Certificates/Kernel/StdOdd/data/c7B/fp1.bin" 864864 2864407904700539672
#kc_repo #kc_natBin CFSG.KD.StdOdd.Cent.C7B fp2 "Certificates/Kernel/StdOdd/data/c7B/fp2.bin" 168480 2676411812649577685
#kc_repo #kc_natBin CFSG.KD.StdOdd.Cent.C7B fp3 "Certificates/Kernel/StdOdd/data/c7B/fp3.bin" 79872 2487986459207464143
#kc_repo #kc_natBin CFSG.KD.StdOdd.Cent.C7B fp4 "Certificates/Kernel/StdOdd/data/c7B/fp4.bin" 19968 9926422064343602098
#kc_repo #kc_natBin CFSG.KD.StdOdd.Cent.C7B fp5 "Certificates/Kernel/StdOdd/data/c7B/fp5.bin" 312 273988827513921984
#kc_repo #kc_natBin CFSG.KD.StdOdd.Cent.C7B fp6 "Certificates/Kernel/StdOdd/data/c7B/fp6.bin" 156 14009967601920213459
#kc_repo #kc_natBin CFSG.KD.StdOdd.Cent.C7B fw1 "Certificates/Kernel/StdOdd/data/c7B/fw1.bin" 199584 13404070811393837590
#kc_repo #kc_natBin CFSG.KD.StdOdd.Cent.C7B fw2 "Certificates/Kernel/StdOdd/data/c7B/fw2.bin" 36720 17171020759329023745
#kc_repo #kc_natBin CFSG.KD.StdOdd.Cent.C7B fw3 "Certificates/Kernel/StdOdd/data/c7B/fw3.bin" 16384 17655163629098652961
#kc_repo #kc_natBin CFSG.KD.StdOdd.Cent.C7B fw4 "Certificates/Kernel/StdOdd/data/c7B/fw4.bin" 4096 2820012639149441657
#kc_repo #kc_natBin CFSG.KD.StdOdd.Cent.C7B fw5 "Certificates/Kernel/StdOdd/data/c7B/fw5.bin" 16 14252345723972168666
#kc_repo #kc_natList CFSG.KD.StdOdd.Cent.C7B lev "Certificates/Kernel/StdOdd/data/c7B/lev.txt" 41 2704503491838498482
#kc_repo #kc_natList CFSG.KD.StdOdd.Cent.C7B ri "Certificates/Kernel/StdOdd/data/c7B/ri.txt" 51 16143569762079349058
#kc_repo #kc_natList CFSG.KD.StdOdd.Cent.C7B lv "Certificates/Kernel/StdOdd/data/c7B/lv.txt" 4 7427733806509192916
#kc_repo #kc_natList CFSG.KD.StdOdd.Cent.C7B hl "Certificates/Kernel/StdOdd/data/c7B/hl.txt" 599 2680388107081074864
#kc_repo #kc_natList CFSG.KD.StdOdd.Cent.C7B cm "Certificates/Kernel/StdOdd/data/c7B/cm.txt" 23 4294628820456199956
#kc_repo #kc_natList CFSG.KD.StdOdd.Cent.C7B cnt "Certificates/Kernel/StdOdd/data/c7B/cnt.txt" 79 6145022105732860268
#kc_repo #kc_natList CFSG.KD.StdOdd.Cent.C7B vec "Certificates/Kernel/StdOdd/data/c7B/vec.txt" 383 16052637676044166916
#kc_repo #kc_natList CFSG.KD.StdOdd.Cent.C7B reps "Certificates/Kernel/StdOdd/data/c7B/reps.txt" 1986 3370593898973996295
#kc_repo #kc_natList CFSG.KD.StdOdd.Cent.C7B st "Certificates/Kernel/StdOdd/data/c7B/st.txt" 90 10579985296150651592
#kc_repo #kc_natBin CFSG.KD.StdOdd.Cent.C7B RF "Certificates/Kernel/StdOdd/data/c7B/rf.bin" 6786 12183918182468684679
#kc_repo #kc_natList CFSG.KD.StdOdd.Cent.C7B sidx "Certificates/Kernel/StdOdd/data/c7B/sidx.txt" 79 6341827816808379021
#kc_repo #kc_natList CFSG.KD.StdOdd.Cent.C7B fail "Certificates/Kernel/StdOdd/data/c7B/fail.txt" 58 10302630463427664380
#kc_repo #kc_natList CFSG.KD.StdOdd.Cent.C7B orb "Certificates/Kernel/StdOdd/data/c7B/orb.txt" 9501 10439015384792699575
#kc_repo #kc_natList CFSG.KD.StdOdd.Cent.C7B rs "Certificates/Kernel/StdOdd/data/c7B/rs.txt" 18 414384928551020945
#kc_repo #kc_natList CFSG.KD.StdOdd.Cent.C7B nl "Certificates/Kernel/StdOdd/data/c7B/nl.txt" 14 11988166176327901981

@[expose] noncomputable def D7B : CentData where
  p := 7
  xw := repWord7B
  d0 := wordOfString "ABABBABBABABAB"
  eL := [0, 2, 4, 5, 3, 1, 6]
  K1 := [(2, 5), (3, 3)]
  Kall := [(2, 5), (1, 3), (3, 3)]
  prog := prog7B
  V := C7B.P.V
  bv := nthN C7B.vec 0
  βs := C7B.vec.tail
  FP j := nthN [C7B.fp1, C7B.fp2, C7B.fp3, C7B.fp4, C7B.fp5, C7B.fp6] (j - 1)
  WN j := nthN [C7B.fw1, C7B.fw2, C7B.fw3, C7B.fw4, C7B.fw5, 0] (j - 1)
  nf j := nthN C7B.lev (2 * (j - 1))
  Df j := nthN C7B.lev (2 * (j - 1) + 1)
  RI j := (segsL 64 C7B.ri).getD (j - 1) []
  LI := C7B.lv
  HI := segsL 64 C7B.hl
  CP := C7B.CP
  HW := C7B.HW
  s := nthN C7B.cm 0
  hD := nthN C7B.cm 1
  m₀ := nthN C7B.cm 2
  reps := C7B.reps
  st := C7B.st
  R0 := C7B.R0
  r0D := nthN C7B.cm 4
  cnts := C7B.cnt

end CFSG.KD.StdOdd.Cent

end
