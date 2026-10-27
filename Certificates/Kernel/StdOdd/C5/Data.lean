module

public import Certificates.Kernel.StdOdd.CentRef
public import CFSG.Monster.Existence.StdOdd.Cert.RepsInputs
import CFSG.Certificates.Kernel.Common.Repo
import CFSG.Certificates.Kernel.Common.Harness
import CFSG.Certificates.Kernel.Common.Eval
meta import Certificates.Kernel.StdOdd.CandGen
public import Certificates.Kernel.StdOdd.C5.Slp

public section

namespace CFSG.KD.StdOdd.Cent

open CFSG.KC.StdOdd.Orbit CFSG.Monster.Existence.StdOdd.Cert

#kc_repo #kc_natBin CFSG.KD.StdOdd.Cent.C5 CP "Certificates/Kernel/StdOdd/data/c5/cp.bin" 1419600 17722239265961897301
#kc_repo #kc_natBin CFSG.KD.StdOdd.Cent.C5 HW "Certificates/Kernel/StdOdd/data/c5/hw.bin" 737100 2171589056762613976
#kc_repo #kc_natBin CFSG.KD.StdOdd.Cent.C5 R0 "Certificates/Kernel/StdOdd/data/c5/r0.bin" 110 17216330094622754136
#kc_repo #kc_natBin CFSG.KD.StdOdd.Cent.C5 CK "Certificates/Kernel/StdOdd/data/c5/ck.bin" 312 838026496859483488
#kc_repo #kc_natBin CFSG.KD.StdOdd.Cent.C5 RK "Certificates/Kernel/StdOdd/data/c5/rk.bin" 13104 11200666649672404463
#kc_repo #kc_natBin CFSG.KD.StdOdd.Cent.C5 fp1 "Certificates/Kernel/StdOdd/data/c5/fp1.bin" 864864 16772109325849440743
#kc_repo #kc_natBin CFSG.KD.StdOdd.Cent.C5 fp2 "Certificates/Kernel/StdOdd/data/c5/fp2.bin" 638976 8210340424293299366
#kc_repo #kc_natBin CFSG.KD.StdOdd.Cent.C5 fp3 "Certificates/Kernel/StdOdd/data/c5/fp3.bin" 359424 14101548529274961470
#kc_repo #kc_natBin CFSG.KD.StdOdd.Cent.C5 fp4 "Certificates/Kernel/StdOdd/data/c5/fp4.bin" 2340 5413726377017960414
#kc_repo #kc_natBin CFSG.KD.StdOdd.Cent.C5 fw1 "Certificates/Kernel/StdOdd/data/c5/fw1.bin" 210672 1974971968167972522
#kc_repo #kc_natBin CFSG.KD.StdOdd.Cent.C5 fw2 "Certificates/Kernel/StdOdd/data/c5/fw2.bin" 155648 16813795309922393976
#kc_repo #kc_natBin CFSG.KD.StdOdd.Cent.C5 fw3 "Certificates/Kernel/StdOdd/data/c5/fw3.bin" 78336 10796723307230760040
#kc_repo #kc_natBin CFSG.KD.StdOdd.Cent.C5 fw4 "Certificates/Kernel/StdOdd/data/c5/fw4.bin" 300 7199013709381604548
#kc_repo #kc_natList CFSG.KD.StdOdd.Cent.C5 lev "Certificates/Kernel/StdOdd/data/c5/lev.txt" 34 12156671252278529305
#kc_repo #kc_natList CFSG.KD.StdOdd.Cent.C5 ri "Certificates/Kernel/StdOdd/data/c5/ri.txt" 33 11549948493205335428
#kc_repo #kc_natList CFSG.KD.StdOdd.Cent.C5 lv "Certificates/Kernel/StdOdd/data/c5/lv.txt" 24 16202575241427978352
#kc_repo #kc_natList CFSG.KD.StdOdd.Cent.C5 hl "Certificates/Kernel/StdOdd/data/c5/hl.txt" 557 3085358740510770539
#kc_repo #kc_natList CFSG.KD.StdOdd.Cent.C5 cm "Certificates/Kernel/StdOdd/data/c5/cm.txt" 21 14787337731300422569
#kc_repo #kc_natList CFSG.KD.StdOdd.Cent.C5 cnt "Certificates/Kernel/StdOdd/data/c5/cnt.txt" 79 14283420136004109397
#kc_repo #kc_natList CFSG.KD.StdOdd.Cent.C5 vec "Certificates/Kernel/StdOdd/data/c5/vec.txt" 283 12303695873775310884
#kc_repo #kc_natList CFSG.KD.StdOdd.Cent.C5 reps "Certificates/Kernel/StdOdd/data/c5/reps.txt" 279 4286331593131589533
#kc_repo #kc_natList CFSG.KD.StdOdd.Cent.C5 st "Certificates/Kernel/StdOdd/data/c5/st.txt" 16 5050575566415601908
#kc_repo #kc_natBin CFSG.KD.StdOdd.Cent.C5 RF "Certificates/Kernel/StdOdd/data/c5/rf.bin" 1442 17944586312865623170
#kc_repo #kc_natList CFSG.KD.StdOdd.Cent.C5 sidx "Certificates/Kernel/StdOdd/data/c5/sidx.txt" 14 4031755916645987632
#kc_repo #kc_natList CFSG.KD.StdOdd.Cent.C5 fail "Certificates/Kernel/StdOdd/data/c5/fail.txt" 14 1152149531595158671
#kc_repo #kc_natList CFSG.KD.StdOdd.Cent.C5 orb "Certificates/Kernel/StdOdd/data/c5/orb.txt" 1557 17587495418152660362
#kc_repo #kc_natList CFSG.KD.StdOdd.Cent.C5 rs "Certificates/Kernel/StdOdd/data/c5/rs.txt" 14 13477230760556346950
#kc_repo #kc_natList CFSG.KD.StdOdd.Cent.C5 nl "Certificates/Kernel/StdOdd/data/c5/nl.txt" 10 11454891664941055354

#kc_eval CFSG.KD.StdOdd.Cent C5 CFSG.KD.StdOdd.Cent.candStep C5.P.V C5.CP C5.HW C5.hl C5.cm
  5 3 5341691905275459992482874955477761541053674975087606488477

@[expose] noncomputable def D5 : CentData where
  p := 5
  xw := repWord5
  d0 := wordOfString "ABBABAB"
  eL := [0, 2, 3, 1, 4]
  K1 := [(2, 5), (1, 4)]
  Kall := [(2, 5), (1, 4)]
  prog := prog5
  V := C5.P.V
  bv := nthN C5.vec 0
  βs := C5.vec.tail
  FP j := nthN [C5.fp1, C5.fp2, C5.fp3, C5.fp4] (j - 1)
  WN j := nthN [C5.fw1, C5.fw2, C5.fw3, C5.fw4] (j - 1)
  nf j := nthN C5.lev (2 * (j - 1))
  Df j := nthN C5.lev (2 * (j - 1) + 1)
  RI j := (segsL 64 C5.ri).getD (j - 1) []
  LI := C5.lv
  HI := segsL 64 C5.hl
  CP := C5.CP
  HW := C5.HW
  s := nthN C5.cm 0
  hD := nthN C5.cm 1
  m₀ := nthN C5.cm 2
  reps := C5.reps
  st := C5.st
  R0 := C5.R0
  r0D := nthN C5.cm 4
  cnts := C5.cnt

end CFSG.KD.StdOdd.Cent

end
