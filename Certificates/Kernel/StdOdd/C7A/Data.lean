module

public import Certificates.Kernel.StdOdd.CentRef
public import CFSG.Monster.Existence.StdOdd.Cert.RepsInputs
import CFSG.Certificates.Kernel.Common.Repo
import CFSG.Certificates.Kernel.Common.Harness
import CFSG.Certificates.Kernel.Common.Eval
meta import Certificates.Kernel.StdOdd.CandGen
public import Certificates.Kernel.StdOdd.C7A.Slp

public section

namespace CFSG.KD.StdOdd.Cent

open CFSG.KC.StdOdd.Orbit CFSG.Monster.Existence.StdOdd.Cert

#kc_repo #kc_natBin CFSG.KD.StdOdd.Cent.C7A CP "Certificates/Kernel/StdOdd/data/c7A/cp.bin" 382200 6453178864751263050
#kc_repo #kc_natBin CFSG.KD.StdOdd.Cent.C7A HW "Certificates/Kernel/StdOdd/data/c7A/hw.bin" 588000 12263127214492723883
#kc_repo #kc_natBin CFSG.KD.StdOdd.Cent.C7A R0 "Certificates/Kernel/StdOdd/data/c7A/r0.bin" 82 17554045608405702331
#kc_repo #kc_natBin CFSG.KD.StdOdd.Cent.C7A CK "Certificates/Kernel/StdOdd/data/c7A/ck.bin" 312 8004406940964794072
#kc_repo #kc_natBin CFSG.KD.StdOdd.Cent.C7A CC "Certificates/Kernel/StdOdd/data/c7A/cc.bin" 764400 11510492858261034561
#kc_repo #kc_natBin CFSG.KD.StdOdd.Cent.C7A RK "Certificates/Kernel/StdOdd/data/c7A/rk.bin" 2808 4097371518243571377
#kc_repo #kc_natBin CFSG.KD.StdOdd.Cent.C7A fp1 "Certificates/Kernel/StdOdd/data/c7A/fp1.bin" 864864 256359016295231435
#kc_repo #kc_natBin CFSG.KD.StdOdd.Cent.C7A fp2 "Certificates/Kernel/StdOdd/data/c7A/fp2.bin" 168480 9561477602662504527
#kc_repo #kc_natBin CFSG.KD.StdOdd.Cent.C7A fp3 "Certificates/Kernel/StdOdd/data/c7A/fp3.bin" 19968 4169225347443317453
#kc_repo #kc_natBin CFSG.KD.StdOdd.Cent.C7A fp4 "Certificates/Kernel/StdOdd/data/c7A/fp4.bin" 4992 15309363064111277878
#kc_repo #kc_natBin CFSG.KD.StdOdd.Cent.C7A fp5 "Certificates/Kernel/StdOdd/data/c7A/fp5.bin" 468 260444357656284622
#kc_repo #kc_natBin CFSG.KD.StdOdd.Cent.C7A fp6 "Certificates/Kernel/StdOdd/data/c7A/fp6.bin" 156 5288937724319935570
#kc_repo #kc_natBin CFSG.KD.StdOdd.Cent.C7A fw1 "Certificates/Kernel/StdOdd/data/c7A/fw1.bin" 288288 14838645269166310006
#kc_repo #kc_natBin CFSG.KD.StdOdd.Cent.C7A fw2 "Certificates/Kernel/StdOdd/data/c7A/fw2.bin" 49680 13074871356752205489
#kc_repo #kc_natBin CFSG.KD.StdOdd.Cent.C7A fw3 "Certificates/Kernel/StdOdd/data/c7A/fw3.bin" 4864 18024738959299549133
#kc_repo #kc_natBin CFSG.KD.StdOdd.Cent.C7A fw4 "Certificates/Kernel/StdOdd/data/c7A/fw4.bin" 1152 7159612722066126560
#kc_repo #kc_natBin CFSG.KD.StdOdd.Cent.C7A fw5 "Certificates/Kernel/StdOdd/data/c7A/fw5.bin" 63 17179257125984464464
#kc_repo #kc_natList CFSG.KD.StdOdd.Cent.C7A lev "Certificates/Kernel/StdOdd/data/c7A/lev.txt" 41 1827542152242321854
#kc_repo #kc_natList CFSG.KD.StdOdd.Cent.C7A ri "Certificates/Kernel/StdOdd/data/c7A/ri.txt" 52 14225812785839686916
#kc_repo #kc_natList CFSG.KD.StdOdd.Cent.C7A lv "Certificates/Kernel/StdOdd/data/c7A/lv.txt" 32 417156074188728967
#kc_repo #kc_natList CFSG.KD.StdOdd.Cent.C7A hl "Certificates/Kernel/StdOdd/data/c7A/hl.txt" 328 1895737946723692045
#kc_repo #kc_natList CFSG.KD.StdOdd.Cent.C7A cm "Certificates/Kernel/StdOdd/data/c7A/cm.txt" 22 453792395966836468
#kc_repo #kc_natList CFSG.KD.StdOdd.Cent.C7A cnt "Certificates/Kernel/StdOdd/data/c7A/cnt.txt" 79 10640431287453733109
#kc_repo #kc_natList CFSG.KD.StdOdd.Cent.C7A vec "Certificates/Kernel/StdOdd/data/c7A/vec.txt" 375 11297603935683977035
#kc_repo #kc_natList CFSG.KD.StdOdd.Cent.C7A reps "Certificates/Kernel/StdOdd/data/c7A/reps.txt" 83 6978493333021799903
#kc_repo #kc_natList CFSG.KD.StdOdd.Cent.C7A st "Certificates/Kernel/StdOdd/data/c7A/st.txt" 4 1701068595381101899
#kc_repo #kc_natBin CFSG.KD.StdOdd.Cent.C7A RF "Certificates/Kernel/StdOdd/data/c7A/rf.bin" 82 12064245716719617545
#kc_repo #kc_natList CFSG.KD.StdOdd.Cent.C7A sidx "Certificates/Kernel/StdOdd/data/c7A/sidx.txt" 2 17476141023344629828
#kc_repo #kc_natList CFSG.KD.StdOdd.Cent.C7A fail "Certificates/Kernel/StdOdd/data/c7A/fail.txt" 2 17476141023344629828
#kc_repo #kc_natList CFSG.KD.StdOdd.Cent.C7A orb "Certificates/Kernel/StdOdd/data/c7A/orb.txt" 321 5489092211429925106
#kc_repo #kc_natList CFSG.KD.StdOdd.Cent.C7A rs "Certificates/Kernel/StdOdd/data/c7A/rs.txt" 15 13985999981520297626
#kc_repo #kc_natList CFSG.KD.StdOdd.Cent.C7A nl "Certificates/Kernel/StdOdd/data/c7A/nl.txt" 14 1528644429987868746

#kc_eval CFSG.KD.StdOdd.Cent C7A CFSG.KD.StdOdd.Cent.levStep C7A.P.V C7A.fp1 C7A.fw1 C7A.ri C7A.lev 1 4

@[expose] noncomputable def D7A : CentData where
  p := 7
  xw := repWord7A
  d0 := wordOfString "BABABBABAB"
  eL := [0, 1, 2, 3, 4, 5, 6]
  K1 := [(1, 5), (3, 4)]
  Kall := [(1, 5), (2, 3), (3, 4)]
  prog := prog7A
  V := C7A.P.V
  bv := nthN C7A.vec 0
  βs := C7A.vec.tail
  FP j := nthN [C7A.fp1, C7A.fp2, C7A.fp3, C7A.fp4, C7A.fp5, C7A.fp6] (j - 1)
  WN j := nthN [C7A.fw1, C7A.fw2, C7A.fw3, C7A.fw4, C7A.fw5, 0] (j - 1)
  nf j := nthN C7A.lev (2 * (j - 1))
  Df j := nthN C7A.lev (2 * (j - 1) + 1)
  RI j := (segsL 64 C7A.ri).getD (j - 1) []
  LI := C7A.lv
  HI := segsL 64 C7A.hl
  CP := C7A.CP
  HW := C7A.HW
  s := nthN C7A.cm 0
  hD := nthN C7A.cm 1
  m₀ := nthN C7A.cm 2
  reps := C7A.reps
  st := C7A.st
  R0 := C7A.R0
  r0D := nthN C7A.cm 4
  cnts := C7A.cnt

end CFSG.KD.StdOdd.Cent

end
