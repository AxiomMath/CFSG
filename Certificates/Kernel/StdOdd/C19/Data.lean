module

public import Certificates.Kernel.StdOdd.CentRef
public import CFSG.Monster.Existence.StdOdd.Cert.RepsInputs
import CFSG.Certificates.Kernel.Common.Repo
import CFSG.Certificates.Kernel.Common.Harness
public import Certificates.Kernel.StdOdd.C19.Slp

public section

namespace CFSG.KD.StdOdd.Cent

open CFSG.KC.StdOdd.Orbit CFSG.Monster.Existence.StdOdd.Cert

#kc_repo #kc_natBin CFSG.KD.StdOdd.Cent.C19 CP "Certificates/Kernel/StdOdd/data/c19/cp.bin" 15600 9507220094580664943
#kc_repo #kc_natBin CFSG.KD.StdOdd.Cent.C19 HW "Certificates/Kernel/StdOdd/data/c19/hw.bin" 3600 10349331055780426534
#kc_repo #kc_natBin CFSG.KD.StdOdd.Cent.C19 R0 "Certificates/Kernel/StdOdd/data/c19/r0.bin" 672 12743653658433503851
#kc_repo #kc_natBin CFSG.KD.StdOdd.Cent.C19 CK "Certificates/Kernel/StdOdd/data/c19/ck.bin" 1872 4683635799900500394
#kc_repo #kc_natBin CFSG.KD.StdOdd.Cent.C19 RK "Certificates/Kernel/StdOdd/data/c19/rk.bin" 50544 8292463709149384843
#kc_repo #kc_natBin CFSG.KD.StdOdd.Cent.C19 fp1 "Certificates/Kernel/StdOdd/data/c19/fp1.bin" 864864 5283580807744472219
#kc_repo #kc_natBin CFSG.KD.StdOdd.Cent.C19 fp2 "Certificates/Kernel/StdOdd/data/c19/fp2.bin" 638976 3719344953666996528
#kc_repo #kc_natBin CFSG.KD.StdOdd.Cent.C19 fp3 "Certificates/Kernel/StdOdd/data/c19/fp3.bin" 9984 12172537236476066968
#kc_repo #kc_natBin CFSG.KD.StdOdd.Cent.C19 fp4 "Certificates/Kernel/StdOdd/data/c19/fp4.bin" 63180 830848348541727764
#kc_repo #kc_natBin CFSG.KD.StdOdd.Cent.C19 fp5 "Certificates/Kernel/StdOdd/data/c19/fp5.bin" 156 10903869234591433440
#kc_repo #kc_natBin CFSG.KD.StdOdd.Cent.C19 fp6 "Certificates/Kernel/StdOdd/data/c19/fp6.bin" 156 6494745040708116402
#kc_repo #kc_natBin CFSG.KD.StdOdd.Cent.C19 fp7 "Certificates/Kernel/StdOdd/data/c19/fp7.bin" 156 15746572107853917107
#kc_repo #kc_natBin CFSG.KD.StdOdd.Cent.C19 fp8 "Certificates/Kernel/StdOdd/data/c19/fp8.bin" 156 16346980016898860911
#kc_repo #kc_natBin CFSG.KD.StdOdd.Cent.C19 fp9 "Certificates/Kernel/StdOdd/data/c19/fp9.bin" 156 13073313535901778413
#kc_repo #kc_natBin CFSG.KD.StdOdd.Cent.C19 fp10 "Certificates/Kernel/StdOdd/data/c19/fp10.bin" 156 1957936476909547024
#kc_repo #kc_natBin CFSG.KD.StdOdd.Cent.C19 fp11 "Certificates/Kernel/StdOdd/data/c19/fp11.bin" 156 11271862475717117978
#kc_repo #kc_natBin CFSG.KD.StdOdd.Cent.C19 fp12 "Certificates/Kernel/StdOdd/data/c19/fp12.bin" 156 10994525123149430302
#kc_repo #kc_natBin CFSG.KD.StdOdd.Cent.C19 fp13 "Certificates/Kernel/StdOdd/data/c19/fp13.bin" 156 13215583473244052946
#kc_repo #kc_natBin CFSG.KD.StdOdd.Cent.C19 fp14 "Certificates/Kernel/StdOdd/data/c19/fp14.bin" 156 3681337484642337637
#kc_repo #kc_natBin CFSG.KD.StdOdd.Cent.C19 fp15 "Certificates/Kernel/StdOdd/data/c19/fp15.bin" 156 13991343449825852943
#kc_repo #kc_natBin CFSG.KD.StdOdd.Cent.C19 fp16 "Certificates/Kernel/StdOdd/data/c19/fp16.bin" 156 432947754339230250
#kc_repo #kc_natBin CFSG.KD.StdOdd.Cent.C19 fp17 "Certificates/Kernel/StdOdd/data/c19/fp17.bin" 156 8149523038264927742
#kc_repo #kc_natBin CFSG.KD.StdOdd.Cent.C19 fp18 "Certificates/Kernel/StdOdd/data/c19/fp18.bin" 156 15825114411063910602
#kc_repo #kc_natBin CFSG.KD.StdOdd.Cent.C19 fw1 "Certificates/Kernel/StdOdd/data/c19/fw1.bin" 199584 3730034040454761317
#kc_repo #kc_natBin CFSG.KD.StdOdd.Cent.C19 fw2 "Certificates/Kernel/StdOdd/data/c19/fw2.bin" 147456 9831472101923145552
#kc_repo #kc_natBin CFSG.KD.StdOdd.Cent.C19 fw3 "Certificates/Kernel/StdOdd/data/c19/fw3.bin" 1408 11710006329660939935
#kc_repo #kc_natBin CFSG.KD.StdOdd.Cent.C19 fw4 "Certificates/Kernel/StdOdd/data/c19/fw4.bin" 11340 12318727388720391944
#kc_repo #kc_natBin CFSG.KD.StdOdd.Cent.C19 fw5 "Certificates/Kernel/StdOdd/data/c19/fw5.bin" 4 4135849867268524135
#kc_repo #kc_natBin CFSG.KD.StdOdd.Cent.C19 fw6 "Certificates/Kernel/StdOdd/data/c19/fw6.bin" 1 17477507686238085729
#kc_repo #kc_natList CFSG.KD.StdOdd.Cent.C19 lev "Certificates/Kernel/StdOdd/data/c19/lev.txt" 89 12880777383491566549
#kc_repo #kc_natList CFSG.KD.StdOdd.Cent.C19 ri "Certificates/Kernel/StdOdd/data/c19/ri.txt" 73 3531148343126858339
#kc_repo #kc_natList CFSG.KD.StdOdd.Cent.C19 lv "Certificates/Kernel/StdOdd/data/c19/lv.txt" 4 7642930872580413654
#kc_repo #kc_natList CFSG.KD.StdOdd.Cent.C19 hl "Certificates/Kernel/StdOdd/data/c19/hl.txt" 6 14668064790228571170
#kc_repo #kc_natList CFSG.KD.StdOdd.Cent.C19 cm "Certificates/Kernel/StdOdd/data/c19/cm.txt" 18 8539053982348496121
#kc_repo #kc_natList CFSG.KD.StdOdd.Cent.C19 cnt "Certificates/Kernel/StdOdd/data/c19/cnt.txt" 47 13756558888390384953
#kc_repo #kc_natList CFSG.KD.StdOdd.Cent.C19 vec "Certificates/Kernel/StdOdd/data/c19/vec.txt" 954 16504338991464890926
#kc_repo #kc_natList CFSG.KD.StdOdd.Cent.C19 reps "Certificates/Kernel/StdOdd/data/c19/reps.txt" 1967 8772824669936437512
#kc_repo #kc_natList CFSG.KD.StdOdd.Cent.C19 st "Certificates/Kernel/StdOdd/data/c19/st.txt" 84 3441631220000056883
#kc_repo #kc_natBin CFSG.KD.StdOdd.Cent.C19 RF "Certificates/Kernel/StdOdd/data/c19/rf.bin" 404 16595106140781053701
#kc_repo #kc_natList CFSG.KD.StdOdd.Cent.C19 sidx "Certificates/Kernel/StdOdd/data/c19/sidx.txt" 6 11688401872993433771
#kc_repo #kc_natList CFSG.KD.StdOdd.Cent.C19 fail "Certificates/Kernel/StdOdd/data/c19/fail.txt" 4 1847220230618269767
#kc_repo #kc_natList CFSG.KD.StdOdd.Cent.C19 orb "Certificates/Kernel/StdOdd/data/c19/orb.txt" 1801 13229926167188604899
#kc_repo #kc_natList CFSG.KD.StdOdd.Cent.C19 rs "Certificates/Kernel/StdOdd/data/c19/rs.txt" 42 16639919522387505232
#kc_repo #kc_natList CFSG.KD.StdOdd.Cent.C19 nl "Certificates/Kernel/StdOdd/data/c19/nl.txt" 38 3167911422168829383

@[expose] noncomputable def D19 : CentData where
  p := 19
  xw := repWord19
  d0 := wordOfString "BBABBABBABABAB"
  eL := [0, 4, 6, 10, 2, 8, 1, 3, 5, 7, 9, 11, 12, 13, 14, 15, 16, 17, 18]
  K1 := [(4, 5), (6, 5)]
  Kall := [(4, 5), (6, 5), (3, 3), (5, 3), (1, 4), (2, 4), (7, 4), (8, 4), (9, 4)]
  prog := prog19
  V := C19.P.V
  bv := nthN C19.vec 0
  βs := C19.vec.tail
  FP j := nthN [C19.fp1, C19.fp2, C19.fp3, C19.fp4, C19.fp5, C19.fp6, C19.fp7, C19.fp8, C19.fp9, C19.fp10, C19.fp11, C19.fp12, C19.fp13, C19.fp14, C19.fp15, C19.fp16, C19.fp17, C19.fp18] (j - 1)
  WN j := nthN [C19.fw1, C19.fw2, C19.fw3, C19.fw4, C19.fw5, C19.fw6, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] (j - 1)
  nf j := nthN C19.lev (2 * (j - 1))
  Df j := nthN C19.lev (2 * (j - 1) + 1)
  RI j := (segsL 64 C19.ri).getD (j - 1) []
  LI := C19.lv
  HI := segsL 64 C19.hl
  CP := C19.CP
  HW := C19.HW
  s := nthN C19.cm 0
  hD := nthN C19.cm 1
  m₀ := nthN C19.cm 2
  reps := C19.reps
  st := C19.st
  R0 := C19.R0
  r0D := nthN C19.cm 4
  cnts := C19.cnt

end CFSG.KD.StdOdd.Cent

end
