module

public import Certificates.Kernel.FixBoundK.PairGData
public import Certificates.Kernel.FixBoundK.MemData0
public import Certificates.Kernel.FixBoundK.MemData1
public import Certificates.Kernel.FixBoundK.MemData2
public import Certificates.Kernel.FixBoundK.MemData3
public import Certificates.Kernel.FixBoundK.MemData4
public import Certificates.Kernel.FixBoundK.MemData5
public import Certificates.Kernel.FixBoundK.MemData6
public import Certificates.Kernel.FixBoundK.MemData7
public import Certificates.Kernel.FixBoundK.MemData8
public import Certificates.Kernel.FixBoundK.MemData9
public import CFSG.Certificates.Kernel.Common.EachTrue

set_option maxRecDepth 400000

public section

open CFSG.KC.FixBoundK.Pair CertificateChecks.KernelFixBoundK.PairG
  CertificateChecks.KernelFixBoundK.Mem0 in
#kc_each CertificateChecks.KernelFixBoundK.PairRep m0r (repAtP IV RG B nB 191 lo reps gens) 0 11

open CFSG.KC.FixBoundK.Pair CertificateChecks.KernelFixBoundK.PairG
  CertificateChecks.KernelFixBoundK.Mem1 in
#kc_each CertificateChecks.KernelFixBoundK.PairRep m1r (repAtP IV RG B nB 191 lo reps gens) 0 31

open CFSG.KC.FixBoundK.Pair CertificateChecks.KernelFixBoundK.PairG
  CertificateChecks.KernelFixBoundK.Mem2 in
#kc_each CertificateChecks.KernelFixBoundK.PairRep m2r (repAtP IV RG B nB 191 lo reps gens) 0 56

open CFSG.KC.FixBoundK.Pair CertificateChecks.KernelFixBoundK.PairG
  CertificateChecks.KernelFixBoundK.Mem3 in
#kc_each CertificateChecks.KernelFixBoundK.PairRep m3r (repAtP IV RG B nB 191 lo reps gens) 0 65

open CFSG.KC.FixBoundK.Pair CertificateChecks.KernelFixBoundK.PairG
  CertificateChecks.KernelFixBoundK.Mem4 in
#kc_each CertificateChecks.KernelFixBoundK.PairRep m4r (repAtP IV RG B nB 191 lo reps gens) 0 133

open CFSG.KC.FixBoundK.Pair CertificateChecks.KernelFixBoundK.PairG
  CertificateChecks.KernelFixBoundK.Mem5 in
#kc_each CertificateChecks.KernelFixBoundK.PairRep m5r (repAtP IV RG B nB 191 lo reps gens) 0 95

open CFSG.KC.FixBoundK.Pair CertificateChecks.KernelFixBoundK.PairG
  CertificateChecks.KernelFixBoundK.Mem6 in
#kc_each CertificateChecks.KernelFixBoundK.PairRep m6r (repAtP IV RG B nB 191 lo reps gens) 0 72

open CFSG.KC.FixBoundK.Pair CertificateChecks.KernelFixBoundK.PairG
  CertificateChecks.KernelFixBoundK.Mem7 in
#kc_each CertificateChecks.KernelFixBoundK.PairRep m7r (repAtP IV RG B nB 191 lo reps gens) 0 159

open CFSG.KC.FixBoundK.Pair CertificateChecks.KernelFixBoundK.PairG
  CertificateChecks.KernelFixBoundK.Mem8 in
#kc_each CertificateChecks.KernelFixBoundK.PairRep m8r (repAtP IV RG B nB 191 lo reps gens) 0 94

open CFSG.KC.FixBoundK.Pair CertificateChecks.KernelFixBoundK.PairG
  CertificateChecks.KernelFixBoundK.Mem9 in
#kc_each CertificateChecks.KernelFixBoundK.PairRep m9r (repAtP IV RG B nB 191 lo reps gens) 0 35

end
