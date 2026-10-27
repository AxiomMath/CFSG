module

public import CFSG.Quasithin.H13.L32NS7Inputs
public import Certificates.Data.Kernel.Mat8S
public import Certificates.Kernel.H13.Data
public import CFSG.Certificates.Kernel.Common.Each

public section

namespace CertificateChecks.KernelH13

open CFSG.Quasithin.H13.Mat8Cert CFSG.Quasithin.H13.S7Cert CFSG.KC.Mat8P CFSG.KC.Mat8R
  CFSG.KC.Mat8S

@[expose] noncomputable def s7OvYBS (inP : Bool) (B : List (List ℕ)) : Bool :=
  inP || (decide (49 ≤ B.length) ||
    B.length == 48 &&
      [0, 1, 2].any fun i => B.all (memLR (ofListLR (elemsFR (pG ++ [mReps.getD i one8])))))

@[expose] noncomputable def s7OvYS (y : List ℕ) : Bool :=
  s7OvYBS (memLR (ofListLR (elemsFR pG)) y) (elemsFS 6 61 (pG ++ [y]) 49)

@[expose] noncomputable def s7OvChunkS (k : ℕ) : Bool :=
  (((D.s7L.map unpackM).drop (k * 48)).take 48).all s7OvYS

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
#kc_each s7OvChunkS 0 105

end CertificateChecks.KernelH13

end
