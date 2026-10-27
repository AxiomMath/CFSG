module

public import Certificates.Kernel.Q8Wit.L34Data
public import Certificates.Kernel.Q8Wit.L34ExtData
public import Certificates.Kernel.LocalComp.L34SChk
public import Certificates.Data.Kernel.Q8WitL34
public import CFSG.Certificates.Kernel.Common.Each
public import CFSG.Certificates.Kernel.Common.ForallChunks
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelQ8W.L34

open CFSG.KC.Enum CFSG.KS CFSG.KS.Prim CFSG.KC.Q8Wit CertificateChecks.KernelLC

theorem sqIn : sqInK 42 6 Q.N SQ 20160 L34S.T W = true := by quickRfl

theorem sqInNeg : (!sqInK 42 6 Q.N SQ 1 (fun _ => pidn 42 6) W) = true := by quickRfl

theorem c1Canon : allN 64 (fun a => canonK 42 6 (mask 6) (42 * 6) (L34C1.P a)) = true := by
  quickRfl

@[expose] noncomputable def ch397505Cent (s : Nat) : Bool :=
  allN 20160 fun t => centPtK 42 6 L34R.T 64 L34C1.P 256 (Nat.add (Nat.mul 20160 s) t)

#kc_each CertificateChecks.KernelQ8W.L34.ch397505Cent 0 12

#kc_forall_chunks centAll (fun s => ch397505Cent s = true) 12
  CertificateChecks.KernelQ8W.L34.ch397505Cent 1

theorem centNeg : (!allN 20160 fun t => centPtK 42 6 L34R.T 64 L34C1.P 1 t) = true := by
  quickRfl

end CertificateChecks.KernelQ8W.L34

end
