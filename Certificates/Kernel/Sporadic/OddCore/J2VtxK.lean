module

public import Certificates.Kernel.Sporadic.OddCore.J2VtxD
public import Certificates.Kernel.Sporadic.OddCore.J2CnK
import CFSG.Certificates.Kernel.Common.Harness
import CFSG.Certificates.Kernel.Common.Each

public section

set_option maxRecDepth 400000
set_option Elab.async false

namespace CertificateChecks.KernelSpor.J2Vtx

open CFSG.KC.Enum CFSG.KS CFSG.KS.Prim CFSG.KS.PEnum CFSG.KS.MulH
open CertificateChecks.KernelSpor.J2Cn
open CFSG.Quasithin.F112R.St84.J2Model CFSG.Quasithin.F112R.St84.Heis CFSG.Fischer

@[expose] noncomputable def pinv (p : Nat) : Nat := pinvS 315 9 (mask 9) p

@[expose] noncomputable def invV (p r : Nat) : Bool :=
  bAnd(canonK 315 9 (mask 9) (315 * 9) p, bAnd(canonK 315 9 (mask 9) (315 * 9) r,
    invEqK 315 9 (mask 9) (315 * 9) p r))

@[expose] noncomputable def wC (wd : List Nat) : Nat :=
  wfoldK 315 9 (mask 9) (fun l => F (Nat.add 31 l)) wd idK

@[expose] noncomputable def wP (wd : List Nat) : Nat :=
  wfoldK 315 9 (mask 9) (fun l => J2P.S (Nat.sub l 1)) wd idK

@[expose] noncomputable def lR (l : Nat) : Nat :=
  VxT ([2, 3, 4, 5, 7, 6, 8].getD (Nat.sub l 1) 0)

@[expose] noncomputable def wR : Nat := wfoldK 315 9 (mask 9) lR [1, 4, 7, 5, 6] idK

@[expose] noncomputable def EKc (k : Nat) : Nat := pc (pw (Nat.mod k 2) (VxT 2)) (pw (Nat.div k 2) (VxT 3))

@[expose] noncomputable def FKc (k : Nat) : Nat := pc (pw (Nat.mod k 2) (VxT 4)) (pw (Nat.div k 2) (VxT 5))

@[expose] noncomputable def CFc (k : Nat) : Nat := pc (pc (pc (VxT 2) (FKc k)) (VxI 2)) (pinv (FKc k))

@[expose] noncomputable def κK (q : Q1M) : Nat :=
  pc (pc (EKc q.a.code.val) (FKc q.b.code.val)) (CFc (q.c + q.a * q.b).code.val)

@[expose] noncomputable def conjV (j : Nat) (α : MulAut Q1M) : Bool :=
  gensQ1M.all fun g => Nat.beq (pc (pc (VxT j) (VxK (q1mIdx g))) (VxI j)) (VxK (q1mIdx (α g)))

@[expose] noncomputable def bindV (G GI : Nat → Nat) (ix : List Nat) : Bool :=
  allN ix.length (fun j => bAnd(Nat.beq (G j) idK, Nat.beq (GI j) (VxT (ix.getD j 0))))

theorem vx_base : (Nat.beq (VxT 0) (wC [2, 1, 2]) && Nat.beq (VxT 1) (wC [4, 4]) &&
    Nat.beq (VxT 2) (wC [3, 2, 3, 3]) && Nat.beq (VxT 3) (wC [2, 3, 3, 3]) &&
    Nat.beq (VxT 4) (wC [2, 1, 2]) && Nat.beq (VxT 5) (wC [1, 4, 3, 4, 3, 2]) &&
    Nat.beq (VxT 6) (wC [2, 3]) && Nat.beq (VxT 7) (wC [1, 2, 4, 2, 1, 4]) &&
    Nat.beq (VxT 8) (wP [1, 2, 1, 2, 1, 2, 2, 1, 2, 2]) && Nat.beq (VxT 9) wR &&
    allN 10 (fun j => invV (VxT j) (VxI j)) &&
    allN 4 (fun k => invV (FKc k) (pinv (FKc k))) &&
    Nat.beq (pc (VxT 0) (VxT 0)) idK && Nat.beq (pw 3 (VxT 1)) idK &&
    Nat.beq (pw 5 (pc (VxT 0) (VxT 1))) idK &&
    Nat.beq (pw 3 (VxT 6)) idK && Nat.beq (pw 2 (VxT 7)) idK &&
    Nat.beq (pc (VxT 7) (VxT 6)) (pc (VxT 6) (VxT 7)) &&
    conjV 6 βM && conjV 9 ρM && conjV 7 τM && sK (VxT 9) &&
    allN 64 (fun i => Nat.beq (VxK i) (κK (q1mAt i))) &&
    allN 64 (fun i => decide (q1mAt i = 1) || bIf(Nat.beq (VxK i) idK, false, true)) &&
    Nat.beq VxA.cnt 60 && bindV VxA.G VxA.GI [0, 1] && penumHdK idK VxA.cnt 200 VxA.T VxA.PL &&
    Nat.beq VxB.cnt 128 && bindV VxB.G VxB.GI [2, 3, 4, 5, 7] &&
    penumHdK idK VxB.cnt 200 VxB.T VxB.PL &&
    Nat.beq VxC.cnt 18 && bindV VxC.G VxC.GI [9, 6, 7] && penumHdK idK VxC.cnt 100 VxC.T VxC.PL &&
    Nat.beq VxX.cnt 1152 && bindV VxX.G VxX.GI [2, 3, 4, 5, 9, 6, 7] &&
    penumHdK idK VxX.cnt 3000 VxX.T VxX.PL) = true := by
  quickRfl

@[expose] noncomputable def vxB1 (i : Nat) : Bool :=
  allN 64 (fun j => Nat.beq (VxK (q1mIdx (q1mAt i * q1mAt j))) (pc (VxK i) (VxK j)))

@[expose] noncomputable def invOf (ix : List Nat) (j : Nat) : Nat := VxI (ix.getD j 0)

@[expose] noncomputable def vxA (_ : Nat) : Bool :=
  bAnd(penumSlK 315 9 (mask 9) (315 * 9) true VxA.G VxA.GI 2 VxA.cnt VxA.T VxA.PL VxA.POS VxA.SRT
    VxA.SRI 0 60,
  bAnd(slK VxA.cnt (hsortPtK 315 9 (mask 9) VxA.cnt VxA.T VxA.HS VxA.HSI) 0 60,
    slK (Nat.mul VxA.cnt 4) (findPtK VxA.cnt VxA.T
      (prodQK 315 9 (mask 9) 4 VxA.T (bothK 2 VxA.GI (invOf [0, 1]))) VxACl) 0 240))

@[expose] noncomputable def vxC (_ : Nat) : Bool :=
  bAnd(penumSlK 315 9 (mask 9) (315 * 9) true VxC.G VxC.GI 3 VxC.cnt VxC.T VxC.PL VxC.POS VxC.SRT
    VxC.SRI 0 18,
  bAnd(slK VxC.cnt (hsortPtK 315 9 (mask 9) VxC.cnt VxC.T VxC.HS VxC.HSI) 0 18,
    slK (Nat.mul VxC.cnt 6) (findPtK VxC.cnt VxC.T
      (prodQK 315 9 (mask 9) 6 VxC.T (bothK 3 VxC.GI (invOf [9, 6, 7]))) VxCCl) 0 108))

@[expose] noncomputable def vxPB (k : Nat) : Bool :=
  bAnd(penumSlK 315 9 (mask 9) (315 * 9) true VxB.G VxB.GI 5 VxB.cnt VxB.T VxB.PL VxB.POS VxB.SRT
    VxB.SRI (Nat.mul 64 k) 64,
  slK VxB.cnt (hsortPtK 315 9 (mask 9) VxB.cnt VxB.T VxB.HS VxB.HSI) (Nat.mul 64 k) 64)

@[expose] noncomputable def vxClB (k : Nat) : Bool :=
  slK (Nat.mul VxB.cnt 10) (findPtK VxB.cnt VxB.T
    (prodQK 315 9 (mask 9) 10 VxB.T (bothK 5 VxB.GI (invOf [2, 3, 4, 5, 7]))) VxBCl)
    (Nat.mul 640 k) 640

@[expose] noncomputable def vxPX (k : Nat) : Bool :=
  bAnd(penumSlK 315 9 (mask 9) (315 * 9) true VxX.G VxX.GI 7 VxX.cnt VxX.T VxX.PL VxX.POS VxX.SRT
    VxX.SRI (Nat.mul 64 k) 64,
  slK VxX.cnt (hsortPtK 315 9 (mask 9) VxX.cnt VxX.T VxX.HS VxX.HSI) (Nat.mul 64 k) 64)

@[expose] noncomputable def vxClX (k : Nat) : Bool :=
  slK (Nat.mul VxX.cnt 14) (findPtK VxX.cnt VxX.T
    (prodQK 315 9 (mask 9) 14 VxX.T (bothK 7 VxX.GI (invOf [2, 3, 4, 5, 9, 6, 7]))) VxXCl)
    (Nat.mul 896 k) 896

end CertificateChecks.KernelSpor.J2Vtx

end

set_option maxRecDepth 400000
set_option Elab.async false

#kc_each CertificateChecks.KernelSpor.J2Vtx.vxB1 0 64
#kc_each CertificateChecks.KernelSpor.J2Vtx.vxA 0 1
#kc_each CertificateChecks.KernelSpor.J2Vtx.vxC 0 1
#kc_each CertificateChecks.KernelSpor.J2Vtx.vxPB 0 2
#kc_each CertificateChecks.KernelSpor.J2Vtx.vxClB 0 2
#kc_each CertificateChecks.KernelSpor.J2Vtx.vxPX 0 18
#kc_each CertificateChecks.KernelSpor.J2Vtx.vxClX 0 18
