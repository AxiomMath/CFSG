module

public import Certificates.Kernel.Seitz.B45
public import CFSG.Certificates.Kernel.Common.Each
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSeitz

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KS.PEnum CFSG.KC.SeitzB45
open CFSG.PSL3Four.Native Certificates.Seitz77CaseB45

@[expose] noncomputable def invT : Nat → Nat := vB (B45A 0)
@[expose] noncomputable def repT : Nat → Nat := vB (B45A 1)
@[expose] noncomputable def rsT : Nat → Nat := rsB (B45A 3)

@[expose] noncomputable def mulK (c : Nat) : Bool :=
  allN 64 fun d => allN 256 fun j => bAnd(Nat.blt (mtT (64 * c + d) j) 256,
    Nat.beq (pcomp 42 6 (mask 6) (TLE.T (64 * c + d)) (TLE.T j)) (TLE.T (mtT (64 * c + d) j)))

@[expose] noncomputable def bindK : Bool :=
  (List.range 256).all (fun i => ((List.range 256).find? fun j => mtT i j == 0).getD 0 == invT i) &&
  (List.range 256).all (fun i =>
    isUT i == (List.range 64).any fun k => Nat.beq (UE.T k) (TLE.T i)) &&
  (List.range 64).all (fun k => (List.range 256).any fun i => Nat.beq (TLE.T i) (UE.T k)) &&
  (List.range 256).all (fun i =>
    ((List.range 256).find? fun j => isUT (mtT (invT j) i)).getD i == repT i) &&
  ((List.range 256).filter fun i => repT i == i) == [rsT 0, rsT 1, rsT 2, rsT 3] &&
  (List.range 256).all (fun i =>
    ([rsT 0, rsT 1, rsT 2, rsT 3].findIdx? (· == repT i)).getD 0 == labT i)

@[expose] noncomputable def tabK : Bool :=
  (allBelow 256 fun i => invT i < 256 && mtT i (invT i) == 0) &&
  (allBelow 256 fun i => labT i < 4) &&
  (allBelow 4 fun p => rsT p < 256 && labT (rsT p) == p) &&
  labT 0 == 0 &&
  (allBelow 256 fun i => allBelow 256 fun j => (labT i == labT j) == isUT (mtT (invT i) j)) &&
  (allBelow 256 fun i => allBelow 256 fun j => labT (mtT i j) == laddT (labT i) (labT j))

theorem t_hd : bAnd(gensK tlGens 42 6 TLE.k TLE.G, bAnd(Nat.beq TLE.cnt 256,
    penumHdK (pidn 42 6) TLE.cnt 256 TLE.T TLE.PL)) = true := by quickRfl

theorem t_sl : penumSlK 42 6 (mask 6) (42 * 6) false TLE.G TLE.GI TLE.k TLE.cnt TLE.T TLE.PL
    TLE.POS TLE.SRT TLE.SRI 0 256 = true := by quickRfl

theorem u_hd : bAnd(gensK uGens 42 6 UE.k UE.G, bAnd(Nat.beq UE.cnt 64,
    penumHdK (pidn 42 6) UE.cnt 64 UE.T UE.PL)) = true := by quickRfl

theorem u_sl : penumSlK 42 6 (mask 6) (42 * 6) false UE.G UE.GI UE.k UE.cnt UE.T UE.PL
    UE.POS UE.SRT UE.SRI 0 64 = true := by quickRfl

end CertificateChecks.KernelSeitz

#kc_each CertificateChecks.KernelSeitz.mulK 0 4

namespace CertificateChecks.KernelSeitz

open CFSG.KC.SeitzB45 Certificates.Seitz77CaseB45

theorem k_bind : bindK = true := by decide +kernel

theorem k_tab : tabK = true := by decide +kernel

theorem k_fb7 : fb7Check mtT isUT = true := by decide +kernel

theorem k_neg : ((List.range 256).all fun i => labT i == 0) = false := by decide +kernel

end CertificateChecks.KernelSeitz

end
