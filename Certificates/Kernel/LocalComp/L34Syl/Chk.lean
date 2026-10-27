module

public import Certificates.Kernel.LocalComp.L34Syl.Data
public import Certificates.Kernel.LocalComp.L34SChk
public import Certificates.Data.Kernel.L34FixPow
public import Certificates.Data.Kernel.L34Scan2
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelLC.L34Syl

open CFSG.KC.Enum CFSG.KS CFSG.KS.Prim CFSG.KS.Raw CFSG.KS.PEnum CFSG.KC.L34K CFSG.KC.L34FixPow
open CFSG.KC.L34Scan2 CertificateChecks.KernelLC.L34X CFSG.PSL3Four.Native
open CFSG.KLie.CT (andB orB notB)

@[expose] noncomputable def cenP (x : Nat) : Bool :=
  allN 64 fun j => commPt 42 6 x (L34SyP.T j)

@[expose] noncomputable def iv (i : Nat) : Nat := pg 6 (mask 6) (L34SyW.W i) 2

@[expose] noncomputable def wa (i : Nat) : Nat := pg 6 (mask 6) (L34SyW.W i) 0

@[expose] noncomputable def wb (i : Nat) : Nat := pg 6 (mask 6) (L34SyW.W i) 1

@[expose] noncomputable def comW (i : Nat) : Nat :=
  pcomp 42 6 (mask 6) (pcomp 42 6 (mask 6) (pcomp 42 6 (mask 6) (L34SyP.T (wa i)) (L34SyP.T (wb i)))
    (L34SyP.T (iv (wa i)))) (L34SyP.T (iv (wb i)))

@[expose] noncomputable def fusePt (n ni e x y : Nat) : Bool :=
  orB (Nat.beq x e) (orB (Nat.beq y e) (orB (Nat.beq x y)
    (orB (Nat.beq (pcomp 42 6 (mask 6) (pcomp 42 6 (mask 6) n x) ni) y)
      (Nat.beq (pcomp 42 6 (mask 6) (pcomp 42 6 (mask 6) ni x) n) y))))

@[expose] noncomputable def cenTail (r n ni e i x : Nat) : Bool :=
  andB (Nat.beq (pcomp 42 6 (mask 6) x x) e) (andB (commPt 42 6 x r)
    (andB (Nat.blt (wa i) 64) (andB (Nat.blt (wb i) 64) (andB (Nat.beq (comW i) x)
      (andB (memL 16 L34SyF.T x)
        (allN 64 fun j => strictB (L34SyP.T j) fun y => orB (notB (cenP y)) (fusePt n ni e x y)))))))

@[expose] noncomputable def sylPt (r n ni e i : Nat) : Bool :=
  strictB (L34SyP.T i) fun x =>
    andB (Nat.blt (iv i) 64) (andB (Nat.beq (pcomp 42 6 (mask 6) x (L34SyP.T (iv i))) e)
      (andB (fixPow x 4)
        (andB (memL 64 L34SyP.T (pcomp 42 6 (mask 6) (pcomp 42 6 (mask 6) r x) r))
          (andB (memL 64 L34SyP.T (pcomp 42 6 (mask 6) (pcomp 42 6 (mask 6) n x) ni))
            (andB (memL 64 L34SyP.T (pcomp 42 6 (mask 6) (pcomp 42 6 (mask 6) ni x) n))
              (orB (notB (cenP x)) (cenTail r n ni e i x)))))))

@[expose] noncomputable def sylF (e k : Nat) : Bool :=
  strictB (L34SyF.T k) fun y =>
    andB (memL 64 L34SyP.T y) (andB (Nat.beq (pcomp 42 6 (mask 6) y y) e)
      (allN 16 fun l => commPt 42 6 y (L34SyF.T l)))

@[expose] noncomputable def sylK : Bool :=
  strictB (pidn 42 6) fun e => strictB (RP 2) fun r => strictB (L34SyN.N 0) fun n =>
    strictB (L34SyN.N 1) fun ni =>
      andB (allN 4 fun j => memL 20160 CertificateChecks.KernelLC.L34S.T (L34SyP.G j))
        (andB (memL 20160 CertificateChecks.KernelLC.L34S.T n)
          (andB (canonK 42 6 (mask 6) (42 * 6) ni) (andB (Nat.beq (pcomp 42 6 (mask 6) n ni) e)
            (andB (Nat.beq (CFSG.KC.HeAutK.cntR (fun i => cenP (L34SyP.T i)) 0 64) 4)
              (andB (allN 64 fun i => sylPt r n ni e i) (allN 16 fun k => sylF e k))))))

theorem kSylP_gens : gensK pGens 42 6 4 L34SyP.G = true := by quickRfl
theorem kSylP_hd : penumHdK (pidn 42 6) 64 64 L34SyP.T L34SyP.PL = true := by quickRfl
theorem kSylP_sl : penumSlK 42 6 (mask 6) (42 * 6) false L34SyP.G L34SyP.GI 4 64 L34SyP.T L34SyP.PL
    L34SyP.POS L34SyP.SRT L34SyP.SRI 0 64 = true := by
  quickRfl

theorem kSylF_gens : gensK (fGens ()) 42 6 4 L34SyF.G = true := by quickRfl
theorem kSylF_hd : penumHdK (pidn 42 6) 16 16 L34SyF.T L34SyF.PL = true := by quickRfl
theorem kSylF_sl : penumSlK 42 6 (mask 6) (42 * 6) false L34SyF.G L34SyF.GI 4 16 L34SyF.T L34SyF.PL
    L34SyF.POS L34SyF.SRT L34SyF.SRI 0 16 = true := by
  quickRfl

theorem kSylN_gens : gensK #[nT] 42 6 1 L34SyN.N = true := by quickRfl

theorem kSyl : sylK = true := by quickRfl

end CertificateChecks.KernelLC.L34Syl

end
