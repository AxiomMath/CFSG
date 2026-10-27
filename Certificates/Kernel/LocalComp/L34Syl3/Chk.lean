module

public import Certificates.Kernel.LocalComp.L34Syl3.Data
public import Certificates.Data.Kernel.L34Scan2
public import Certificates.Data.Kernel.L34W.Tab42
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelLC.L34Syl3

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KS.PEnum CFSG.KC.BfsPin CFSG.KC.L34K
open CFSG.KC.L34Scan2 CFSG.KC.L34W CFSG.ComponentClassification.GrSLit.L34Facts
open CFSG.KLie.CT (andB orB notB)

@[expose] noncomputable def fixT : Bool :=
  allN 64 fun i => strictB (L34PT.T i) fun t =>
    andB (Nat.beq (pg 6 (mask 6) t 2) 2) (Nat.beq (pg 6 (mask 6) t 23) 23)

theorem k22203f : fixT = true := by quickRfl

@[expose] noncomputable def normPt (NB x : Nat) : Bool :=
  orB (notB (allN 42 fun q => strictB (pg 6 (mask 6) x q) fun v =>
      orB (andB (notB (Nat.beq v 2)) (notB (Nat.beq v 23)))
        (Nat.beq (pg 6 (mask 6) (L34PT.G 0) q) q)))
    (memL NB L34PB.T x)

@[expose] noncomputable def normSl (NB L o : Nat) : Bool :=
  allN L fun i => strictB (L34S.T (Nat.add o i)) (normPt NB)

theorem k22203n0 : normSl 192 2520 (2520 * 0) = true := by quickRfl
theorem k22203n1 : normSl 192 2520 (2520 * 1) = true := by quickRfl
theorem k22203n2 : normSl 192 2520 (2520 * 2) = true := by quickRfl
theorem k22203n3 : normSl 192 2520 (2520 * 3) = true := by quickRfl
theorem k22203n4 : normSl 192 2520 (2520 * 4) = true := by quickRfl
theorem k22203n5 : normSl 192 2520 (2520 * 5) = true := by quickRfl
theorem k22203n6 : normSl 192 2520 (2520 * 6) = true := by quickRfl
theorem k22203n7 : normSl 192 2520 (2520 * 7) = true := by quickRfl

@[expose] noncomputable def centK (Z : List Nat) : Bool :=
  allN 64 fun k => strictB (tgK L34R.G k) fun t =>
    (allN 4 fun j => commPt 42 6 t (L34PT.G j)) == Z.contains k

theorem k22203c : centK [0, 4, 8, 12] = true := by quickRfl

@[expose] noncomputable def prodK (D : List (Nat × Nat × Nat)) : Bool :=
  D.all fun d =>
    Nat.beq (pcomp 42 6 (mask 6) (tgK L34R.G d.1) (tgK L34R.G d.2.1)) (tgK L34R.G d.2.2)

theorem k22203p : prodK prodData = true := by quickRfl

theorem kU1_gens : gensK (wordTabs wU₁) 42 6 4 L34SyU1.G = true := by quickRfl
theorem kU1_hd : penumHdK (pidn 42 6) 16 16 L34SyU1.T L34SyU1.PL = true := by quickRfl
theorem kU1_sl : penumSlK 42 6 (mask 6) (42 * 6) false L34SyU1.G L34SyU1.GI 4 16 L34SyU1.T
    L34SyU1.PL L34SyU1.POS L34SyU1.SRT L34SyU1.SRI 0 16 = true := by
  quickRfl

theorem kU2_gens : gensK (wordTabs wU₂) 42 6 4 L34SyU2.G = true := by quickRfl
theorem kU2_hd : penumHdK (pidn 42 6) 16 16 L34SyU2.T L34SyU2.PL = true := by quickRfl
theorem kU2_sl : penumSlK 42 6 (mask 6) (42 * 6) false L34SyU2.G L34SyU2.GI 4 16 L34SyU2.T
    L34SyU2.PL L34SyU2.POS L34SyU2.SRT L34SyU2.SRI 0 16 = true := by
  quickRfl

@[expose] noncomputable def memU (U : Nat → Nat) (a : Nat) : Bool :=
  allN 16 fun k => memL 16 U (tgK L34R.G (Nat.mul a k))

theorem k22203m : andB (memU L34SyU1.T 1) (memU L34SyU2.T 4) = true := by quickRfl

@[expose] noncomputable def pInv1 (j : Nat) : Nat := pinvS 42 6 (mask 6) (L34P1.G j)

@[expose] noncomputable def pInv2 (j : Nat) : Nat := pinvS 42 6 (mask 6) (L34P2.G j)

theorem k22203i : allN 3 (fun j =>
    andB (andB (canonK 42 6 (mask 6) (42 * 6) (pInv1 j))
      (Nat.beq (pcomp 42 6 (mask 6) (L34P1.G j) (pInv1 j)) (pidn 42 6)))
    (andB (canonK 42 6 (mask 6) (42 * 6) (pInv2 j))
      (Nat.beq (pcomp 42 6 (mask 6) (L34P2.G j) (pInv2 j)) (pidn 42 6)))) = true := by
  quickRfl

@[expose] noncomputable def normU (P PI UG UT : Nat → Nat) : Bool :=
  allN 3 fun j => allN 4 fun i =>
    andB (memL 16 UT (pcomp 42 6 (mask 6) (pcomp 42 6 (mask 6) (P j) (UG i)) (PI j)))
      (memL 16 UT (pcomp 42 6 (mask 6) (pcomp 42 6 (mask 6) (PI j) (UG i)) (P j)))

theorem k22203u : andB (normU L34P1.G pInv1 L34SyU1.G L34SyU1.T)
    (normU L34P2.G pInv2 L34SyU2.G L34SyU2.T) = true := by
  quickRfl

end CertificateChecks.KernelLC.L34Syl3

end
