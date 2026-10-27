module

public import Certificates.Data.Kernel.L34Graph
public import Certificates.Kernel.LocalComp.L34Para.Data
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelLC.L34P3

open CFSG.KC.Enum CFSG.KS CFSG.KS.Prim CFSG.KS.Raw CFSG.KC.BfsPin CFSG.KC.L34K CFSG.KC.L34W
open CFSG.KLie.CT (andB orB notB)

@[expose] noncomputable def p3InvK (G : Nat → Nat) : Bool :=
  allN 3 fun j => strictB (pinvS 42 6 (mask 6) (G j)) fun gi =>
    andB (canonK 42 6 (mask 6) (42 * 6) gi) (Nat.beq (pcomp 42 6 (mask 6) (G j) gi) (pidn 42 6))

@[expose] noncomputable def p3O2K (G : Nat → Nat) (inU : Nat → Bool) : Bool :=
  allN 64 fun k => orB (inU k) (strictB (tgK L34R.G k) fun t => notB (allN 3 fun j =>
    strictB (G j) fun g => notB (notInK 64 L34PT.T
      (pcomp 42 6 (mask 6) (pcomp 42 6 (mask 6) g t) (pinvS 42 6 (mask 6) g)))))

@[expose] noncomputable def p3TransK (N : Nat) (P : Nat → Nat) (inU : Nat → Bool) (k₀ : Nat) :
    Bool :=
  strictB (tgK L34R.G k₀) fun t0 => allN 64 fun k => orB (notB (inU k)) (orB (Nat.beq k 0)
    (strictB (tgK L34R.G k) fun t => notB (allN N fun i => strictB (P i) fun x =>
      notB (Nat.beq (pcomp 42 6 (mask 6) x t0) (pcomp 42 6 (mask 6) t x)))))

@[expose] noncomputable def p3ProdK (inU inV : Nat → Bool) : Bool :=
  CFSG.KC.L34Graph.forceL ((List.range 64).map (tgK L34R.G)) fun L =>
    allN 64 fun k => strictB (L.getD k 0) fun t => notB (allN 64 fun a => notB (andB (inU a)
      (strictB (L.getD a 0) fun ta => notB (allN 64 fun b => notB (andB (inV b)
        (Nat.beq (pcomp 42 6 (mask 6) ta (L.getD b 0)) t))))))

@[expose] noncomputable def p3NcK (a b : Nat) : Bool :=
  strictB (tgK L34R.G a) fun x => strictB (tgK L34R.G b) fun y =>
    notB (Nat.beq (pcomp 42 6 (mask 6) x y) (pcomp 42 6 (mask 6) y x))

theorem k7280i1 : p3InvK L34P1.G = true := by quickRfl

theorem k7280i2 : p3InvK L34P2.G = true := by quickRfl

theorem k7280o1 : p3O2K L34P1.G (fun k => decide (k < 16)) = true := by quickRfl

theorem k7280o2 : p3O2K L34P2.G (fun k => k % 4 == 0) = true := by quickRfl

theorem k7280t1 : p3TransK 960 L34P1.T (fun k => decide (k < 16)) 4 = true := by quickRfl

theorem k7280t2 : p3TransK 960 L34P2.T (fun k => k % 4 == 0) 4 = true := by quickRfl

theorem k7280p1 : p3ProdK (fun k => decide (k < 16)) (fun k => k % 4 == 0) = true := by quickRfl

theorem k7280p2 : p3ProdK (fun k => k % 4 == 0) (fun k => decide (k < 16)) = true := by quickRfl

theorem k7280n : p3NcK 1 16 = true := by quickRfl

end CertificateChecks.KernelLC.L34P3

end
