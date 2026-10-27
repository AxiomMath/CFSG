module

public import Certificates.Kernel.Fi24Rk.Data
public import Certificates.Data.Kernel.Fi22Rk.DefsN
import CFSG.Certificates.Kernel.Common.Harness
import CFSG.Certificates.Kernel.Common.Each

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelFi24Rk.K

open CFSG.KC.Enum CFSG.KC.Fi22Rk CertificateChecks.KernelFi24Rk
open CertificateChecks.KernelLC

theorem rowsA : rowsK 504 9 5 Fi24PlT.A.F D.AK = true := by quickRfl

theorem rowsG : rowsK 504 9 2 T.G.F D.GK = true := by quickRfl

theorem rowsM : rowsK 243 8 2 T.M.F D.MUK = true := by quickRfl

theorem mult : multK 504 9 D.AK = true := by quickRfl

theorem pow : powK 504 9 D.AK D.PW = true := by quickRfl

theorem lay3 : layerK 504 9 3 9 D.PW D.J3 (pw4 D.PW) = true := by quickRfl

theorem lay2 : layerK 504 9 2 27 D.PW D.J2 D.J3 = true := by quickRfl

theorem lay1 : layerK 504 9 1 81 D.PW D.J1 D.J2 = true := by quickRfl

@[expose] noncomputable def lay0 (c : Nat) : Bool :=
  allN (nat_lit 16) fun r => strictB (Nat.add (Nat.mul (nat_lit 16) c) r) fun i =>
    bIf(Nat.blt i (nat_lit 243), Nat.beq (D.IK i)
      (pc 504 9 (D.PW (Nat.mod i (nat_lit 3))) (D.J1 (Nat.div i (nat_lit 3)))), true)

theorem inj : injK 9 1 D.IK D.SO = true := by quickRfl

@[expose] noncomputable def conj0 (c : Nat) : Bool := conjC 504 9 D.GK D.MUK D.IK 0 c

@[expose] noncomputable def conj1 (c : Nat) : Bool := conjC 504 9 D.GK D.MUK D.IK 1 c

theorem run : pbRunKN 9 D.MUK D.LK D.EK D.PLK D.SL = true := by quickRfl

theorem mt : mtKN 9 D.LK D.MTK = true := by quickRfl

theorem tree : treeKN 9 D.MUK D.LK D.PLK D.MTK D.FMK = true := by quickRfl

theorem fix : allN 9 (fixAtN 9 D.MTK D.FMK) = true := by quickRfl

open CFSG.KLie.CT (notB) in
theorem neg : bAnd(notB (rowsK 504 9 5 Fi24PlT.A.F (fun k => D.AK (Nat.succ k))),
    bAnd(notB (powK 504 9 D.AK (fun i => D.PW (Nat.succ i))),
    bAnd(notB (pbRunKN 9 D.MUK (fun k => nIf(Nat.beq k (nat_lit 5), D.LK 6, D.LK k)) D.EK D.PLK
      D.SL),
    bAnd(notB (mtKN 9 D.LK (fun k => Nat.add (D.MTK k) (nat_lit 1))),
      notB (conjAt 504 9 D.GK (fun l => Nat.add (D.MUK l) (nat_lit 1)) D.IK 0 0))))) = true := by
  quickRfl

end CertificateChecks.KernelFi24Rk.K

#kc_each CertificateChecks.KernelFi24Rk.K.lay0 0 16
#kc_each CertificateChecks.KernelFi24Rk.K.conj0 0 16
#kc_each CertificateChecks.KernelFi24Rk.K.conj1 0 16

end
