module

public import Certificates.Kernel.Fi22Rk.Data
public import Certificates.Data.Kernel.Fi22Rk.Defs
import CFSG.Certificates.Kernel.Common.Harness
import CFSG.Certificates.Kernel.Common.Each

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelFi22Rk.K

open CFSG.KC.Enum CFSG.KC.Fi22Rk CertificateChecks.KernelFi22Rk

theorem rowsA : rowsK 3510 12 5 T.A.F D.AK = true := by quickRfl

theorem rowsG : rowsK 3510 12 2 T.G.F D.GK = true := by quickRfl

theorem rowsM : rowsK 243 8 2 T.M.F D.MUK = true := by quickRfl

theorem mult : multK 3510 12 D.AK = true := by quickRfl

theorem pow : powK 3510 12 D.AK D.PW = true := by quickRfl

theorem lay3 : layerK 3510 12 3 9 D.PW D.J3 (pw4 D.PW) = true := by quickRfl

theorem lay2 : layerK 3510 12 2 27 D.PW D.J2 D.J3 = true := by quickRfl

theorem lay1 : layerK 3510 12 1 81 D.PW D.J1 D.J2 = true := by quickRfl

@[expose] noncomputable def lay0 (c : Nat) : Bool :=
  allN (nat_lit 16) fun r => strictB (Nat.add (Nat.mul (nat_lit 16) c) r) fun i =>
    bIf(Nat.blt i (nat_lit 243), Nat.beq (D.IK i)
      (pc 3510 12 (D.PW (Nat.mod i (nat_lit 3))) (D.J1 (Nat.div i (nat_lit 3)))), true)

theorem inj : injK 12 8 D.IK D.SO = true := by quickRfl

theorem run : pbRunK D.MUK D.LK D.EK D.PLK D.SL = true := by quickRfl

@[expose] noncomputable def mtc (c : Nat) : Bool := mtC D.LK D.MTK c

theorem tree : treeK D.MUK D.LK D.PLK D.MTK D.FMK = true := by quickRfl

@[expose] noncomputable def fixc (c : Nat) : Bool :=
  allN (nat_lit 9) fun r => fixAt D.MTK D.FMK (Nat.add (Nat.mul (nat_lit 9) c) r)

theorem nonab : nonabK D.MTK = true := by quickRfl

open CFSG.KLie.CT (notB) in
theorem neg : bAnd(notB (rowsK 3510 12 5 T.A.F (fun k => D.AK (Nat.succ k))),
    bAnd(notB (powK 3510 12 D.AK (fun i => D.PW (Nat.succ i))),
    bAnd(notB (pbRunK D.MUK (fun k => nIf(Nat.beq k (nat_lit 5), D.LK 6, D.LK k)) D.EK D.PLK D.SL),
      notB (mtC D.LK (fun k => Nat.add (D.MTK k) (nat_lit 1)) (nat_lit 0))))) = true := by
  quickRfl

end CertificateChecks.KernelFi22Rk.K

#kc_each CertificateChecks.KernelFi22Rk.K.lay0 0 16
#kc_each CertificateChecks.KernelFi22Rk.K.mtc 0 9
#kc_each CertificateChecks.KernelFi22Rk.K.fixc 0 9

end
