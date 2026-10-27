module

public import Certificates.Data.Kernel.MonsterB.Rep4371Row
import CFSG.Certificates.Kernel.Common.Harness

public section

namespace CertificateChecks.Sq3022

open CFSG.KC.KDense CFSG.KC.Rep4371Row

@[expose] noncomputable def P1 : Nat := nat_lit 984818244535754528103549039458486304

@[expose] noncomputable def P6 : Nat := nat_lit 899228929685057613473567618418055332

@[expose] noncomputable def BT6 : Nat := nat_lit 79873156457113056204225129793389314108

theorem bt1 : betaTabT P1 = 0 := by decide +kernel

theorem bt6 : betaTabT P6 = BT6 := by decide +kernel

theorem k1 : kappaT 0 63 = 0 := by decide +kernel

theorem k6 : kappaT BT6 63 = 0 := by decide +kernel

theorem rows1 : sqRowsT 3 P1 0 0 0 0 0 = true := by quickRfl

theorem rows2 : sqRowsT 734 P1 0 0 1 63 0 = true := by quickRfl

theorem rows6 : sqRowsT 374 P6 BT6 0 0 0 0 = true := by quickRfl

end CertificateChecks.Sq3022

end
