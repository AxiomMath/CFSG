module

public import Certificates.Kernel.Ru7130.Codes
public import Certificates.Data.Kernel.Ru7130.Data
import CFSG.Certificates.Kernel.Common.Harness
public import Certificates.Data.Kernel.HSA312.Defs

set_option maxRecDepth 100000

public section

namespace CFSG.KD.Ru7130

open CFSG.KC.Enum CFSG.KC.LQT.PcW CFSG.Quasithin.A312S CFSG.Quasithin.A312S.Ru

@[expose] noncomputable def R (i : Nat) : Nat := J.R.getD i 0

theorem rQ : ((List.range ruQuot2.length).all fun i => Nat.beq (qtW 4060 12 4095 I Lc
    (ruQuot2.getD i default).w (ruQuot2.getD i default).k) (R i)) = true := by
  quickRfl

theorem rOrd : ((List.range ruQuot2.length).all fun i => [0, 1, 2, 3, 4].all fun b =>
    pg 12 4095 (powS 4060 12 4095 I (R i) (ruQuot2.getD i default).m) b == b) = true := by
  quickRfl

theorem kG : ((List.range ruKer.length).all fun i => Nat.beq (powS 4060 12 4095 I
    (wordPB 4060 12 4095 R (ruKer.getD i default).u I) (ruKer.getD i default).k) (J.K.getD i 0)) =
    true := by
  quickRfl

theorem kV : (J.K.all fun k => Vs.all fun v => pcS 4060 12 4095 k v == pcS 4060 12 4095 v k) =
    true := by
  quickRfl

end CFSG.KD.Ru7130

end
