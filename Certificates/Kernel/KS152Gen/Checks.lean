module

public import Certificates.Kernel.KS152Gen.Data
public import Certificates.Data.Kernel.KS152Gen
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CFSG.KD.KS152Gen

open CFSG.KD.J2Five CFSG.KC.Enum CFSG.KS

theorem base_ok : bAnd(Nat.beq (lenN g0) 3, bAnd(eq (getN g0 2) (pm (getN g0 1) (getN g0 1)),
    eq (pm (getN g0 1) (pm (getN g0 1) (getN g0 1))) one)) = true := by
  quickRfl

theorem vals_ci : valsOK g0 gci gciw = true := by
  quickRfl

theorem vals_t : valsOK g0 tg tw = true := by
  quickRfl

theorem vals_s : valsOK g0 sg sw = true := by
  quickRfl

theorem vals_y : valsOK g0 [yg] [yw] = true := by
  quickRfl

theorem vals_f : valsOK g0 fg fw = true := by
  quickRfl

theorem vals_c : valsOK g0 gc gcw = true := by
  quickRfl

theorem invs_ok : bAnd(invsOK gc gci, bAnd(invsOK qg qgi, bAnd(cubeOK qg qgi,
    bAnd(eq (pm yg ygi) one, eq ygi (pm yg (pm yg (pm yg yg))))))) = true := by
  quickRfl

theorem t_ok : ckT tg tW tC ti0 xI qg = true := by
  quickRfl

theorem w_ok : ckW qg wW wC wi0 gc nI = true := by
  quickRfl

theorem s_ok : ckS sg sW sC si0 zi yg = true := by
  quickRfl

theorem f_ok : ckF yg fg aW aC ai0 kW kC ki0 = true := by
  quickRfl

theorem c_ok : ckC gc gci yg rec = true := by
  quickRfl

theorem g_ok : genOK (getN g0 0) (getN g0 1) yg ygi gc gci qg qgi aw bw = true := by
  quickRfl

end CFSG.KD.KS152Gen

end
