module

public import Certificates.Kernel.Sol5Q.Data
import CFSG.Certificates.Kernel.Common.Harness

set_option maxRecDepth 100000

public section

namespace CFSG.KD.Sol5Q11

open CFSG.KC.Sol5Q

theorem ct : ctOK (nat_lit 11) S (nat_lit 2304) CT = true := by quickRfl

theorem h : hOK (nat_lit 11) E HB NH HG HPL = true := by quickRfl

theorem gens : gensK (nat_lit 11) E S HG = true := by quickRfl

theorem fcb : fcbK (nat_lit 11) E HB NH BN CT RB = true := by quickRfl

theorem fcr : fcrK (nat_lit 11) E S HB NH true BN CT RR GD = true := by quickRfl

theorem fco2 : fco2K (nat_lit 11) E HB NH true FO = true := by quickRfl

end CFSG.KD.Sol5Q11
