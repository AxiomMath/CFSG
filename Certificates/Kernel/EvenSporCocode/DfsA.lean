module

public import Certificates.Kernel.EvenSporCocode.Data
public meta import CFSG.Certificates.Kernel.Common.Each
public import CFSG.Certificates.Kernel.Common.Each
public import Certificates.Data.Kernel.RangeSplit
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxHeartbeats 0

namespace CertificateChecks.KernelCocode

open CFSG.KC.EvenSporCocode CFSG.KC.RangeSplit CFSG.EvenSporadicStandard.Induction.Balance.Cocode24

theorem dfsF0_0 : (((D.IV.drop (16 * nat_lit 0)).take 16).take 4).all
    (fun c => !validExt (lookK D.RB) [0] c ||
      dfsK (lookK D.RB) (colsK D.LT) 9 (extV (lookK D.RB) [0] c) (extFK (colsK D.LT) (List.range 4096) c)
        (extC (lookK D.RB) D.IV c)) = true := by
  quickRfl

theorem dfsF0_1 : ((((D.IV.drop (16 * nat_lit 0)).take 16).drop 4).take 4).all
    (fun c => !validExt (lookK D.RB) [0] c ||
      dfsK (lookK D.RB) (colsK D.LT) 9 (extV (lookK D.RB) [0] c) (extFK (colsK D.LT) (List.range 4096) c)
        (extC (lookK D.RB) D.IV c)) = true := by
  quickRfl

theorem dfsF0_2 : (((((D.IV.drop (16 * nat_lit 0)).take 16).drop 4).drop 4).take 4).all
    (fun c => !validExt (lookK D.RB) [0] c ||
      dfsK (lookK D.RB) (colsK D.LT) 9 (extV (lookK D.RB) [0] c) (extFK (colsK D.LT) (List.range 4096) c)
        (extC (lookK D.RB) D.IV c)) = true := by
  quickRfl

theorem dfsF0_3 : (((((D.IV.drop (16 * nat_lit 0)).take 16).drop 4).drop 4).drop 4).all
    (fun c => !validExt (lookK D.RB) [0] c ||
      dfsK (lookK D.RB) (colsK D.LT) 9 (extV (lookK D.RB) [0] c) (extFK (colsK D.LT) (List.range 4096) c)
        (extC (lookK D.RB) D.IV c)) = true := by
  quickRfl

theorem dfsF0 : dfsF (nat_lit 0) = true := by
  unfold dfsF dfsSubK childrenSubK
  exact all_cut ((D.IV.drop (16 * nat_lit 0)).take 16) 4 dfsF0_0 (all_cut (((D.IV.drop (16 * nat_lit 0)).take 16).drop 4) 4 dfsF0_1 (all_cut ((((D.IV.drop (16 * nat_lit 0)).take 16).drop 4).drop 4) 4 dfsF0_2 (dfsF0_3)))

end CertificateChecks.KernelCocode

set_option maxHeartbeats 0 in
#kc_each CertificateChecks.KernelCocode.dfsF 1 6

end
