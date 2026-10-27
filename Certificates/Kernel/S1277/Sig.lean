module

public import Certificates.Data.Kernel.S1277KSig
public import Certificates.Kernel.S1277.SigData
public import CFSG.Certificates.Kernel.Common.Harness
public import CFSG.Certificates.Kernel.Common.Lce

public section

namespace CFSG.KP.S1277Sig

open CFSG.KC.S1277Sig CFSG.KD.S1277Sig

theorem sig_ok : sigAll sd sl sb sT = true := by quickRfl

theorem sigOrd_eq : sT.map (fun T => (T.map List.length).prod) = [1344, 1152, 40320, 576] := by
  decide +kernel

theorem neg_sig : CFSG.KC.notB (sigAll sd sl sb
    (sT.set 1 ((sT.getD 1 []).set 0 ((((sT.getD 1 []).getD 0 [])).drop 1)))) = true := by quickRfl

theorem neg_sig2 : CFSG.KC.notB (sigAll sd (sl.set 3 ((sl.getD 3 0) ^^^ 2 ^ 5)) sb sT) = true := by
  quickRfl

theorem neg_sig3 : CFSG.KC.notB (sigAll sd sl (sb.set 0 [1, 2, 4, 7]) sT) = true := by quickRfl

end CFSG.KP.S1277Sig

end
