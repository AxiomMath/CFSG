module

public import Certificates.Kernel.YoshQ.DataN
public import Certificates.Kernel.YoshQ.DataW
public import Certificates.Data.Kernel.YoshQ.Fast
import Certificates.Kernel.YoshQ.RecN
import CFSG.Certificates.Kernel.YoshQ.FastSound

public section

set_option maxRecDepth 100000

namespace CertificateChecks.KernelYoshQ

open CFSG.KC.YoshQ CFSG.EvenSporadicStandard.M12Std.Yosh

set_option maxHeartbeats 0

@[expose] def W6_0 : List Nat := [
  0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 10,
  0, 0, 0, 0, 0, 0, 14, 0, 0, 1, 1061, 513, 0, 0, 0, 0, 0, 0, 123, 0, 0, 476, 201, 101, 0, 0, 517,
  515, 0, 0, 109, 103, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 17, 0, 0, 113, 491, 827, 0, 19, 0,
  0, 0, 53, 0, 0, 0, 35, 0, 213, 0, 111, 0, 0, 0, 211, 0, 0, 15, 61, 0, 48, 0, 5, 0, 219, 0, 816,
  0, 108, 0, 0, 0, 208, 0, 0, 0, 0, 0, 0, 0, 0]

theorem l6v_0 : l6V N00.cnt N00.EP 27880 N00.RL (goodTabsN N00.GS N00.RL 0 0)
    (nTN N00.GS (swN eWord)) E00.RL 41 W6_0 = true := by
  decide +kernel

theorem l6_0 : l6N N00.RL (goodTabsN N00.GS N00.RL 0 0) (nTN N00.GS (swN eWord)) E00.RL = true :=
  l6N_of_V n00_rec.2.1 l6v_0

@[expose] def W6_1 : List Nat := [
  0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 10,
  0, 0, 0, 0, 0, 0, 14, 0, 0, 1, 1061, 513, 0, 0, 0, 0, 0, 0, 123, 0, 0, 476, 201, 101, 0, 0, 517,
  515, 0, 0, 109, 103, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 17, 0, 0, 113, 491, 827, 0, 19, 0,
  0, 0, 53, 0, 0, 0, 35, 0, 213, 0, 111, 0, 0, 0, 211, 0, 0, 15, 61, 0, 48, 0, 5, 0, 219, 0, 816,
  0, 108, 0, 0, 0, 208, 0, 0, 0, 0, 0, 0, 0, 0]

theorem l6v_1 : l6V N01.cnt N01.EP 27880 N01.RL (goodTabsN N01.GS N01.RL 0 1)
    (nTN N01.GS (swN eWord)) E01.RL 41 W6_1 = true := by
  decide +kernel

theorem l6_1 : l6N N01.RL (goodTabsN N01.GS N01.RL 0 1) (nTN N01.GS (swN eWord)) E01.RL = true :=
  l6N_of_V n01_rec.2.1 l6v_1

end CertificateChecks.KernelYoshQ

end
