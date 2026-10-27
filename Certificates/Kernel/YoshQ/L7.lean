module

public import Certificates.Kernel.YoshQ.DataN
public import Certificates.Kernel.YoshQ.DataW
public import Certificates.Kernel.YoshQ.DataM
public import Certificates.Data.Kernel.YoshQ.Fast
import Certificates.Kernel.YoshQ.RecN
import CFSG.Certificates.Kernel.YoshQ.FastSound

public section

set_option maxRecDepth 100000

namespace CertificateChecks.KernelYoshQ

open CFSG.KC.YoshQ CFSG.EvenSporadicStandard.M12Std.Yosh

set_option maxHeartbeats 0

@[expose] def W7_0 : List Nat := [
  0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 25, 0, 0, 0, 172, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
  15, 175, 22, 0, 0, 196, 0, 72, 472, 806, 26, 2872, 4444, 334, 49, 0, 0, 1, 320, 179, 4, 0, 1362,
  817, 1381, 0, 0, 5047, 2860, 0, 0, 1906, 802, 0, 76, 0, 0, 331, 0, 0, 0, 0, 0, 0, 0, 0, 818, 176,
  0, 3809, 29, 160, 319, 1724, 197, 0, 0, 803, 473, 0, 0, 1382, 335, 2861, 56, 2873, 2, 0, 0, 3821,
  5, 0, 0, 1903, 799, 0, 21, 1727, 77, 161, 338, 0, 798, 0, 330, 0, 0, 0, 171, 0, 0, 0, 0, 0, 0, 0,
  0]

@[expose] def V7_0 : List Nat := [
  0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 20533, 0, 0, 0, 20746, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
  0, 5, 20766, 21433, 0, 0, 20747, 0, 24, 21054, 16443, 16437, 20480, 20482, 20952, 21749, 0, 0,
  21444, 16401, 16652, 21760, 0, 454, 20538, 20591, 0, 0, 20516, 20487, 0, 0, 21132, 20768, 0,
  20628, 0, 0, 20934, 0, 0, 0, 0, 0, 0, 0, 0, 16449, 16651, 0, 16385, 17341, 20488, 20497, 16536,
  16656, 0, 0, 16442, 16963, 0, 0, 16500, 16839, 16384, 17657, 16393, 17337, 0, 0, 16402, 17653, 0,
  0, 20654, 20537, 0, 7, 16537, 16532, 16392, 16840, 0, 266, 0, 110, 0, 0, 0, 57, 0, 0, 0, 0, 0, 0,
  0, 0]

theorem l7fv_0 : l7fV N10.cnt N10.EP 56426 N10.GS N10.RL 1 0 (nTN N10.GS (swN eWord))
      (nTN N10.GS (swN uWord)) E10.RL W7_0 V7_0 21444 17337 = true ∧
    E10.RL.filter (memH 56426 (goodTabsN N10.GS N10.RL 1 0)) = GE10.GS := by
  decide +kernel

theorem l7f_0 : l7FusionN N10.RL (goodTabsN N10.GS N10.RL 1 0) (nTN N10.GS (swN eWord))
    (nTN N10.GS (swN uWord)) E10.RL = true :=
  l7FusionN_of_V n10_rec.2.1 l7fv_0.1

@[expose] def W7_1 : List Nat := [
  0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 25, 0, 0, 0, 172, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
  15, 175, 22, 0, 0, 196, 0, 72, 472, 806, 26, 2884, 4465, 334, 49, 0, 0, 1, 320, 179, 4, 0, 1362,
  817, 1381, 0, 0, 5083, 2869, 0, 0, 1906, 802, 0, 76, 0, 0, 331, 0, 0, 0, 0, 0, 0, 0, 0, 818, 176,
  0, 3821, 29, 160, 319, 1724, 197, 0, 0, 803, 473, 0, 0, 1382, 335, 2870, 56, 2885, 2, 0, 0, 3836,
  5, 0, 0, 1903, 799, 0, 21, 1727, 77, 161, 338, 0, 798, 0, 330, 0, 0, 0, 171, 0, 0, 0, 0, 0, 0, 0,
  0]

@[expose] def V7_1 : List Nat := [
  0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 20746, 0, 0, 0, 20533, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
  0, 5, 20747, 21448, 0, 0, 20766, 0, 24, 21069, 16392, 16652, 20487, 20504, 20935, 21765, 0, 0,
  21436, 16496, 16437, 21753, 0, 454, 20768, 20954, 0, 0, 20484, 20480, 0, 0, 20655, 20538, 0,
  21053, 0, 0, 20586, 0, 0, 0, 0, 0, 0, 0, 0, 16442, 16656, 0, 16402, 17340, 20537, 20590, 16541,
  16651, 0, 0, 16449, 16958, 0, 0, 16495, 16844, 16393, 17657, 16384, 17345, 0, 0, 16385, 17662, 0,
  0, 20511, 20488, 0, 7, 16409, 16959, 16443, 16490, 0, 266, 0, 110, 0, 0, 0, 57, 0, 0, 0, 0, 0, 0,
  0, 0]

theorem l7fv_1 : l7fV N11.cnt N11.EP 56426 N11.GS N11.RL 1 1 (nTN N11.GS (swN eWord))
      (nTN N11.GS (swN uWord)) E11.RL W7_1 V7_1 21436 17345 = true ∧
    E11.RL.filter (memH 56426 (goodTabsN N11.GS N11.RL 1 1)) = GE11.GS := by
  decide +kernel

theorem l7f_1 : l7FusionN N11.RL (goodTabsN N11.GS N11.RL 1 1) (nTN N11.GS (swN eWord))
    (nTN N11.GS (swN uWord)) E11.RL = true :=
  l7FusionN_of_V n11_rec.2.1 l7fv_1.1

theorem l7s : l7SylowN (nTN N10.GS (swN cWord)) (nTN N10.GS (swN eWord)) (nTN N10.GS (swN uWord))
      E10.RL S10.RL = true ∧
    l7SylowN (nTN N11.GS (swN cWord)) (nTN N11.GS (swN eWord)) (nTN N11.GS (swN uWord))
      E11.RL S11.RL = true := by decide +kernel

@[expose] def VA_0 : List Nat := [
  8192, 2, 111, 16384]

theorem l7av_0 : l7AV N10.cnt N10.EP 56426 N10.GS N10.RL 1 0 (nTN N10.GS (swN cWord))
    A10.GS A10.RL E10.RL S10.RL VA_0 = true := by
  decide +kernel

theorem l7a_0 : l7AN (badTabsN N10.GS N10.RL 1 0) (nTN N10.GS (swN cWord)) A10.GS A10.RL E10.RL
    S10.RL = true :=
  l7AN_of_V n10_rec.2.1 l7av_0

@[expose] def VA_1 : List Nat := [
  8192, 2, 111, 16428]

theorem l7av_1 : l7AV N11.cnt N11.EP 56426 N11.GS N11.RL 1 1 (nTN N11.GS (swN cWord))
    A11.GS A11.RL E11.RL S11.RL VA_1 = true := by
  decide +kernel

theorem l7a_1 : l7AN (badTabsN N11.GS N11.RL 1 1) (nTN N11.GS (swN cWord)) A11.GS A11.RL E11.RL
    S11.RL = true :=
  l7AN_of_V n11_rec.2.1 l7av_1

theorem l7v : l7VN N10.RL (vWords.map fun W => nTN N10.GS (swN W)) = true ∧
    l7VN N11.RL (vWords.map fun W => nTN N11.GS (swN W)) = true ∧
    ((badChains 1 0).all fun c => c.1 == [1, 1]) = true ∧
    ((badChains 1 1).all fun c => c.1 == [1, 1]) = true := by decide +kernel

theorem l7ge : E10.RL.filter (memN 16 5 (goodTabsN N10.GS N10.RL 1 0)) = GE10.GS ∧
    E11.RL.filter (memN 16 5 (goodTabsN N11.GS N11.RL 1 1)) = GE11.GS :=
  ⟨(filter_memN_good_of_V n10_rec.2.1 (goodV_of_l7fV l7fv_0.1)).trans l7fv_0.2,
    (filter_memN_good_of_V n11_rec.2.1 (goodV_of_l7fV l7fv_1.1)).trans l7fv_1.2⟩

end CertificateChecks.KernelYoshQ

end
