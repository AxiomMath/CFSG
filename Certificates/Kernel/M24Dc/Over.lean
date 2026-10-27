module

public import Certificates.Kernel.M24Dc.Final
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.SporLatM24Dc
public import CFSG.LocalAnalysis.QuasithinUnique.K1.EvenClassicalStrong
public import CFSG.Quasithin.Vol2.Ch8Sec2L822CovP3
public import CFSG.Sporadic.Th.F2Spec

public section

namespace CFSG.KD.M24Dc

open CFSG.Blueprint.NativeSporadic CFSG.QuasithinUnique.Ch1.SporLat

theorem card_of_sylow_le
    {T Y : Subgroup (Carrier .M24)} (hT : CFSG.QuasithinUnique.IsSylowTwoOf T ⊤) (hTY : T ≤ Y)
    (hY : Y ≠ ⊤) : Nat.card Y ∈ [1024, 322560, 64512, 138240, 21504, 9216, 3072] := by
  have hG : Nat.card (Carrier .M24) = 244823040 := CFSG.Sporadic.Mathieu.card_M24
  have : Finite (Carrier .M24) := Nat.finite_of_card_ne_zero (by rw [hG]; decide)
  rcases M24K.m24K_overgroups facts ⟨MulEquiv.refl _⟩ hT hTY with h | ⟨m, hm, hc, -⟩
  · exact absurd h hY
  · have hall : ∀ m ∈ M24.m24Mems, m.order ∈ [1024, 322560, 64512, 138240, 21504, 9216, 3072] := by
      decide
    rw [hc]
    exact hall m hm

end CFSG.KD.M24Dc

end
