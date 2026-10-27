module

public import CFSG.Certificates.Kernel.TwoNodeSmall.WitKSound
import Certificates.Kernel.TwoNodeSmall.Checks8
import Certificates.Kernel.TwoNodeSmall.Checks9
import Certificates.Kernel.TwoNodeSmall.Checks9m
import CFSG.Certificates.Kernel.Common.ForallChunks
public import CFSG.LocalAnalysis.StandardType.GGTwoNodeSmallRankDefs
public import Certificates.Kernel.TwoNodeSmall.Data

namespace CFSG.KD.TNS708603

#kc_forall_chunks all8 (fun k => CFSG.KD.TNS708603.c8 k = true) 90
  CFSG.KD.TNS708603.ch708603.p8_ 1
#kc_forall_chunks all9 (fun k => CFSG.KD.TNS708603.c9 k = true) 90
  CFSG.KD.TNS708603.ch708603.p9_ 1
#kc_forall_chunks all9m (fun k => CFSG.KD.TNS708603.c9m k = true) 90
  CFSG.KD.TNS708603.ch708603.p9m_ 1

open CFSG.TwoNodeSmall CFSG.TwoNodeSmall.WitK

theorem div3 {g s : Nat} (hs : s < 3) : (3 * g + s) / 3 = g := by omega

theorem mod3 {g s : Nat} (hs : s < 3) : (3 * g + s) % 3 = s := by omega

public section

public theorem closed_all :
    ∀ P ∈ pts8 () ++ pts9 () ++ pts9m (), ∀ [Fact P.p.Prime], P.Closed :=
  closed_of_chunks (w8 := w8) (w9 := w9) (w9m := w9m)
    (fun g hg s hs => by
      have h := groups_of_90 all8 g hg s hs
      simp only [c8, div3 hs, mod3 hs] at h
      exact h)
    (fun g hg s hs => by
      have h := groups_of_90 all9 g hg s hs
      simp only [c9, div3 hs, mod3 hs] at h
      exact h)
    (fun g hg s hs => by
      have h := groups_of_90 all9m g hg s hs
      simp only [c9m, div3 hs, mod3 hs] at h
      exact h)

end

end CFSG.KD.TNS708603
