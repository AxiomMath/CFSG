module

public import Certificates.Kernel.HS589207.ScanK
import CFSG.Certificates.Kernel.Spor.Loops
import CFSG.Certificates.Kernel.Spor.RawOrbEval

public section

namespace CFSG.KD.HS589207.Scans

open CFSG.KC.DcHSOutK CFSG.KC.Enum CFSG.KD.HS589207.ScanK

theorem slices {f : Nat → Bool} (h0 : allBlk 0 f 2880 = true) (h1 : allBlk 2880 f 2880 = true)
    (h2 : allBlk 5760 f 2880 = true) (h3 : allBlk 8640 f 2880 = true) :
    allN 11520 f = true := by
  rw [CFSG.KS.Raw.Orb.allN_iff]
  intro m hm
  have g : ∀ b, allBlk b f 2880 = true → b ≤ m → m < b + 2880 → f m = true := fun b h hb1 hb2 => by
    have := CFSG.KS.allBlk_spec h (m - b) (by omega)
    have e : Nat.add b (m - b) = m := by
      change b + (m - b) = m
      omega
    rwa [e] at this
  by_cases a : m < 2880
  · exact g 0 h0 (by omega) (by omega)
  by_cases b : m < 5760
  · exact g 2880 h1 (by omega) (by omega)
  by_cases c : m < 8640
  · exact g 5760 h2 (by omega) (by omega)
  · exact g 8640 h3 (by omega) (by omega)

theorem cent : allN 11520 (fun m => !(I0.all fun j => commF (mF m) (mF j)) || I0.contains m) =
    true := slices c0 c1 c2 c3

theorem out : allN 11520 (fun m => (I0.all fun j => commF (fun q => wF (mF m q)) (mF j)) ==
    IO.contains m) = true := slices o0 o1 o2 o3

end CFSG.KD.HS589207.Scans

end
