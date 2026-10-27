module

public import Certificates.Kernel.SporSch.PairHS.HS2272Fns
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSporSch.HS72

open CFSG.KC.Enum CFSG.KS CFSG.KS.SporSch CFSG.KS.HS2272

theorem neg_cf : bIf(cfL (nat_lit 3850) LP (tR (nat_lit 0))
    [(HSD.cf.getD 0 []).getD 0 [], (HSD.cf.getD 0 []).getD 0 []] (nat_lit 0), false, true) = true := by
  quickRfl

theorem neg_orb : bIf(orbL (nat_lit 3850) (LC (nat_lit 0)) [[nat_lit 0]]
    [(LC (nat_lit 0) (nat_lit 0) (nat_lit 0), nat_lit 0, nat_lit 0),
      (LC (nat_lit 0) (nat_lit 0) (nat_lit 0), nat_lit 0, nat_lit 0)] (nat_lit 1), false, true) =
    true := by
  quickRfl

theorem neg_even : bIf(evenOrd bsR (tR (nat_lit 0)) (nat_lit 3), false, true) = true := by
  quickRfl

theorem neg_sort : bIf(sortK (nat_lit 2) (fun i => Nat.sub (nat_lit 5) i) (fun i => i) (fun i => i),
    false, true) = true := by
  quickRfl

theorem neg_bind : bIf(eqBlk (nat_lit 0) (nat_lit 770) (tv (nat_lit 6))
    (nfp (bndAt (nat_lit 9)).2.1), false, true) = true := by
  quickRfl

theorem neg_ne : bIf(neL bsR (tR (nat_lit 1)) (tR (nat_lit 1)), false, true) = true := by
  quickRfl

theorem neg_data : bIf(Nat.beq (chainOrd (nat_lit 0)) (nat_lit 7681), false, true) = true := by
  quickRfl

theorem neg_s : bIf(sAt (nat_lit 1) (HSD.sw.getD 2 []) (HSD.sc.getD 1 (0, [])), false, true) =
    true := by
  quickRfl

end CertificateChecks.KernelSporSch.HS72

end
