module

public import Certificates.Data.Kernel.U35Pk
import CFSG.Certificates.Kernel.Common.EachTrue
import CFSG.Certificates.Kernel.Common.ForallTree
import CFSG.Certificates.Kernel.Common.Harness

public section

namespace U35Pk

set_option maxRecDepth 100000

theorem ch7159k : constsOK = true := by quickRfl

theorem ch7159r : repsOK = true := by quickRfl

theorem ch7159n : nOK = true := by quickRfl

theorem ch7159l : lamOK = true := by quickRfl

theorem ch7159t : t0K = true := by quickRfl

theorem ch7159c0 : covC 2481 0 cov0 = true := by quickRfl

theorem ch7159c1 : covC 2455 2481 cov1 = true := by quickRfl

theorem ch7159c2 : covC 2627 4936 cov2 = true := by quickRfl

theorem ch7159c3 : covC 2306 7563 cov3 = true := by quickRfl

theorem ch7159c4 : covC 2340 9869 cov4 = true := by quickRfl

theorem ch7159c5 : covC 2628 12209 cov5 = true := by quickRfl

theorem ch7159c6 : covC 788 14837 cov6 = true := by quickRfl

#kc_each U35Pk ch7159g (fun k => gu2R (getK repW (k / 25)) (25 * (k % 25)) 25) 0 400

#kc_forall_tree ch7159gAll (fun k => gu2R (getK repW (k / 25)) (25 * (k % 25)) 25 = true) 400
  U35Pk.ch7159g

theorem covK_true : covK = true := by
  rw [covK, covW, covC_eq]
  have c0 := ch7159c0
  have c1 := ch7159c1
  have c2 := ch7159c2
  have c3 := ch7159c3
  have c4 := ch7159c4
  have c5 := ch7159c5
  have c6 := ch7159c6
  rw [covC_eq] at c0 c1 c2 c3 c4 c5 c6
  have h1 := covR_app _ _ _ 2481 0 _ _ 2455 c0 c1
  have h2 := covR_app _ _ _ 4936 0 _ _ 2627 h1 c2
  have h3 := covR_app _ _ _ 7563 0 _ _ 2306 h2 c3
  have h4 := covR_app _ _ _ 9869 0 _ _ 2340 h3 c4
  have h5 := covR_app _ _ _ 12209 0 _ _ 2628 h4 c5
  exact covR_app _ _ _ 14837 0 _ _ 788 h5 c6

theorem gu2All_true : allL repW gu2K = true := by
  have hlen : lenK repW = 16 := Nat.eq_of_beq_eq_true (by quickRfl)
  refine allL_of_get gu2K repW fun i hi => gu2K_of _ fun j hj => ?_
  rw [hlen] at hi
  have hk : 25 * i + j < 400 := by omega
  have h := ch7159gAll (25 * i + j) hk
  have e1 : (25 * i + j) / 25 = i := by omega
  have e2 : (25 * i + j) % 25 = j := by omega
  rwa [e1, e2] at h

theorem u35PkCheck_of (h1 : constsOK = true) (h2 : repsOK = true) (h3 : nOK = true)
    (h4 : lamOK = true) (h5 : t0K = true) (h6 : covK = true) (h7 : allL repW gu2K = true) :
    u35PkCheck = true := by
  unfold u35PkCheck
  rw [h1, h2, h3, h4, h5, h6, h7]

theorem u35PkCheck_true : u35PkCheck = true :=
  u35PkCheck_of ch7159k ch7159r ch7159n ch7159l ch7159t covK_true gu2All_true

noncomputable def onesB : Nat := Nat.div (Nat.sub (Nat.shiftLeft 1 162) 1) (Nat.sub (Nat.shiftLeft 1 18) 1)

theorem ch7159x1 : bIf(eltK onesB, false, true) = true := by quickRfl

theorem ch7159x2 :
    bIf(strictB (mulAB SA (aToB (getK nW 25))) (refK (getK nW 25) 3), false, true) = true := by
  quickRfl

theorem ch7159x3 : bIf(gu2R (bToA onesB) 1 1, false, true) = true := by quickRfl

theorem ch7159x4 :
    bIf(covC 2481 0 (List.rec (motive := fun _ => List Nat) [] (fun _ t _ => t) cov0), false, true)
      = true := by
  quickRfl

theorem ch7159x5 : bIf(unitK (bToA onesB), false, true) = true := by quickRfl

theorem ch7159x6 : bIf(nChk (bToA (dB 12)), false, true) = true := by quickRfl

theorem ch7159x7 : bIf(canA (Nat.add (getK repW 0) 5), false, true) = true := by quickRfl

theorem ch7159x8 :
    strictB (bToA (mulAB (getK repW 0) (y0B 494))) (fun ZA => strictB (mulAB ZA (dB 1)) fun XB =>
      strictB (bToA XB) fun XA => bIf(strictB (mulAB SA XB) (refK XA 5), false,
        bIf(strictB (mulAB RA XB) (refK XA 5), false, strictB (mulAB R2A XB) (refK XA 5))))
      = true := by
  quickRfl

end U35Pk

end
