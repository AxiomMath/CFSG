module

public import Certificates.Kernel.GammaU.Census1Data
import CFSG.Certificates.Kernel.Common.EachTrue
import CFSG.Certificates.Kernel.Common.ForallChunks

set_option maxRecDepth 100000

public section

#kc_each CFSG.KD.GUC1 cc16966b_blk (fun c => CFSG.KD.GUC1.blk c) 0 24
#kc_each CFSG.KD.GUC1 cc16966b_orb (fun q => CFSG.KD.GUC1.orb q) 0 11
#kc_each CFSG.KD.GUC1 cc16966b_k0b (fun c => CFSG.KD.GUC1.kblk (nat_lit 0) c) 0 3
#kc_each CFSG.KD.GUC1 cc16966b_k1b (fun c => CFSG.KD.GUC1.kblk (nat_lit 1) c) 0 1
#kc_each CFSG.KD.GUC1 cc16966b_k2b (fun c => CFSG.KD.GUC1.kblk (nat_lit 2) c) 0 1
#kc_each CFSG.KD.GUC1 cc16966b_k3b (fun c => CFSG.KD.GUC1.kblk (nat_lit 3) c) 0 1
#kc_each CFSG.KD.GUC1 cc16966b_k4b (fun c => CFSG.KD.GUC1.kblk (nat_lit 4) c) 0 1
#kc_each CFSG.KD.GUC1 cc16966b_k5b (fun c => CFSG.KD.GUC1.kblk (nat_lit 5) c) 0 1
#kc_each CFSG.KD.GUC1 cc16966b_klv (fun i => CFSG.KD.GUC1.klvl i) 0 6

namespace CFSG.KD.GUC1

open CFSG.KC.IF4C CFSG.KC.GUC

#kc_forall_chunks cc16966b_blkall (fun c => blk c = true) 24 CFSG.KD.GUC1.cc16966b_blk 1
#kc_forall_chunks cc16966b_orball (fun q => orb q = true) 11 CFSG.KD.GUC1.cc16966b_orb 1
#kc_forall_chunks cc16966b_k0all (fun c => kblk (nat_lit 0) c = true) 3 CFSG.KD.GUC1.cc16966b_k0b 1
#kc_forall_chunks cc16966b_klvall (fun i => klvl i = true) 6 CFSG.KD.GUC1.cc16966b_klv 1

theorem cc16966b_kgens : kgens = true := by decide +kernel

theorem cc16966b_inv :
    (invOK FT FTi 384 && invOK CS CSI NC && invOK CG CGI 160 &&
      Nat.beq (mulP TH (mulP TH TH)) idP) = true := by
  decide +kernel

theorem cc16966b_len :
    (Nat.beq (lenN ED) 384 && Nat.beq (lenN OR) 11 && Nat.beq (lenN CN) NC &&
      allBelow 384 (fun X => Nat.blt (fld FC X) 32)) = true := by
  decide +kernel

theorem cc16966b_lab : labOK LB 384 OR AR = true := by decide +kernel

theorem cc16966b_cn : cnOK CS CSI TH (five CG 1) CN 0 = true := by decide +kernel

end CFSG.KD.GUC1

end
