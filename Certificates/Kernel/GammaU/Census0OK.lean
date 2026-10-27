module

public import Certificates.Kernel.GammaU.Census0Data
import CFSG.Certificates.Kernel.Common.EachTrue
import CFSG.Certificates.Kernel.Common.ForallChunks

set_option maxRecDepth 100000

public section

#kc_each CFSG.KD.GUC0 cc16966a_blk (fun c => CFSG.KD.GUC0.blk c) 0 24
#kc_each CFSG.KD.GUC0 cc16966a_orb (fun q => CFSG.KD.GUC0.orb q) 0 11
#kc_each CFSG.KD.GUC0 cc16966a_k0b (fun c => CFSG.KD.GUC0.kblk (nat_lit 0) c) 0 3
#kc_each CFSG.KD.GUC0 cc16966a_k1b (fun c => CFSG.KD.GUC0.kblk (nat_lit 1) c) 0 1
#kc_each CFSG.KD.GUC0 cc16966a_k2b (fun c => CFSG.KD.GUC0.kblk (nat_lit 2) c) 0 1
#kc_each CFSG.KD.GUC0 cc16966a_k3b (fun c => CFSG.KD.GUC0.kblk (nat_lit 3) c) 0 1
#kc_each CFSG.KD.GUC0 cc16966a_k4b (fun c => CFSG.KD.GUC0.kblk (nat_lit 4) c) 0 1
#kc_each CFSG.KD.GUC0 cc16966a_k5b (fun c => CFSG.KD.GUC0.kblk (nat_lit 5) c) 0 1
#kc_each CFSG.KD.GUC0 cc16966a_klv (fun i => CFSG.KD.GUC0.klvl i) 0 6

namespace CFSG.KD.GUC0

open CFSG.KC.IF4C CFSG.KC.GUC

#kc_forall_chunks cc16966a_blkall (fun c => blk c = true) 24 CFSG.KD.GUC0.cc16966a_blk 1
#kc_forall_chunks cc16966a_orball (fun q => orb q = true) 11 CFSG.KD.GUC0.cc16966a_orb 1
#kc_forall_chunks cc16966a_k0all (fun c => kblk (nat_lit 0) c = true) 3 CFSG.KD.GUC0.cc16966a_k0b 1
#kc_forall_chunks cc16966a_klvall (fun i => klvl i = true) 6 CFSG.KD.GUC0.cc16966a_klv 1

theorem cc16966a_kgens : kgens = true := by decide +kernel

theorem cc16966a_inv :
    (invOK FT FTi 384 && invOK CS CSI NC && invOK CG CGI 160 &&
      Nat.beq (mulP TH (mulP TH TH)) idP) = true := by
  decide +kernel

theorem cc16966a_len :
    (Nat.beq (lenN ED) 384 && Nat.beq (lenN OR) 11 && Nat.beq (lenN CN) NC &&
      allBelow 384 (fun X => Nat.blt (fld FC X) 32)) = true := by
  decide +kernel

theorem cc16966a_lab : labOK LB 384 OR AR = true := by decide +kernel

theorem cc16966a_cn : cnOK CS CSI TH (five CG 0) CN 0 = true := by decide +kernel

end CFSG.KD.GUC0

end
