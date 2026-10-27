module

public import Certificates.Kernel.GammaU.Sigma1Data
import CFSG.Certificates.Kernel.Common.EachTrue
import CFSG.Certificates.Kernel.Common.ForallChunks

set_option maxRecDepth 100000

public section

#kc_each CFSG.KD.GUS1 cs16981b0b (fun c => CFSG.KD.GUS1.blk (nat_lit 0) c) 0 2
#kc_each CFSG.KD.GUS1 cs16981b1b (fun c => CFSG.KD.GUS1.blk (nat_lit 1) c) 0 5
#kc_each CFSG.KD.GUS1 cs16981b2b (fun c => CFSG.KD.GUS1.blk (nat_lit 2) c) 0 1
#kc_each CFSG.KD.GUS1 cs16981b3b (fun c => CFSG.KD.GUS1.blk (nat_lit 3) c) 0 2
#kc_each CFSG.KD.GUS1 cs16981b4b (fun c => CFSG.KD.GUS1.blk (nat_lit 4) c) 0 1
#kc_each CFSG.KD.GUS1 cs16981blv (fun i => CFSG.KD.GUS1.lvl i) 0 5

namespace CFSG.KD.GUS1

open CFSG.KC.IF4C CFSG.KC.IF4R CFSG.KC.GUS
open CFSG.GF2Type.Smith1979.GammaU CFSG.GF2Type.Smith1979.GammaU.StepA
open CFSG.GF2Type.Smith1979.GammaU.SigmaP CFSG.GF2Type.Smith1979.GammaU.ResPair

#kc_forall_chunks cs16981b0all (fun c => blk (nat_lit 0) c = true) 2 CFSG.KD.GUS1.cs16981b0b 1
#kc_forall_chunks cs16981b1all (fun c => blk (nat_lit 1) c = true) 5 CFSG.KD.GUS1.cs16981b1b 1
#kc_forall_chunks cs16981b2all (fun c => blk (nat_lit 2) c = true) 1 CFSG.KD.GUS1.cs16981b2b 1
#kc_forall_chunks cs16981b3all (fun c => blk (nat_lit 3) c = true) 2 CFSG.KD.GUS1.cs16981b3b 1
#kc_forall_chunks cs16981b4all (fun c => blk (nat_lit 4) c = true) 1 CFSG.KD.GUS1.cs16981b4b 1

theorem cs16981b_gens : gens = true := by decide +kernel

theorem cs16981b_rows : ((n2Gens 1).all fun r => rowsOK r.toList) = true := by decide +kernel

theorem cs16981b_pairs :
    (pairsOK (commPairs 1) (lenN NG) && pairsOK (perfPairs 1) (lenN PG)) = true := by
  decide +kernel

theorem cs16981b_inv : invsOK NG NI = true := by decide +kernel

theorem cs16981b_sift : CFSG.KC.IF4R.recsOK T O 1 (fun _ => idP) TG QP = true := by
  decide +kernel

theorem cs16981b_rw : wordsG PG RW [look SP 0, look SP 1] = true := by decide +kernel

theorem cs16981b_dw : wordsG (dgP PG PI (perfPairs 1)) DW PG = true := by decide +kernel

theorem cs16981b_stab :
    (memN a0 (s45 1) && stabOK (NG ++ unpack NI (lenN NG)) (s45 1)) = true := by
  decide +kernel

theorem cs16981b_reach : reachOK NG a0 OL OT (s45 1) = true := by decide +kernel

theorem cs16981b_sigma : sigmaOK (s45 1) (sigmaBasis 1) (spanList (sigmaBasis 1)) = true := by
  decide +kernel

theorem cs16981b_oval : ovalOK (outPts 1) = true := by decide +kernel

theorem cs16981b_nc : ncOK C (sigmaBasis 1) (nthD 0 PG CG) = true := by decide +kernel

end CFSG.KD.GUS1

end
