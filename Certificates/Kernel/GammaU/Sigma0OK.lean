module

public import Certificates.Kernel.GammaU.Sigma0Data
import CFSG.Certificates.Kernel.Common.EachTrue
import CFSG.Certificates.Kernel.Common.ForallChunks

set_option maxRecDepth 100000

public section

#kc_each CFSG.KD.GUS0 cs16981a0b (fun c => CFSG.KD.GUS0.blk (nat_lit 0) c) 0 2
#kc_each CFSG.KD.GUS0 cs16981a1b (fun c => CFSG.KD.GUS0.blk (nat_lit 1) c) 0 5
#kc_each CFSG.KD.GUS0 cs16981a2b (fun c => CFSG.KD.GUS0.blk (nat_lit 2) c) 0 1
#kc_each CFSG.KD.GUS0 cs16981a3b (fun c => CFSG.KD.GUS0.blk (nat_lit 3) c) 0 2
#kc_each CFSG.KD.GUS0 cs16981a4b (fun c => CFSG.KD.GUS0.blk (nat_lit 4) c) 0 1
#kc_each CFSG.KD.GUS0 cs16981alv (fun i => CFSG.KD.GUS0.lvl i) 0 5

namespace CFSG.KD.GUS0

open CFSG.KC.IF4C CFSG.KC.IF4R CFSG.KC.GUS
open CFSG.GF2Type.Smith1979.GammaU CFSG.GF2Type.Smith1979.GammaU.StepA
open CFSG.GF2Type.Smith1979.GammaU.SigmaP CFSG.GF2Type.Smith1979.GammaU.ResPair

#kc_forall_chunks cs16981a0all (fun c => blk (nat_lit 0) c = true) 2 CFSG.KD.GUS0.cs16981a0b 1
#kc_forall_chunks cs16981a1all (fun c => blk (nat_lit 1) c = true) 5 CFSG.KD.GUS0.cs16981a1b 1
#kc_forall_chunks cs16981a2all (fun c => blk (nat_lit 2) c = true) 1 CFSG.KD.GUS0.cs16981a2b 1
#kc_forall_chunks cs16981a3all (fun c => blk (nat_lit 3) c = true) 2 CFSG.KD.GUS0.cs16981a3b 1
#kc_forall_chunks cs16981a4all (fun c => blk (nat_lit 4) c = true) 1 CFSG.KD.GUS0.cs16981a4b 1

theorem cs16981a_gens : gens = true := by decide +kernel

theorem cs16981a_rows : ((n2Gens 0).all fun r => rowsOK r.toList) = true := by decide +kernel

theorem cs16981a_pairs :
    (pairsOK (commPairs 0) (lenN NG) && pairsOK (perfPairs 0) (lenN PG)) = true := by
  decide +kernel

theorem cs16981a_inv : invsOK NG NI = true := by decide +kernel

theorem cs16981a_sift : CFSG.KC.IF4R.recsOK T O 1 (fun _ => idP) TG QP = true := by
  decide +kernel

theorem cs16981a_rw : wordsG PG RW [look SP 0, look SP 1] = true := by decide +kernel

theorem cs16981a_dw : wordsG (dgP PG PI (perfPairs 0)) DW PG = true := by decide +kernel

theorem cs16981a_stab :
    (memN a0 (s45 0) && stabOK (NG ++ unpack NI (lenN NG)) (s45 0)) = true := by
  decide +kernel

theorem cs16981a_reach : reachOK NG a0 OL OT (s45 0) = true := by decide +kernel

theorem cs16981a_sigma : sigmaOK (s45 0) (sigmaBasis 0) (spanList (sigmaBasis 0)) = true := by
  decide +kernel

theorem cs16981a_oval : ovalOK (outPts 0) = true := by decide +kernel

theorem cs16981a_nc : ncOK C (sigmaBasis 0) (nthD 0 PG CG) = true := by decide +kernel

end CFSG.KD.GUS0

end
