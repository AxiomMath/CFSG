module

public import Certificates.Kernel.Fi23Nt.PosChkDefs
import CFSG.Certificates.Kernel.Common.EachTrue
import CFSG.Certificates.Kernel.BabyMonster.Load

#kc_each CFSG.KD.Fi23Nt tw101701ps (fun s => CFSG.KD.Fi23Nt.posSl s) 0 31
#bm_bool CFSG.KD.Fi23Nt tw101701pv (passV0)
#bm_bool CFSG.KD.Fi23Nt tw101701wk (wordsOK)
#bm_bool CFSG.KD.Fi23Nt tw101701dw (ddWOK)
#bm_bool CFSG.KD.Fi23Nt tw101701negPs (negPos)
#bm_bool CFSG.KD.Fi23Nt tw101701negRt (negRoot)
#bm_bool CFSG.KD.Fi23Nt tw101701negPv (negPassV0)
#bm_bool CFSG.KD.Fi23Nt tw101701negDw (negDdW)
