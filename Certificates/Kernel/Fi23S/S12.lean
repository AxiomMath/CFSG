module

public import Certificates.Kernel.Fi23S.S12Defs
import CFSG.Certificates.Kernel.BabyMonster.Load
public import Certificates.Kernel.Fi23R.ChkDefs

#bm_bool CFSG.KD.Fi23S s12K_ok (s12K)
#bm_bool CFSG.KD.Fi23S neg_s01
  (Bool.not (CFSG.KC.Fi23R.eqB CFSG.KD.Fi23K.G [(eS 1) (eS 0)] [(eS 0) (eS 1)]))
#bm_bool CFSG.KD.Fi23S neg_g4 (negG)
