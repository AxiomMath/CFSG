module

public import Certificates.Kernel.LocalComp.Fi24TwoB.Kd15027
public import Certificates.Kernel.LocalComp.Fi24TwoB.Kdd15027
public import Certificates.Kernel.Sporadic.Fi24K.C2077
import CFSG.Certificates.Kernel.Common.Harness
import Mathlib.Tactic.NormNum

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelLC.Fi24B

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim
open CFSG.Certificates CFSG.Certificates.Native CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native
open CFSG.ComponentClassification.RankTwoSporadic.Fi24Prime CertificateChecks.KernelSpor.Fi24C
open CertificateChecks.KernelLC

theorem dRows : allN 16 (fun j => Nat.beq (Fi24BKd.S j) (pg 4536 (mask 4536) Fi24BT.Kd.F j)) =
    true := by quickRfl
theorem ddRows : allN 21 (fun j => Nat.beq (Fi24BKdd.S j) (pg 4536 (mask 4536) Fi24BT.Kdd.F j)) =
    true := by quickRfl
theorem dBase : allN 7 (fun t => Nat.beq fi24KdBase.toArray[t]! (pg 9 (mask 9) Fi24BKd.BP t)) =
    true := by quickRfl
theorem ddBase : allN 7 (fun t => Nat.beq fi24KddBase.toArray[t]! (pg 9 (mask 9) Fi24BKdd.BP t)) =
    true := by quickRfl
theorem permD : allN 16 (fun j => permOK 504 9 (mask 9) (504 * 9) (Fi24BKd.S j) (Fi24BKd.SI j)) =
    true := by quickRfl
theorem permDD : allN 21 (fun j =>
    permOK 504 9 (mask 9) (504 * 9) (Fi24BKdd.S j) (Fi24BKdd.SI j)) = true := by quickRfl

theorem dS : fi24KdStrong = SA 504 9 16 Fi24BKd.S := by
  rw [fi24KdStrong, Fi24BT.kd_eq]
  exact rowsOf_unpack (by norm_num) (by norm_num)
    fun j hj => Nat.eq_of_beq_eq_true (allN_spec dRows j hj)

theorem ddS : fi24KddStrong = SA 504 9 21 Fi24BKdd.S := by
  rw [fi24KddStrong, Fi24BT.kdd_eq]
  exact rowsOf_unpack (by norm_num) (by norm_num)
    fun j hj => Nat.eq_of_beq_eq_true (allN_spec ddRows j hj)

theorem bindsD : Binds 504 9 Fi24BKd.S 16 7 Fi24BKd.BP (SA 504 9 16 Fi24BKd.S)
    fi24KdBase.toArray :=
  ⟨by norm_num, by norm_num, by norm_num, by simp, fun j hj => ofFn_get hj, rfl,
    fun t ht => Nat.eq_of_beq_eq_true (allN_spec dBase t ht)⟩

theorem bindsDD : Binds 504 9 Fi24BKdd.S 21 7 Fi24BKdd.BP (SA 504 9 21 Fi24BKdd.S)
    fi24KddBase.toArray :=
  ⟨by norm_num, by norm_num, by norm_num, by simp, fun j hj => ofFn_get hj, rfl,
    fun t ht => Nat.eq_of_beq_eq_true (allN_spec ddBase t ht)⟩

theorem prodD : ((List.range 7).map fun i => rcnt (Fi24BKd.LR i)).prod = 40131624960 := by
  decide +kernel
theorem prodDD : ((List.range 7).map fun i => rcnt (Fi24BKdd.LR i)).prod = 40131624960 := by
  decide +kernel

theorem sizeD : fi24KdStrong.size = 16 := by rw [dS]; simp
theorem sizeDD : fi24KddStrong.size = 21 := by rw [ddS]; simp

theorem chainD : rawChainOK 504 (fi24KdStrong.extract 0 (min 5 fi24KdStrong.size)) fi24KdStrong
    fi24KdBase.toArray fi24KdWords 4 = true := by
  rw [sizeD, dS, Fi24BW.dW]
  exact rawChainK_sound (NS := 32) (CH := 16) bindsD Fi24BKd.head Fi24BKd.hl (by norm_num)
    Fi24BKd.hs

theorem chainDD : rawChainOK 504 (fi24KddStrong.extract 0 (min 10 fi24KddStrong.size))
    fi24KddStrong fi24KddBase.toArray fi24KddWords 4 = true := by
  rw [sizeDD, ddS, Fi24BW.ddW]
  exact rawChainK_sound (NS := 32) (CH := 16) bindsDD Fi24BKdd.head Fi24BKdd.hl (by norm_num)
    Fi24BKdd.hs

theorem sizesD : (rawOrbitSizes 504 fi24KdStrong fi24KdBase.toArray).prod = 40131624960 := by
  rw [dS, rawOrbitSizesK_sound bindsD permD Fi24BKd.hl, prodD]

theorem sizesDD : (rawOrbitSizes 504 fi24KddStrong fi24KddBase.toArray).prod = 40131624960 := by
  rw [ddS, rawOrbitSizesK_sound bindsDD permDD Fi24BKdd.hl, prodDD]

end CertificateChecks.KernelLC.Fi24B

end
