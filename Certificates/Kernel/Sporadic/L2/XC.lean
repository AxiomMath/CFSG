module

public import Certificates.Kernel.Sporadic.L2.XC0
public import Certificates.Kernel.Sporadic.L2.XC1
public import Certificates.Kernel.Sporadic.L2.XC2
public import Certificates.Kernel.Sporadic.L2.Text
public import Certificates.Kernel.Sporadic.OddCore.SuzMGCG
public import Certificates.Kernel.Sporadic.OddCore.SuzTwCF
import CFSG.Certificates.Kernel.Common.Harness
import Mathlib.Tactic.IntervalCases

public section

set_option maxRecDepth 400000

#ks_rawchain_sl2_join CertificateChecks.KernelSpor.L2XC

namespace CertificateChecks.KernelSpor.L2XCG

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.Monster.B.Co2.Native
open CFSG.Sporadic.SuzRecog.LevelTwo CFSG.Sporadic.SuzRecog.LevelTwoData
open CertificateChecks.KernelSpor

theorem kS : allN 9 (fun j => Nat.beq (L2XC.S j) (L2XS.F j)) = true := by quickRfl

theorem kBase : allN 5 (fun t => Nat.beq xBase.toArray[t]! (pg 11 (mask 11) L2XC.BP t)) =
    true := by quickRfl

theorem kPerm : allN 9 (fun j => permOK 1782 11 (mask 11) (1782 * 11) (L2XC.S j)
    (L2XC.SI j)) = true := by quickRfl

theorem kOrb : (List.range 5).map (fun i => rcnt (L2XC.LR i)) = [162, 105, 64, 3, 3] := by
  decide +kernel

theorem negS : Bool.not (allN 9 (fun j => Nat.beq (Nat.xor (L2XC.S j) 1) (L2XS.F j))) = true := by
  quickRfl

theorem binds : Binds 1782 11 L2XC.S 9 5 L2XC.BP xStrongArrs xBase.toArray :=
  ⟨by norm_num, by norm_num, by norm_num, by simp [xStrongArrs],
    SuzMGCG.strong_bind L2XS.eq L2XS.all kS, by simp [xBase],
    fun t ht => Nat.eq_of_beq_eq_true (allN_spec kBase t ht)⟩

theorem gens_eq : gens = xStrongArrs.extract 0 2 := by
  apply Array.ext
  · simp [gens, xStrongArrs]
  · intro j h1 h2
    have hj : j < 2 := by simpa [gens] using h1
    interval_cases j <;> simp [gens, xStrongArrs]

theorem words_eq : xWords = CFSG.Sporadic.Schreier.Co3.Native.wordsArr 2 9 L2XCD.deriv :=
  wordsArr_eq (by simp [xWords]) (by norm_num)
    (fun j hj => by interval_cases j <;> rfl) (by simp only [L2XCD.deriv, Array.toArray_toList])

theorem chainOK_true : chainOK = true := by
  have hc := rawChainK_sound (chunks := 4) binds L2XC.head L2XC.hl (by norm_num) L2XC.hs
  rw [← words_eq, ← gens_eq] at hc
  unfold chainOK
  rw [hc, rawOrbitSizesK_sound binds kPerm L2XC.hl, kOrb]
  simp [xStrongArrs]

theorem memX_of {g : Array Nat} {G : Nat} (hg : g = unpack 1782 11 G)
    (hc : CFSG.KS.Prim.canonK 1782 11 (mask 11) (1782 * 11) G = true)
    (h : siftK 1782 11 (mask 11) (1782 * 11) (pidn 1782 11) L2XC.LR L2XC.TRI L2XC.BP 5 0 G = true) :
    memX g = true :=
  siftK_sound binds kPerm L2XC.hl hg (range_of_canonK hc) h

end CertificateChecks.KernelSpor.L2XCG

end
