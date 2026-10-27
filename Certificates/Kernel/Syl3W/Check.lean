module

public import Certificates.Kernel.Syl3W.Data
public import Certificates.Data.Kernel.Syl3W
public import Certificates.Data.Claims1310uSyl3
public import Certificates.Kernel.Misc.Perm.CharsCat

public section

open CFSG.KC.Syl3W
open CFSG.KC.BalanceSC (getL)
open CFSG.LocalAnalysis.GLTheoremB.MovingAround.Claims1310u

#ks_chars_cat CFSG.KD.Syl3W.MS syl3MatStr
#ks_chars_cat CFSG.KD.Syl3W.GS syl3GenMatStr

namespace CFSG.KD.Syl3W

set_option maxRecDepth 100000 in
theorem codesM : codesK (MS.chars.map Char.toNat) MP 2916 = true := by decide +kernel

theorem codesG : codesK (GS.chars.map Char.toNat) GP 144 = true := by decide +kernel

theorem tabB : (syl3TabArr.toList.map Fin.val ==
    (List.range 324).map fun m => ln7 TB m) = true := by decide +kernel

theorem wordsB : (syl3GenWordData.length == 81 && (syl3GenWordData.getD 0 []).isEmpty &&
    (List.range 81).all fun i => i == 0 ||
      (syl3GenWordData.getD i []).map Fin.val ==
        (syl3GenWordData.getD (getL 0 WP i) []).map Fin.val ++ [getL 0 WL i]) = true := by
  decide +kernel

theorem swB : (syl3SimpleWordData.map (List.map Fin.val) == SW) = true := by decide +kernel

theorem rfB : ((List.range 6).all fun s => (List.range 36).all fun e =>
    decide ((syl3ReflArr s).getD e 0 = ((ln (getL 0 RF s) e : Nat) : Int) - 100)) = true := by
  decide +kernel

theorem oneB : ((List.range 36).all fun e =>
    decide (syl3OneArr.getD e 0 = ((ln ONE e : Nat) : Int) - 100)) = true := by
  decide +kernel

theorem tab : tabK MP GP TB = true := by decide +kernel

theorem inv : invK GP ONE = true := by decide +kernel

theorem gen : genK RF ONE GP SW SG = true := by decide +kernel

theorem elt : eltK MP GP ONE (syl3GenWordData.map (List.map Fin.val)) SX = true := by
  decide +kernel

theorem mt : mtK MT TB WP WL = true := by decide +kernel

theorem fm : fmK MP FM = true := by decide +kernel

theorem p12 : p12K MT FM = true := by decide +kernel

theorem dist : distK MP = true := by decide +kernel

theorem nonab : Nat.beq (mulK MT 1 3) (mulK MT 3 1) = false := by decide +kernel

theorem prod_neg : prodOK (slot MP 1) (slot GP 0) (slot MP 1) = false := by decide +kernel

theorem mt_neg : mtK MT TB WP (WL.map fun l => (l + 1) % 4) = false := by decide +kernel

theorem fm_neg : fmK MP (FM.tail ++ FM.take 1) = false := by decide +kernel

theorem p12_neg : p12K MT (FM.map fun _ => 2 ^ 729 - 1) = false := by decide +kernel

theorem codes_neg : codesK (GS.chars.map Char.toNat) MP 144 = false := by decide +kernel

end CFSG.KD.Syl3W

end
