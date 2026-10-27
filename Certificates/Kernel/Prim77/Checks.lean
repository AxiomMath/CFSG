module

public import Certificates.Data.Kernel.Prim77.Checks
public import Certificates.Kernel.Over77.Data
public import Certificates.Kernel.Misc.Perm.CharsCat
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Wilson.MaximalityAmbient.Prim77Data
import all Init.Data.List.SplitOn.Basic

public section

#ks_chars_cat CFSG.KD.Prim77.Tc CFSG.AGLEmbeddingD2.Wilson.MaximalityAmbient.Prim77.transText
#ks_chars_cat CFSG.KD.Prim77.Sc CFSG.AGLEmbeddingD2.Wilson.MaximalityAmbient.Prim77.stabText
#ks_chars_cat CFSG.KD.Prim77.Rc CFSG.AGLEmbeddingD2.Wilson.MaximalityAmbient.Prim77.repText

namespace CFSG.KD.Prim77

open CFSG.KC.Enum CFSG.KC.Over77 CFSG.KC.Prim77 CFSG.KD.Over77
open CFSG.AGLEmbeddingD2.Wilson.MaximalityAmbient.Over77 (dataS)
open CFSG.AGLEmbeddingD2.Wilson.MaximalityAmbient.Prim77 (w8Word)

theorem c12634base : (arK (nth S 0) dataS[0]! && arK (nth S 2) dataS[2]! &&
    arK (nth S 3) dataS[3]! && arK (nth S 4) dataS[4]!) = true := by decide +kernel

theorem c12634trans : letsB (nth S 0) (nth S 2) (fun a a2 c c4 =>
    optB (wordsO Tc.chars) (transK (let5 a a2 c c4))) = true := by decide +kernel

theorem c12634stab : letsB (nth S 0) (nth S 2) (fun a a2 c c4 =>
    optB (wordsO Sc.chars) (fun W => optB (natsO Rc.chars) (stabK (let5 a a2 c c4) W))) = true := by
  decide +kernel

theorem c12634ord : letsB (nth S 0) (nth S 2) (fun a a2 c c4 =>
    ordK a 3 && ordK c 5 && ordK (nth S 3) 7 && ordK (nth S 4) 11 &&
      strictB (wordK (let5 a a2 c c4) w8Word idP)
        (fun x => notIdK (powK x 4) && idK (powK x 8))) = true := by
  decide +kernel

theorem c12634negT : letsB (nth S 0) (nth S 2) (fun a a2 c c4 =>
    !optB (wordsO Sc.chars) (transK (let5 a a2 c c4))) = true := by decide +kernel

theorem c12634negS : letsB (nth S 0) (nth S 2) (fun a a2 c c4 =>
    !optB (wordsO Tc.chars) (fun W => optB (natsO Rc.chars) (stabK (let5 a a2 c c4) W))) = true := by
  decide +kernel

theorem c12634negO : (!ordK (nth S 0) 5) = true := by decide +kernel

theorem c12634negB : (!arK (nth S 0) dataS[2]!) = true := by decide +kernel

end CFSG.KD.Prim77

end
