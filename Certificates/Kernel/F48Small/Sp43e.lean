module

public import CFSG.Milestones.ASVolI.F48.Small.Sp43eInputs
public import Certificates.Data.Kernel.F48Small.Pack
public import Certificates.Kernel.SporSch.Th.GenStr
public import Certificates.Data.Kernel.DcK

public section

#kss_strof CertificateChecks.KernelF48S.Sp43eP1 CFSG.ASVolI.burnsideF48s_sp43eP1Str

set_option maxRecDepth 100000 in
#kss_strof CertificateChecks.KernelF48S.Sp43eP2 CFSG.ASVolI.burnsideF48s_sp43eP2Str

namespace CertificateChecks.KernelF48S

open CFSG.ASVolI CFSG.KC.F48S CFSG.KC.LQT.L

@[expose] noncomputable def wordsSp43e (cs : List Char) : List (List (Fin 5 × Bool)) :=
  (CFSG.KC.DcK.splitGo ' ' cs []).map fun l => l.map burnsideF48s_sp43eLetter

@[expose] noncomputable def ekSp43e (w : List (Fin 5 × Bool)) : ℕ :=
  evK 45 (burnsideF48s_sp43eLS.map encL) (burnsideF48s_sp43eLSi.map encL) w

@[expose] noncomputable def lettersSp43e : Bool :=
  ((wordsSp43e Sp43eP1.chars ++ burnsideF48s_sp43eR1 ++ burnsideF48s_sp43eU).all fun w =>
    w.all fun l => decide (l.1 ≠ 3)) &&
  ((wordsSp43e Sp43eP2.chars ++ burnsideF48s_sp43eR2 ++ burnsideF48s_sp43eV).all fun w =>
    w.all fun l => decide (l.1 ≠ 2)) &&
  ((burnsideF48s_sp43eKW ++ burnsideF48s_sp43eTW ++ burnsideF48s_sp43eW).all fun w =>
    w.all fun l => decide (l.1 ≠ 2 ∧ l.1 ≠ 3))

theorem lettersSp43e_ok : lettersSp43e = true := by decide +kernel

theorem gensSp43e_ok : burnsideF48s_sp43eCheckGens () = true := by decide +kernel

theorem relsSp43e_ok : burnsideF48s_sp43eCheckRels () = true := by decide +kernel

@[expose] noncomputable def closedSp43e : Bool :=
  decide ((wordsSp43e Sp43eP1.chars).length = 1296) &&
  decide ((wordsSp43e Sp43eP2.chars).length = 1296) &&
  decide ((wordsSp43e Sp43eP1.chars).getD 0 [(0, true)] = []) &&
  decide ((wordsSp43e Sp43eP2.chars).getD 0 [(0, true)] = []) &&
  decide (burnsideF48s_sp43eKW = [[], burnsideF48s_sp43eWord "f", burnsideF48s_sp43eWord "aaa",
    burnsideF48s_sp43eWord "aaaf"]) &&
  decide (burnsideF48s_sp43eU.length = 32) && decide (burnsideF48s_sp43eV.length = 32) &&
  decide (burnsideF48s_sp43eW.length = 32) &&
  closedK 45 (setT ((wordsSp43e Sp43eP1.chars).map ekSp43e)) ((wordsSp43e Sp43eP1.chars).map ekSp43e)
    ([0, 1, 2, 4].map (getK (burnsideF48s_sp43eLS.map encL))) &&
  closedK 45 (setT ((wordsSp43e Sp43eP2.chars).map ekSp43e)) ((wordsSp43e Sp43eP2.chars).map ekSp43e)
    ([0, 1, 3, 4].map (getK (burnsideF48s_sp43eLS.map encL))) &&
  closedK 45 (setT (burnsideF48s_sp43eKW.map ekSp43e)) (burnsideF48s_sp43eKW.map ekSp43e)
    ([burnsideF48s_sp43eWord "f", burnsideF48s_sp43eWord "aaa"].map ekSp43e)

theorem closedSp43e_ok : closedSp43e = true := by decide +kernel

@[expose] noncomputable def candSp43e : Bool :=
  candK 45 (setT ((wordsSp43e Sp43eP1.chars).map ekSp43e))
    (setT ((wordsSp43e Sp43eP2.chars).map ekSp43e))
    ((wordsSp43e Sp43eP1.chars).map ekSp43e) ((wordsSp43e Sp43eP2.chars).map ekSp43e)
    (burnsideF48s_sp43eKW.map ekSp43e) (burnsideF48s_sp43eTW.map ekSp43e)
    (uvwK (burnsideF48s_sp43eU.map ekSp43e) (burnsideF48s_sp43eV.map ekSp43e)
      (burnsideF48s_sp43eW.map ekSp43e) burnsideF48s_sp43eU.length)

theorem candSp43e_ok : candSp43e = true := by decide +kernel

theorem neg_closedSp43e : CFSG.KC.Ord.notB (closedK 45
    (setT ((wordsSp43e Sp43eP1.chars).map ekSp43e).tail) ((wordsSp43e Sp43eP1.chars).map ekSp43e).tail
    ([0, 1, 2, 4].map (getK (burnsideF48s_sp43eLS.map encL)))) = true := by
  decide +kernel

theorem neg_candSp43e : CFSG.KC.Ord.notB (candK 45 (setT ((wordsSp43e Sp43eP1.chars).map ekSp43e))
    (setT ((wordsSp43e Sp43eP2.chars).map ekSp43e))
    ((wordsSp43e Sp43eP1.chars).map ekSp43e) ((wordsSp43e Sp43eP2.chars).map ekSp43e)
    (burnsideF48s_sp43eKW.map ekSp43e) (burnsideF48s_sp43eTW.map ekSp43e) []) = true := by
  decide +kernel

end CertificateChecks.KernelF48S
