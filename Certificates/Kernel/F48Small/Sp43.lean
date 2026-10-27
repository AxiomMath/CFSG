module

public import CFSG.Milestones.ASVolI.F48.Small.Sp43Inputs
public import Certificates.Data.Kernel.F48Small.Pack
public import Certificates.Kernel.SporSch.Th.GenStr
public import Certificates.Data.Kernel.DcK

public section

#kss_strof CertificateChecks.KernelF48S.Sp43P1 CFSG.ASVolI.burnsideF48s_sp43P1Str

set_option maxRecDepth 100000 in
#kss_strof CertificateChecks.KernelF48S.Sp43P2 CFSG.ASVolI.burnsideF48s_sp43P2Str

namespace CertificateChecks.KernelF48S

open CFSG.ASVolI CFSG.KC.F48S CFSG.KC.LQT.L

@[expose] noncomputable def wordsSp43 (cs : List Char) : List (List (Fin 4 × Bool)) :=
  (CFSG.KC.DcK.splitGo ' ' cs []).map fun l => l.map burnsideF48s_sp43Letter

@[expose] noncomputable def ekSp43 (w : List (Fin 4 × Bool)) : ℕ :=
  evK 45 (burnsideF48s_sp43LS.map encL) (burnsideF48s_sp43LSi.map encL) w

@[expose] noncomputable def lettersSp43 : Bool :=
  ((wordsSp43 Sp43P1.chars ++ burnsideF48s_sp43R1 ++ burnsideF48s_sp43U).all fun w =>
    w.all fun l => decide (l.1 ≠ 3)) &&
  ((wordsSp43 Sp43P2.chars ++ burnsideF48s_sp43R2 ++ burnsideF48s_sp43V).all fun w =>
    w.all fun l => decide (l.1 ≠ 2)) &&
  ((burnsideF48s_sp43KW ++ burnsideF48s_sp43TW ++ burnsideF48s_sp43W).all fun w =>
    w.all fun l => decide (l.1 ≠ 2 ∧ l.1 ≠ 3))

theorem lettersSp43_ok : lettersSp43 = true := by decide +kernel

theorem gensSp43_ok : burnsideF48s_sp43CheckGens () = true := by decide +kernel

theorem relsSp43_ok : burnsideF48s_sp43CheckRels () = true := by decide +kernel

@[expose] noncomputable def closedSp43 : Bool :=
  decide ((wordsSp43 Sp43P1.chars).length = 648) && decide ((wordsSp43 Sp43P2.chars).length = 648) &&
  decide ((wordsSp43 Sp43P1.chars).getD 0 [(0, true)] = []) &&
  decide ((wordsSp43 Sp43P2.chars).getD 0 [(0, true)] = []) &&
  decide (burnsideF48s_sp43KW = [[], burnsideF48s_sp43Word "aaa"]) &&
  decide (burnsideF48s_sp43U.length = 8) && decide (burnsideF48s_sp43V.length = 8) &&
  decide (burnsideF48s_sp43W.length = 8) &&
  closedK 45 (setT ((wordsSp43 Sp43P1.chars).map ekSp43)) ((wordsSp43 Sp43P1.chars).map ekSp43)
    ([0, 1, 2].map (getK (burnsideF48s_sp43LS.map encL))) &&
  closedK 45 (setT ((wordsSp43 Sp43P2.chars).map ekSp43)) ((wordsSp43 Sp43P2.chars).map ekSp43)
    ([0, 1, 3].map (getK (burnsideF48s_sp43LS.map encL)))

theorem closedSp43_ok : closedSp43 = true := by decide +kernel

@[expose] noncomputable def candSp43 : Bool :=
  candK 45 (setT ((wordsSp43 Sp43P1.chars).map ekSp43)) (setT ((wordsSp43 Sp43P2.chars).map ekSp43))
    ((wordsSp43 Sp43P1.chars).map ekSp43) ((wordsSp43 Sp43P2.chars).map ekSp43)
    (burnsideF48s_sp43KW.map ekSp43) (burnsideF48s_sp43TW.map ekSp43)
    (uvwK (burnsideF48s_sp43U.map ekSp43) (burnsideF48s_sp43V.map ekSp43)
      (burnsideF48s_sp43W.map ekSp43) burnsideF48s_sp43U.length)

theorem candSp43_ok : candSp43 = true := by decide +kernel

theorem neg_closedSp43 : CFSG.KC.Ord.notB (closedK 45
    (setT ((wordsSp43 Sp43P1.chars).map ekSp43).tail) ((wordsSp43 Sp43P1.chars).map ekSp43).tail
    ([0, 1, 2].map (getK (burnsideF48s_sp43LS.map encL)))) = true := by
  decide +kernel

theorem neg_candSp43 : CFSG.KC.Ord.notB (candK 45 (setT ((wordsSp43 Sp43P1.chars).map ekSp43))
    (setT ((wordsSp43 Sp43P2.chars).map ekSp43))
    ((wordsSp43 Sp43P1.chars).map ekSp43) ((wordsSp43 Sp43P2.chars).map ekSp43)
    (burnsideF48s_sp43KW.map ekSp43) (burnsideF48s_sp43TW.map ekSp43) []) = true := by
  decide +kernel

end CertificateChecks.KernelF48S
