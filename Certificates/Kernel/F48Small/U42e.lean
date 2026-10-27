module

public import CFSG.Milestones.ASVolI.F48.Small.U42eInputs
public import Certificates.Data.Kernel.F48Small.Pack
public import Certificates.Kernel.SporSch.Th.GenStr
public import Certificates.Data.Kernel.DcK

public section

#kss_strof CertificateChecks.KernelF48S.U42eP1 CFSG.ASVolI.burnsideF48s_u42eP1Str

set_option maxRecDepth 100000 in
#kss_strof CertificateChecks.KernelF48S.U42eP2 CFSG.ASVolI.burnsideF48s_u42eP2Str

namespace CertificateChecks.KernelF48S

open CFSG.ASVolI CFSG.KC.F48S CFSG.KC.LQT.L

@[expose] noncomputable def wordsU42e (cs : List Char) : List (List (Fin 5 × Bool)) :=
  (CFSG.KC.DcK.splitGo ' ' cs []).map fun l => l.map burnsideF48s_u42eLetter

@[expose] noncomputable def ekU42e (w : List (Fin 5 × Bool)) : ℕ :=
  evK 45 (burnsideF48s_u42eLS.map encL) (burnsideF48s_u42eLSi.map encL) w

@[expose] noncomputable def lettersTw : Bool :=
  ((wordsU42e U42eP1.chars ++ burnsideF48s_u42eR1).all fun w => w.all fun l => decide (l.1 ≠ 3)) &&
  ((wordsU42e U42eP2.chars ++ burnsideF48s_u42eR2).all fun w => w.all fun l => decide (l.1 ≠ 2)) &&
  ((burnsideF48s_u42eC0W ++ burnsideF48s_u42eN0W).all fun w => w.all fun l =>
    decide (l.1 ≠ 2 ∧ l.1 ≠ 3)) &&
  (List.range 7).all fun j =>
    ((burnsideF48s_u42eU j).all fun w => w.all fun l => decide (l.1 ≠ 3)) &&
    ((burnsideF48s_u42eV j).all fun w => w.all fun l => decide (l.1 ≠ 2)) &&
    ((burnsideF48s_u42eKW j ++ burnsideF48s_u42eTW j ++ burnsideF48s_u42eW j).all fun w =>
      w.all fun l => decide (l.1 ≠ 2 ∧ l.1 ≠ 3))

theorem lettersTw_ok : lettersTw = true := by decide +kernel

theorem gens_ok : burnsideF48s_u42eCheckGens () = true := by decide +kernel

theorem rels_ok : burnsideF48s_u42eCheckRels () = true := by decide +kernel

@[expose] noncomputable def closedTw : Bool :=
  decide ((wordsU42e U42eP1.chars).length = 1152) && decide ((wordsU42e U42eP2.chars).length = 1920) &&
  decide ((wordsU42e U42eP1.chars).getD 0 [(0, true)] = []) &&
  decide ((wordsU42e U42eP2.chars).getD 0 [(0, true)] = []) &&
  decide (burnsideF48s_u42eC0W = [[], burnsideF48s_u42eWord "AA", burnsideF48s_u42eWord "aa"]) &&
  decide ((burnsideF48s_u42eU 3).length = 98) &&
  closedK 45 (setT ((wordsU42e U42eP1.chars).map ekU42e)) ((wordsU42e U42eP1.chars).map ekU42e)
    ([0, 1, 2, 4].map (getK (burnsideF48s_u42eLS.map encL))) &&
  closedK 45 (setT ((wordsU42e U42eP2.chars).map ekU42e)) ((wordsU42e U42eP2.chars).map ekU42e)
    ([0, 1, 3, 4].map (getK (burnsideF48s_u42eLS.map encL))) &&
  (List.range 7).all fun j =>
    decide ((burnsideF48s_u42eKW j).getD 0 [(0, true)] = []) &&
    decide (0 < (burnsideF48s_u42eKW j).length) &&
    (burnsideF48s_u42eC0W.all fun c => memT (setT ((burnsideF48s_u42eKW j).map ekU42e)) (ekU42e c)) &&
    closedK 45 (setT ((burnsideF48s_u42eKW j).map ekU42e)) ((burnsideF48s_u42eKW j).map ekU42e)
      ((burnsideF48s_u42eKW j).map ekU42e) &&
    decide ((burnsideF48s_u42eU j).length ≤ (burnsideF48s_u42eV j).length) &&
    decide ((burnsideF48s_u42eU j).length ≤ (burnsideF48s_u42eW j).length)

theorem closedTw_ok : closedTw = true := by decide +kernel

@[expose] noncomputable def candTw : Bool :=
  (List.range 7).all fun j =>
    candK 45 (setT ((wordsU42e U42eP1.chars).map ekU42e)) (setT ((wordsU42e U42eP2.chars).map ekU42e))
      ((wordsU42e U42eP1.chars).map ekU42e) ((wordsU42e U42eP2.chars).map ekU42e)
      ((burnsideF48s_u42eKW j).map ekU42e) ((burnsideF48s_u42eTW j).map ekU42e)
      (uvwK ((burnsideF48s_u42eU j).map ekU42e) ((burnsideF48s_u42eV j).map ekU42e)
        ((burnsideF48s_u42eW j).map ekU42e) (burnsideF48s_u42eU j).length)

theorem candTw_ok : candTw = true := by decide +kernel

@[expose] noncomputable def classTw : Bool :=
  (burnsideF48s_u42eN0W.all fun n =>
    memT (setT ((wordsU42e U42eP1.chars).map ekU42e)) (ekU42e n) &&
    memT (setT ((wordsU42e U42eP2.chars).map ekU42e)) (ekU42e n) &&
    normK 45 (burnsideF48s_u42eC0W.map ekU42e) (ekU42e n)) &&
  (wordsU42e U42eP1.chars).all fun s =>
    !normK 45 (burnsideF48s_u42eC0W.map ekU42e) (ekU42e s) ||
    memT (setT (burnsideF48s_u42eC0W.map ekU42e)) (ekU42e s) ||
    !memT (setT (burnsideF48s_u42eC0W.map ekU42e)) (pcomp (ekU42e s) 45 (ekU42e s)) ||
    !memT (setT ((wordsU42e U42eP2.chars).map ekU42e)) (ekU42e s) ||
    burnsideF48s_u42eN0W.any fun n => (List.range 7).any fun j =>
      (burnsideF48s_u42eKW j).any fun k => eqAt (ekU42e n) (ekU42e s) (ekU42e k) (ekU42e n) 45

theorem classTw_ok : classTw = true := by decide +kernel

end CertificateChecks.KernelF48S
