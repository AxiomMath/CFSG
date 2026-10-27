module

public import Certificates.Kernel.WE8K.TabA
public import Certificates.Kernel.WE8K.TabQ
import CFSG.Certificates.Kernel.Common.ForallTree

set_option maxRecDepth 400000

public section

namespace CFSG.KD.WE8K

open CFSG.KC.WE8K
open CFSG.KC.Loop (allBelow)

#kc_forall_tree ch18004_tabPAll (fun k => tabPFam k = true) 8 CFSG.KD.WE8K.ch18004P

#kc_forall_tree ch18004_tabDAll (fun k => tabDFam k = true) 8 CFSG.KD.WE8K.ch18004D

#kc_forall_tree ch18004_startAll (fun k => startFam k = true) 10 CFSG.KD.WE8K.ch18004s

#kc_forall_tree ch18004_zwAll (fun k => zwFam k = true) 3 CFSG.KD.WE8K.ch18004z

#kc_forall_tree ch18004_qPAll (fun k => qPFam k = true) 8 CFSG.KD.WE8K.ch18004qp

#kc_forall_tree ch18004_qMAll (fun k => qMFam k = true) 8 CFSG.KD.WE8K.ch18004qm

theorem ch18004_tab : tabOK rT permP negP addP adjM = true := by
  have h1 : allBelow 8 1 (tabPF rT permP) = true := allBelow_of ch18004_tabPAll
  have h2 : allBelow 8 1 (tabDF rT addP) = true := allBelow_of ch18004_tabDAll
  rw [tabOK, ch18004_rt, ch18004_adj, h1, ch18004_tabN, h2]
  rfl

theorem ch18004_qP : qOK 1 qp xp rT = true := by
  have h : allBelow 8 1 (qF false qp rT) = true := allBelow_of ch18004_qPAll
  rw [qOK]
  change (true && Nat.beq (lenK qp) 7 && qXOK false xp rT && allBelow 8 1 (qF false qp rT)) = true
  rw [ch18004_qXP, h]
  decide +kernel

theorem ch18004_qM : qOK (-1) qm xm rT = true := by
  have h : allBelow 8 1 (qF true qm rT) = true := allBelow_of ch18004_qMAll
  rw [qOK]
  change (true && Nat.beq (lenK qm) 7 && qXOK true xm rT && allBelow 8 1 (qF true qm rT)) = true
  rw [ch18004_qXM, h]
  decide +kernel

theorem ch18004_starts : startsOK oS = true := allBelow_of ch18004_startAll

end CFSG.KD.WE8K

end
