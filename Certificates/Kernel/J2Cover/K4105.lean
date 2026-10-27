module

public import Certificates.Kernel.J2Cover.K19
public import Certificates.Kernel.J2Cover.K4105E
public import CFSG.Certificates.Kernel.J2EnumQSound
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelJ2Cover

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KC.Child3 CFSG.KC.J2Cover CFSG.KC.J2Enum
open CFSG.Monster.B.Co2.Native CFSG.Certificates.Native
open CFSG.Sporadic.Th.Native (Table ap idT)
open CFSG.Sporadic.Schreier.Native CFSG.ComponentClassification.J2Cover

theorem sumF_zero : ∀ m, sumF m (fun _ => 0) = 0
  | 0 => rfl
  | m + 1 => by
    change strictN (sumF m fun _ => 0) (fun s' => Nat.add s' 0) = 0
    rw [strictN_eq', sumF_zero m]

theorem sum5 : sumF (rcnt (PA.LR 0))
    (blkCntQ 315 9 PA.LR PA.TR PA.BP (pidn 315 9) (PA.S 0) TA 5 5 2) = 0 := by
  rw [Nat.eq_of_beq_eq_true kL0, sumF_congr 315 (g := fun _ => 0) fun a ha => Nat.eq_of_beq_eq_true
    (CFSG.KC.Co3Bfs.cover_of_blocks (by norm_num) (by norm_num) E5B.all a ha), sumF_zero]

theorem cnt5 : (orderTablesOf (idT 315) 5).countP
      (pairTest 315 5 2 2 5 (arrTable 315 (unpack 315 9 (PA.S 0)))) = 0 ∧
    (orderTablesOf (idT 315) 5).countP (pairTest 315 5 2 2 5 (arrTable 315 (unpack 315 9 TA))) =
      0 := by
  unfold orderTablesOf autTables
  have h := enumCntQ_sound chainPA k20 ⟨cPA 0 (by omega), by quickRfl⟩ ⟨cTA, by quickRfl⟩
    (q := 5) (r := 5) (s := 2) (by norm_num) (by norm_num) (by norm_num)
  rw [h.1, h.2, sum5]
  exact ⟨rfl, rfl⟩

theorem total4105 : classTotal 315 #[tblA, tblB] #[tblAInv, tblBInv] (orderTablesOf (idT 315) 2)
    (orderTablesOf (idT 315) 5) 4000 5 2 2 5 = 0 := by
  unfold orderTablesOf autTables
  rw [(classes_sound (g := 2) (cap := 4000) (r := 5) (s := 2) (my := 5) chainPA (le_refl 2)
    (gensP RC.GP RC.GIP gA gB gAi gBi) gpC (le_refl 2) (by quickRfl) rcAll ordRep lenN).2]
  have hl : RC.CS.length = 2 := rfl
  have hr : List.range 2 = [0, 1] := rfl
  rw [hl, hr]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
  have h := cnt5
  unfold orderTablesOf autTables at h
  rw [eRC0, eRC1, h.1, h.2]
  rfl

end CertificateChecks.KernelJ2Cover

end
