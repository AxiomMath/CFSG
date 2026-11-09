module

public import Certificates.Kernel.LocalComp.HeFix
public import Certificates.Kernel.SporSch.HeT.B2114K
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitHe36CertInputs
public import CFSG.Certificates.Kernel.Enum.DefsC
import CFSG.Certificates.Kernel.Common.Harness
import CFSG.Certificates.Kernel.Spor.PK.Perm.CompC

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelLC.HeGS36

open CFSG.KC.Enum CFSG.KS CFSG.KS.Prim CFSG.KC.PermTool CFSG.ComponentClassification.GrSLit.HeldFix
open CFSG.ComponentClassification.GrSLit.HeGS CertificateChecks.KernelLC.HeFix
open CFSG.Sporadic.SmallOddCore

@[expose] noncomputable def pc (p q : Nat) : Nat := pcomp 8330 14 (mask 14) p q

@[expose] noncomputable def K (w : List Nat) : Nat :=
  wordTabK 8330 14 CertificateChecks.KernelSporSch.HeB14.C0 w

@[expose] noncomputable def H (w : List Nat) : Nat := wordTabK 8330 14 PC1 w

@[expose] noncomputable def cT : Nat :=
  pc (powK 8330 14 (pc (pc (pc (HG.F 1) (K (heDWords.getD 1 []))) G1I) PT1) 8) (HG.F 1)

@[expose] noncomputable def cI : Nat := pinvS 8330 14 (mask 14) cT

@[expose] noncomputable def w1 : Nat := pc (pc cT (HG.F 0)) cI

@[expose] noncomputable def tgt (p : Nat) : Nat := nIf(Nat.beq (p % 2) 0, w1, pc w1 PT1)

@[expose] noncomputable def zT : Nat := pc (pc (pc G1I (HG.F 0)) (HG.F 1)) (K heGSVWord)

@[expose] noncomputable def gT : Nat := pc (pc zT zT) G1I

@[expose] noncomputable def gI : Nat := pinvS 8330 14 (mask 14) gT

@[expose] noncomputable def i5 : Nat := pc (pc gT (K (heDWords.getD 0 []))) gI

@[expose] noncomputable def g36pc (p q : Nat) : Nat := pcompC 8330 14 (mask 14) p q

@[expose] noncomputable def g36w (G : Nat → Nat) (w : List Nat) : Nat :=
  List.rec (motive := fun _ => Nat) (pidn 8330 14) (fun j _ acc => g36pc (G j) acc) w

@[expose] noncomputable def g36pow (p e : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) (pidn 8330 14) (fun _ acc => g36pc p acc) e

@[expose] noncomputable def g36K (w : List Nat) : Nat := g36w CertificateChecks.KernelSporSch.HeB14.C0 w

@[expose] noncomputable def g36cT : Nat :=
  g36pc (g36pow (g36pc (g36pc (g36pc (HG.F 1) (g36K (heDWords.getD 1 []))) G1I) PT1) 8) (HG.F 1)

@[expose] noncomputable def g36zT : Nat :=
  g36pc (g36pc (g36pc G1I (HG.F 0)) (HG.F 1)) (g36K heGSVWord)

@[expose] noncomputable def g36gT : Nat := g36pc (g36pc g36zT g36zT) G1I

@[expose] noncomputable def g36i5 : Nat :=
  g36pc (g36pc g36gT (g36K (heDWords.getD 0 []))) (pinvS 8330 14 (mask 14) g36gT)

@[expose] noncomputable def g36w1 : Nat := g36pc (g36pc g36cT (HG.F 0)) (pinvS 8330 14 (mask 14) g36cT)

@[expose] noncomputable def g36tgt (p : Nat) : Nat := nIf(Nat.beq (p % 2) 0, g36w1, g36pc g36w1 PT1)

@[expose] noncomputable def g36F (p : Nat) : Bool :=
  Nat.beq (g36pc (g36w PC1 (heGS36D p 0)) (g36pc (g36pow (g36w PC1 heGSXWord) (3 + p / 2))
    (g36pc (g36w PC1 (heGS36D p 1)) (g36pc (g36w PC1 (heGS36D p 2))
      (g36pc (g36pow (g36w PC1 heGSXWord) (3 + p / 2)) (g36w PC1 (heGS36D p 3)))))))
    (g36tgt p)

theorem g36Rel : (Nat.beq (H [1, 1]) (pidn 8330 14) && Nat.beq (H [2, 2]) (pidn 8330 14) &&
    Nat.beq (H [3, 3]) (pidn 8330 14) && Nat.beq (H [8, 8, 8, 8, 8, 8]) (pidn 8330 14)) = true := by
  quickRfl

theorem g36pc_eq (p q : Nat) : g36pc p q = pc p q := CFSG.KS.PK.pcompC_eq 8330 14 p q

theorem g36w_eq (G : Nat → Nat) : ∀ w, g36w G w = wordTabK 8330 14 G w
  | [] => rfl
  | j :: w => by
    change g36pc (G j) (g36w G w) = pc (G j) (wordTabK 8330 14 G w)
    rw [g36pc_eq, g36w_eq G w]

theorem g36pow_eq (p : Nat) : ∀ e, g36pow p e = powK 8330 14 p e
  | 0 => rfl
  | e + 1 => by
    change g36pc p (g36pow p e) = pc p (powK 8330 14 p e)
    rw [g36pc_eq, g36pow_eq p e]

theorem g36K_eq (w : List Nat) : g36K w = K w := g36w_eq _ w

theorem g36cT_eq : g36cT = cT := by
  unfold g36cT cT
  simp only [g36pc_eq, g36K_eq, g36pow_eq]

theorem g36gT_eq : g36gT = gT := by
  unfold g36gT gT g36zT zT
  simp only [g36pc_eq, g36K_eq]

theorem g36i5_eq : g36i5 = i5 := by
  unfold g36i5 i5 gI
  simp only [g36pc_eq, g36K_eq, g36gT_eq]

theorem kCanon' : (allN 9 (fun j => cn (CertificateChecks.KernelSporSch.HeB14.C0 j)) &&
    cn G1I && cn g36cT && cn (pinvS 8330 14 (mask 14) g36cT) && cn g36gT &&
      cn (pinvS 8330 14 (mask 14) g36gT)) = true := by
  quickRfl

theorem kCanon : (allN 9 (fun j => cn (CertificateChecks.KernelSporSch.HeB14.C0 j)) &&
    cn G1I && cn cT && cn cI && cn gT && cn gI) = true := by
  have h := kCanon'
  rw [g36cT_eq, g36gT_eq] at h
  unfold cI gI
  exact h

theorem kC' : (Nat.beq (g36pc g36cT (g36K (heDWords.getD 1 []))) (g36pc PT1 g36cT) &&
    permOK 8330 14 (mask 14) (8330 * 14) g36cT (pinvS 8330 14 (mask 14) g36cT) &&
    permOK 8330 14 (mask 14) (8330 * 14) (pinvS 8330 14 (mask 14) g36cT) g36cT &&
    permOK 8330 14 (mask 14) (8330 * 14) g36gT (pinvS 8330 14 (mask 14) g36gT) &&
    permOK 8330 14 (mask 14) (8330 * 14) (pinvS 8330 14 (mask 14) g36gT) g36gT) = true := by
  quickRfl

theorem kC : (Nat.beq (pc cT (K (heDWords.getD 1 []))) (pc PT1 cT) &&
    permOK 8330 14 (mask 14) (8330 * 14) cT cI && permOK 8330 14 (mask 14) (8330 * 14) cI cT &&
    permOK 8330 14 (mask 14) (8330 * 14) gT gI && permOK 8330 14 (mask 14) (8330 * 14) gI gT) =
      true := by
  have h := kC'
  rw [g36cT_eq, g36gT_eq, g36K_eq, g36pc_eq, g36pc_eq] at h
  unfold cI gI
  exact h

theorem kG0 : g36F 0 = true := by quickRfl

theorem kG1 : g36F 1 = true := by quickRfl

theorem kG2 : g36F 2 = true := by quickRfl

theorem kG3 : g36F 3 = true := by quickRfl

theorem kE' : (!Nat.beq (g36pc (g36K (heDWords.getD 1 [])) g36i5)
      (g36pc g36i5 (g36K (heDWords.getD 1 []))) &&
    Nat.beq (g36pc (g36K (heGSComm2 heGSUComm)) (g36K (heGSComm2 heGSUComm))) (pidn 8330 14)) =
      true := by
  quickRfl

theorem kE : (!Nat.beq (pc (K (heDWords.getD 1 [])) i5) (pc i5 (K (heDWords.getD 1 []))) &&
    Nat.beq (pc (K (heGSComm2 heGSUComm)) (K (heGSComm2 heGSUComm))) (pidn 8330 14)) = true := by
  have h := kE'
  rw [g36i5_eq, g36K_eq, g36K_eq, g36pc_eq, g36pc_eq, g36pc_eq] at h
  exact h

end CertificateChecks.KernelLC.HeGS36

end
