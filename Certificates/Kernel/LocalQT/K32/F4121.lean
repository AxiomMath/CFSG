module

public import Certificates.Kernel.LocalQT.K32.D4121b
public import Certificates.Kernel.LocalQT.K32.D4121c
public import Certificates.Kernel.SporSch.Mathieu.M23Facts
public import Certificates.Kernel.SporSch.Mathieu.M22Facts
import CFSG.Certificates.Kernel.Common.Harness
import Mathlib.Tactic.IntervalCases

public section

set_option maxRecDepth 400000

namespace CFSG.KD.LQT.C4121

open CFSG CFSG.Sporadic CFSG.Sporadic.Schreier CFSG.Certificates CFSG.Sporadic.Mathieu
open CFSG.Sporadic.Schreier.Native CFSG.Monster.B.Mathieu
open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KS.M11 CFSG.KS.MEnum CFSG.KS.SporSch.MOC
open CFSG.KS.SporSch.MBT CFSG.Sporadic.Th.Native CFSG.QuasithinUnique.DoubleA3.K32Mathieu
open CertificateChecks.KernelSporSch

theorem t23 : Nat.beq (sumOrdK 23 5 (mask 5) (ordK M23Q.LR 6) M23B.XL M23B.CL 3 M23B.XL.length)
    56672 = true := by quickRfl

theorem x23 : (cosetOrderTables m23Certificate 1 3).length = 56672 :=
  (classEq_sound (by decide) (by decide) M23OC.chainQ M23OC.classEq (mo := 3)
    (by norm_num) (by norm_num)).2.trans (Nat.eq_of_beq_eq_true t23)

theorem r23a : abOK (m23Rep3Words.getD 0 []) = true := by quickRfl

theorem r23b : Nat.beq (abWordK 23 5 (mask 5) (pidn 23 5) (M23Q.S 0) (M23Q.SI 0) (M23Q.S 1)
    (M23Q.SI 1) (m23Rep3Words.getD 0 [])) (M23K3.getD 0 clsD0).R = true := by quickRfl

theorem img23 : imageList (m23Rep3.getD 0 1) = (unpack 23 5 (M23K3.getD 0 clsD0).R).toList := by
  rw [m23Rep3, M23OC.getD_map_eval]
  exact M23OC.img_word r23a r23b

theorem cls23 : ClsOK 23 5 M23OC.tA M23OC.tB 3 60000 M23K3 := by
  intro j hj
  have hj1 : j < 1 := by simpa [M23K3] using hj
  interval_cases j
  exact ⟨M23K3.h0, M23OC.elems_of_blocks (by decide) M23K3.hb0, fun i hi => absurd hi (by omega)⟩

theorem hR23 : m23Rep3.length = M23K3.length ∧ ∀ j < M23K3.length,
    imageList (m23Rep3.getD j 1) = (unpack 23 5 (M23K3.getD j clsD0).R).toList := by
  refine ⟨by decide, fun j hj => ?_⟩
  have hj1 : j < 1 := by simpa [M23K3] using hj
  interval_cases j
  exact img23

theorem cover23 : repsOK 23 (pairTables m23PermA m23PermB) (pairTables m23PermA⁻¹ m23PermB⁻¹)
      (cosetOrderTables m23Certificate 1 3) (m23Rep3.map toTable) 60000 = true ∧
    repSizes 23 (pairTables m23PermA m23PermB) (pairTables m23PermA⁻¹ m23PermB⁻¹)
      (m23Rep3.map toTable) 60000 = [56672] ∧
    (m23Rep3.map toTable).all (ordTest 23 3) = true := by
  obtain ⟨h1, h2, h3⟩ := chainK_reps3 M23OC.tA_eq M23OC.tB_eq M23OC.szOK' cls23 hR23
    (by norm_num) (X := cosetOrderTables m23Certificate 1 3) (by rw [x23]; decide)
  exact ⟨h1, h2.trans (by decide), h3⟩

theorem g23a : allN 3 (fun j => abOK (m23Cent3Words.getD j [])) = true := by quickRfl

theorem g23b : allN 3 (fun j => Nat.beq (abWordK 23 5 (mask 5) (pidn 23 5) (M23Q.S 0)
    (M23Q.SI 0) (M23Q.S 1) (M23Q.SI 1) (m23Cent3Words.getD j [])) (M23C3.S j)) = true := by
  quickRfl

theorem comm23 : allN 3 (fun j => commK 23 5 (mask 5) (23 * 5) (M23C3.S j)
    (M23K3.getD 0 clsD0).R) = true := by quickRfl

theorem chain23 : ChainK 23 5 (m23Cent3Words.map (evalCodes [m23PermA, m23PermB]))
    m23Cent3ChainWords (#v[0, 2] : Vector (Fin 23) 2) M23C3.S M23C3.SI M23C3.LR M23C3.TR
    M23C3.TRI 4 M23C3.BP 2 16 := by
  refine ⟨by norm_num, by norm_num, by norm_num, fun j hj => ?_, by decide, M23C3.head, M23C3.hl,
    by norm_num, M23C3.hs⟩
  have hj3 : j < 3 := by simpa [m23Cent3Words] using hj
  rw [M23OC.getD_map_eval]
  exact M23OC.img_word (allN_spec g23a j hj3) (allN_spec g23b j hj3)

theorem cent23 : m23Cent3Q.check = true ∧ m23Cent3Q.orderCertificate = 180 ∧
    (m23Cent3Words.map (evalCodes [m23PermA, m23PermB])).all
      (fun h => commT 23 (toTable h) (toTable (m23Rep3.getD 0 1))) = true := by
  obtain ⟨h1, h2⟩ := chainK_check (by decide) (by decide) chain23
  exact ⟨h1, h2.trans (by decide), M23OC.comm_of img23 chain23.2.2.2.1 (by decide) comm23⟩

theorem x22 : (cosetOrderTables m22Certificate 1 3).length = (M22X3.CS.map List.sum).sum :=
  chainK_cosetCount2 (by decide) (by decide) M22OC.chainQ M22OC.imgOne M22OC.cOne (by norm_num)
    (by norm_num) M22X3.hc

theorem r22a : abOK (m22Rep3Words.getD 0 []) = true := by quickRfl

theorem r22b : Nat.beq (abWordK 22 5 (mask 5) (pidn 22 5) (M22Q.S 0) (M22Q.SI 0) (M22Q.S 1)
    (M22Q.SI 1) (m22Rep3Words.getD 0 [])) (M22K3.getD 0 clsD0).R = true := by quickRfl

theorem img22 : imageList (m22Rep3.getD 0 1) = (unpack 22 5 (M22K3.getD 0 clsD0).R).toList := by
  rw [m22Rep3, M22OC.getD_map_eval]
  exact M22OC.img_word r22a r22b

theorem cls22 : ClsOK 22 5 M22OC.tA M22OC.tB 3 14000 M22K3 := by
  intro j hj
  have hj1 : j < 1 := by simpa [M22K3] using hj
  interval_cases j
  exact ⟨M22K3.h0, M22OC.elems_of_blocks (by decide) M22K3.hb0, fun i hi => absurd hi (by omega)⟩

theorem hR22 : m22Rep3.length = M22K3.length ∧ ∀ j < M22K3.length,
    imageList (m22Rep3.getD j 1) = (unpack 22 5 (M22K3.getD j clsD0).R).toList := by
  refine ⟨by decide, fun j hj => ?_⟩
  have hj1 : j < 1 := by simpa [M22K3] using hj
  interval_cases j
  exact img22

theorem cover22 : repsOK 22 (pairTables m22gA m22gB) (pairTables m22gA⁻¹ m22gB⁻¹)
      (cosetOrderTables m22Certificate 1 3) (m22Rep3.map toTable) 14000 = true ∧
    repSizes 22 (pairTables m22gA m22gB) (pairTables m22gA⁻¹ m22gB⁻¹)
      (m22Rep3.map toTable) 14000 = [12320] ∧
    (m22Rep3.map toTable).all (ordTest 22 3) = true := by
  obtain ⟨h1, h2, h3⟩ := chainK_reps3 M22OC.tA_eq M22OC.tB_eq M22OC.szOK' cls22 hR22
    (by norm_num) (X := cosetOrderTables m22Certificate 1 3) (by rw [x22]; decide)
  exact ⟨h1, h2.trans (by decide), h3⟩

theorem g22a : allN 4 (fun j => abOK (m22Cent3Words.getD j [])) = true := by quickRfl

theorem g22b : allN 4 (fun j => Nat.beq (abWordK 22 5 (mask 5) (pidn 22 5) (M22Q.S 0)
    (M22Q.SI 0) (M22Q.S 1) (M22Q.SI 1) (m22Cent3Words.getD j [])) (M22C3.S j)) = true := by
  quickRfl

theorem comm22 : allN 4 (fun j => commK 22 5 (mask 5) (22 * 5) (M22C3.S j)
    (M22K3.getD 0 clsD0).R) = true := by quickRfl

theorem chain22 : ChainK 22 5 (m22Cent3Words.map (evalCodes [m22gA, m22gB]))
    m22Cent3ChainWords (#v[0, 1] : Vector (Fin 22) 2) M22C3.S M22C3.SI M22C3.LR M22C3.TR
    M22C3.TRI 5 M22C3.BP 2 16 := by
  refine ⟨by norm_num, by norm_num, by norm_num, fun j hj => ?_, by decide, M22C3.head, M22C3.hl,
    by norm_num, M22C3.hs⟩
  have hj4 : j < 4 := by simpa [m22Cent3Words] using hj
  rw [M22OC.getD_map_eval]
  exact M22OC.img_word (allN_spec g22a j hj4) (allN_spec g22b j hj4)

theorem cent22 : m22Cent3Q.check = true ∧ m22Cent3Q.orderCertificate = 36 ∧
    (m22Cent3Words.map (evalCodes [m22gA, m22gB])).all
      (fun h => commT 22 (toTable h) (toTable (m22Rep3.getD 0 1))) = true := by
  obtain ⟨h1, h2⟩ := chainK_check (by decide) (by decide) chain22
  exact ⟨h1, h2.trans (by decide), M22OC.comm_of img22 chain22.2.2.2.1 (by decide) comm22⟩

end CFSG.KD.LQT.C4121

end
