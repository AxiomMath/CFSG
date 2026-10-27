module

public import Certificates.Kernel.J2HypOne.Checks
public import Certificates.Kernel.J2Cover.KFact17260Facts

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelJ2HypOne

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KS.PEnum CFSG.KS.MulH CFSG.KC.J2Cover
open CFSG.KC.Misc.ArrEnum CFSG.KC.Child3 CFSG.KC.BfsPin
open CFSG.Monster.B.Co2.Native CFSG.Sporadic.Th.Native CFSG.Sporadic.Schreier.Native
open CFSG.ComponentClassification.J2Cover (inP arrTable outerArr tblU)
open CertificateChecks.KernelJ2Cover.KF17260 CFSG.EvenSporadicStandard.HypOne
  CFSG.EvenSporadicStandard.HypOne.J2

theorem compT_arr {X Y : Nat} (hX : CnN 315 9 X) (hY : CnN 315 9 Y) :
    compT 315 (arrTable 315 (unpack 315 9 X)) (arrTable 315 (unpack 315 9 Y)) =
      arrTable 315 (unpack 315 9 (pc X Y)) := by
  rw [arrTable_unpack, arrTable_unpack, compT_unpack hX hY, ← arrTable_unpack]
  rfl

theorem binds : arrE1 = unpack 315 9 (E 0) ∧ arrE2 = unpack 315 9 (E 1) ∧
    arrE3 = unpack 315 9 (E 2) ∧ arrL = unpack 315 9 (E 3) ∧ outerArr = unpack 315 9 (E 4) := by
  have hb := ch24273bind
  simp only [bAnd_iff] at hb
  obtain ⟨b1, b2, b3, bL, bU⟩ := hb
  exact ⟨arrBind_sound b1, arrBind_sound b2, arrBind_sound b3, arrBind_sound bL, arrBind_sound bU⟩

theorem e8_facts : Nat.beq (pcomp 315 9 (mask 9) (E 0) (E 1)) (pcomp 315 9 (mask 9) (E 1) (E 0)) = true ∧
    Nat.beq (pcomp 315 9 (mask 9) (E 0) (E 2)) (pcomp 315 9 (mask 9) (E 2) (E 0)) = true ∧
    Nat.beq (pcomp 315 9 (mask 9) (E 1) (E 2)) (pcomp 315 9 (mask 9) (E 2) (E 1)) = true ∧
    ord2K (E 0) = true ∧ ord2K (E 1) = true ∧ ord2K (E 2) = true ∧
    ord2K (pc (E 0) (E 1)) = true ∧ ord2K (pc (E 0) (E 2)) = true ∧
    ord2K (pc (E 1) (E 2)) = true ∧ ord2K (pc (pc (E 0) (E 1)) (E 2)) = true := by
  have h := ch24273e8
  unfold e8K commK24273 pc at h
  simp only [bAnd_iff] at h
  exact h

theorem e8Data_eq : e8Data = true := by
  obtain ⟨b1, b2, b3, -, -⟩ := binds
  have hel := ch24273elt
  obtain ⟨i1, p1, -, c1, -, -⟩ := elt_of b1 (allN_spec hel 0 (by norm_num))
  obtain ⟨i2, p2, -, c2, -, -⟩ := elt_of b2 (allN_spec hel 1 (by norm_num))
  obtain ⟨i3, p3, -, c3, -, -⟩ := elt_of b3 (allN_spec hel 2 (by norm_num))
  obtain ⟨m12, m13, m23, o1, o2, o3, o12, o13, o23, o123⟩ := e8_facts
  unfold e8Data
  rw [i1, i2, i3, p1, p2, p3]
  unfold e8Check
  rw [b1, b2, b3, commT_unpack c1 c2, commT_unpack c1 c3, commT_unpack c2 c3,
    compT_arr c1 c2, compT_arr c1 c3, compT_arr c2 c3,
    compT_arr (X := pc (E 0) (E 1)) (canon_pcN c1 c2) c3,
    ordTest_of (by norm_num) c1, ordTest_of (by norm_num) c2, ordTest_of (by norm_num) c3,
    ordTest_of (X := pc (E 0) (E 1)) (by norm_num) (canon_pcN c1 c2),
    ordTest_of (X := pc (E 0) (E 2)) (by norm_num) (canon_pcN c1 c3),
    ordTest_of (X := pc (E 1) (E 2)) (by norm_num) (canon_pcN c2 c3),
    ordTest_of (X := pc (pc (E 0) (E 1)) (E 2)) (by norm_num) (canon_pcN (canon_pcN c1 c2) c3)]
  unfold ord2K at o1 o2 o3 o12 o13 o23 o123
  rw [m12, m13, m23, o1, o2, o3, o12, o13, o23, o123]
  rfl

theorem foursData_eq : foursData = true := by
  obtain ⟨-, -, -, bL, bU⟩ := binds
  obtain ⟨iL, pL, eL, cL, cLI, -⟩ := elt_of bL (allN_spec ch24273elt 3 (by norm_num))
  have cU : CnN 315 9 (E 4) := ch24273u
  have h := ch24273four
  unfold ord2K at h
  unfold foursData
  rw [iL, pL, eL]
  unfold tblU
  rw [bL, bU, compT_arr cL cU, compT_arr (X := pc (E 3) (E 4)) (canon_pcN cL cU) cLI,
    compT_arr (X := pc (pc (E 3) (E 4)) (EI 3)) (canon_pcN (canon_pcN cL cU) cLI) cU,
    ordTest_of (X := pc (pc (pc (E 3) (E 4)) (EI 3)) (E 4)) (by norm_num)
      (canon_pcN (canon_pcN (canon_pcN cL cU) cLI) cU)]
  exact h

theorem facts : e8Data = true ∧ foursData = true := ⟨e8Data_eq, foursData_eq⟩

end CertificateChecks.KernelJ2HypOne

end
