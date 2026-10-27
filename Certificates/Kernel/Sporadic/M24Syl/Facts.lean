module

public import Certificates.Kernel.Sporadic.M24Syl.Checks
public import Certificates.Kernel.SporSch.Mathieu.M24Facts
public import CFSG.Certificates.Kernel.Spor.MSylowSoundW
public import CFSG.Certificates.Kernel.Spor.MSylowCentSound
public import CFSG.Sporadic.Schreier.MathieuSylowAutM24Inputs
public import CFSG.Sporadic.Schreier.MathieuSylowAutM24Derivs
public import CFSG.Sporadic.Schreier.MathieuSylowAutCent
public import CFSG.Sporadic.Schreier.MathieuOddCoreM24Data
public meta import CFSG.Sporadic.Schreier.MathieuSylowAutMain
public meta import CFSG.Sporadic.Schreier.M24
public meta import CFSG.Monster.B.Mathieu.M24Check
public meta import Certificates.Data.CFSGNative.SporadicSchreier.MathieuOddCore
import CFSG.Certificates.Kernel.Common.Harness
public import CFSG.Certificates.Kernel.Spor.PCountW
public import CFSG.Certificates.Kernel.Spor.PK.Perm.Inv

public section

namespace CertificateChecks.KernelSpor.M24Syl

open CFSG.KC.Enum CFSG.KS CFSG.KS.PCnt CFSG.KS.MSyl CFSG.Sporadic.Schreier CFSG.Sporadic.Mathieu
open CFSG.Certificates CFSG.Sporadic.Th.Native CFSG.Sporadic.Schreier.Native CFSG.Monster.B.Mathieu
open CFSG.KS.SporSch.MOC CertificateChecks.KernelSporSch

set_option maxRecDepth 400000

@[expose] def z0 : Equiv.Perm (Fin 24) :=
  List.formPerm [1, 15] * List.formPerm [2, 10] * List.formPerm [4, 21] * List.formPerm [6, 13] *
    List.formPerm [7, 23] * List.formPerm [12, 22] * List.formPerm [14, 19] *
    List.formPerm [16, 17]

theorem natTbl_z0 : natTbl 24 m24SylowZ = toTable z0 := by
  have h : ∀ i : Fin 24, UInt32.ofNat (m24SylowZ.getD i.val 0) = UInt32.ofNat (z0 i).val := by
    decide +kernel
  unfold natTbl toTable
  exact congrArg _ (funext h)

theorem pk_one : pkw 5 (1 : Equiv.Perm (Fin 24)) = I := Nat.eq_of_beq_eq_true (by quickRfl)
theorem pk_a : pkw 5 m24gA = A := Nat.eq_of_beq_eq_true (by quickRfl)
theorem pk_ai : pkw 5 m24gA⁻¹ = Ai := Nat.eq_of_beq_eq_true (by quickRfl)
theorem pk_b : pkw 5 m24gB = B := Nat.eq_of_beq_eq_true (by quickRfl)
theorem pk_bi : pkw 5 m24gB⁻¹ = Bi := Nat.eq_of_beq_eq_true (by quickRfl)
theorem pk_z : pkw 5 z0 = Z := Nat.eq_of_beq_eq_true (by quickRfl)
theorem pk_zi : pkw 5 z0⁻¹ = Zi := Nat.eq_of_beq_eq_true (by quickRfl)

theorem pt_eq : exprsV 24 5 (mask 5) I (slpP 24 5 (mask 5) I A Ai B Bi m24Derivs) ES = PT :=
  eq_of_beq pt

theorem pt_pkw : PT = ES.map fun e => pkw 5 (slpExpr m24gA m24gB m24Derivs e) := by
  rw [← pt_eq, ← pk_one, ← pk_a, ← pk_ai, ← pk_b, ← pk_bi,
    exprsV_slpP_pkw (by norm_num) (by norm_num)]

theorem zb_ne : z0 * m24gB ≠ m24gB * z0 := by
  intro h
  have e1 : pcomp 24 5 (mask 5) Z B = pkw 5 (z0 * m24gB) := by
    rw [← pk_z, ← pk_b]
    exact pkw_mul (by norm_num) (by norm_num) _ _
  have e2 : pcomp 24 5 (mask 5) B Z = pkw 5 (m24gB * z0) := by
    rw [← pk_z, ← pk_b]
    exact pkw_mul (by norm_num) (by norm_num) _ _
  have hz := zb
  rw [e1, e2, h, Nat.beq_refl] at hz
  exact Bool.false_ne_true hz

theorem sylowAut : sylowAutOK 24 (toTable m24gA) (toTable m24gB) m24Derivs ES (toTable z0)
    1100 244823040 10 = true := by
  refine sylowAutP_sound_w (w := 5) (by norm_num) (by norm_num) m24gA m24gB z0 m24Derivs ES 1100
    244823040 10 ?_
  rw [pk_one, pk_a, pk_ai, pk_b, pk_bi, pk_z, pk_zi]
  exact syl

theorem centralizer : sylCentOK 24 (sylowGens 24 (toTable m24gA) (toTable m24gB) m24Derivs
    ES) (toTable z0) (toTable m24gB) (allTables m24CentQ1) = true := by
  have hs : enumFrom 24 5 (mask 5) (24 * 5) M24C1.LR M24C1.TR
      (centBadP 24 5 (mask 5) (pidn 24 5) Z PT) 3 0 (pidn 24 5) 0 = 0 :=
    Nat.eq_of_beq_eq_true scan
  rw [pt_pkw, ← pk_z] at hs
  have hbs : (#v[0, 1, 2] : Vector (Fin 24) 3).toList.Nodup := by decide
  have h := sylCentOK_of_scan (n := 24) (w := 5) (k := 3) (by norm_num) hbs
    KernelSporSch.M24OC.chainC1 sylowAut zb_ne hs
  unfold m24CentQ1
  exact h

theorem facts : (sylowAutOK 24 (toTable m24gA) (toTable m24gB) m24Derivs
      m24SylowExprs (natTbl 24 m24SylowZ) 1100 244823040 10 = true
    )
    ∧ (sylCentOK 24 (sylowGens 24 (toTable m24gA) (toTable m24gB) m24Derivs m24SylowExprs)
      (natTbl 24 m24SylowZ) (toTable m24gB) (allTables m24CentQ1) = true
    )
    ∧ ((repsOK 24 (pairTables m24gA m24gB) (pairTables m24gA⁻¹ m24gB⁻¹)
        (cosetOrderTables m24Certificate 1 2) (m24InvReps.map toTable) 40000 = true ∧
      repSizes 24 (pairTables m24gA m24gB) (pairTables m24gA⁻¹ m24gB⁻¹)
        (m24InvReps.map toTable) 40000 = [31878, 11385] ∧
      (m24InvReps.map toTable).all (ordTest 24 2) = true
    )
    ∧ (m24CentQ1.check = true ∧ m24CentQ1.orderCertificate = 7680 ∧
      (m24CentWords1.map (evalCodes [m24gA, m24gB])).all
        (fun h => commT 24 (toTable h) (toTable ((m24InvReps).getD 0 1))) = true ∧
      oddWitnessOK 24 15 (allTables m24CentQ1) = true
    )
    ∧ (m24CentQ2.check = true ∧ m24CentQ2.orderCertificate = 21504 ∧
      (m24CentWords2.map (evalCodes [m24gA, m24gB])).all
        (fun h => commT 24 (toTable h) (toTable ((m24InvReps).getD 1 1))) = true ∧
      oddWitnessOK 24 21 (allTables m24CentQ2) = true
    )
    ∧ (ordTest 24 2 (toTable m24gA) = true ∧ ordTest 24 3 (toTable m24gB) = true ∧
      wordsTest 24 2 3 m24AutWords (toTable m24gA) (toTable m24gB) = true ∧
      repsTotal 24 (pairTables m24gA m24gB) (pairTables m24gA⁻¹ m24gB⁻¹)
        (m24InvReps.map toTable) (orderTables m24Certificate 3) 40000 (wordsTest 24 2 3 m24AutWords) =
          244823040
    )) := by
  rw [natTbl_z0]
  exact ⟨sylowAut, centralizer, KernelSporSch.M24OC.facts2205⟩

end CertificateChecks.KernelSpor.M24Syl

end
