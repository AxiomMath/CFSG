module

public import Certificates.Kernel.Sporadic.M23Syl.Checks
public import Certificates.Kernel.SporSch.Mathieu.M23Facts
public import CFSG.Certificates.Kernel.Spor.MSylowSoundW
public import CFSG.Certificates.Kernel.Spor.MSylowCentSound
public import CFSG.Sporadic.Schreier.MathieuSylowAutM23Inputs
public import CFSG.Sporadic.Schreier.MathieuSylowAutM23Derivs
public import CFSG.Sporadic.Schreier.MathieuSylowAutCent
public import CFSG.Sporadic.Schreier.MathieuOddCoreM23Data
public meta import CFSG.Sporadic.Schreier.MathieuSylowAutMain
public meta import CFSG.Sporadic.Schreier.M23
public meta import CFSG.Sporadic.Schreier.M23Pinned
public meta import Certificates.Data.CFSGNative.SporadicSchreier.MathieuOddCore
import CFSG.Certificates.Kernel.Common.Harness
public import CFSG.Certificates.Kernel.Spor.PCountW
public import CFSG.Certificates.Kernel.Spor.PK.Perm.Inv

public section

namespace CertificateChecks.KernelSpor.M23Syl

open CFSG.KC.Enum CFSG.KS CFSG.KS.PCnt CFSG.KS.MSyl CFSG.Sporadic.Schreier CFSG.Sporadic.Mathieu
open CFSG.Certificates CFSG.Sporadic.Th.Native CFSG.Sporadic.Schreier.Native CFSG.Monster.B.Mathieu
open CFSG.KS.SporSch.MOC CertificateChecks.KernelSporSch

set_option maxRecDepth 400000

@[expose] def z0 : Equiv.Perm (Fin 23) :=
  List.formPerm [0, 7] * List.formPerm [1, 6] * List.formPerm [2, 9] * List.formPerm [3, 8] *
    List.formPerm [12, 19] * List.formPerm [13, 18] * List.formPerm [14, 21] *
    List.formPerm [15, 20]

theorem natTbl_z0 : natTbl 23 m23SylowZ = toTable z0 := by
  have h : ∀ i : Fin 23, UInt32.ofNat (m23SylowZ.getD i.val 0) = UInt32.ofNat (z0 i).val := by
    decide +kernel
  unfold natTbl toTable
  exact congrArg _ (funext h)

theorem pk_one : pkw 5 (1 : Equiv.Perm (Fin 23)) = I := Nat.eq_of_beq_eq_true (by quickRfl)
theorem pk_a : pkw 5 m23PermA = A := Nat.eq_of_beq_eq_true (by quickRfl)
theorem pk_ai : pkw 5 m23PermA⁻¹ = Ai := Nat.eq_of_beq_eq_true (by quickRfl)
theorem pk_b : pkw 5 m23PermB = B := Nat.eq_of_beq_eq_true (by quickRfl)
theorem pk_bi : pkw 5 m23PermB⁻¹ = Bi := Nat.eq_of_beq_eq_true (by quickRfl)
theorem pk_z : pkw 5 z0 = Z := Nat.eq_of_beq_eq_true (by quickRfl)
theorem pk_zi : pkw 5 z0⁻¹ = Zi := Nat.eq_of_beq_eq_true (by quickRfl)

theorem pt_eq : exprsV 23 5 (mask 5) I (slpP 23 5 (mask 5) I A Ai B Bi m23Derivs) ES = PT :=
  eq_of_beq pt

theorem pt_pkw : PT = ES.map fun e => pkw 5 (slpExpr m23PermA m23PermB m23Derivs e) := by
  rw [← pt_eq, ← pk_one, ← pk_a, ← pk_ai, ← pk_b, ← pk_bi,
    exprsV_slpP_pkw (by norm_num) (by norm_num)]

theorem zb_ne : z0 * m23PermB ≠ m23PermB * z0 := by
  intro h
  have e1 : pcomp 23 5 (mask 5) Z B = pkw 5 (z0 * m23PermB) := by
    rw [← pk_z, ← pk_b]
    exact pkw_mul (by norm_num) (by norm_num) _ _
  have e2 : pcomp 23 5 (mask 5) B Z = pkw 5 (m23PermB * z0) := by
    rw [← pk_z, ← pk_b]
    exact pkw_mul (by norm_num) (by norm_num) _ _
  have hz := zb
  rw [e1, e2, h, Nat.beq_refl] at hz
  exact Bool.false_ne_true hz

theorem sylowAut : sylowAutOK 23 (toTable m23PermA) (toTable m23PermB) m23Derivs ES (toTable z0)
    150 10200960 7 = true := by
  refine sylowAutP_sound_w (w := 5) (by norm_num) (by norm_num) m23PermA m23PermB z0 m23Derivs ES 150
    10200960 7 ?_
  rw [pk_one, pk_a, pk_ai, pk_b, pk_bi, pk_z, pk_zi]
  exact syl

theorem centralizer : sylCentOK 23 (sylowGens 23 (toTable m23PermA) (toTable m23PermB) m23Derivs
    ES) (toTable z0) (toTable m23PermB) (allTables m23CentQ1) = true := by
  have hs : enumFrom 23 5 (mask 5) (23 * 5) M23C1.LR M23C1.TR
      (centBadP 23 5 (mask 5) (pidn 23 5) Z PT) 4 0 (pidn 23 5) 0 = 0 :=
    Nat.eq_of_beq_eq_true scan
  rw [pt_pkw, ← pk_z] at hs
  have hbs : (#v[2, 0, 5, 4] : Vector (Fin 23) 4).toList.Nodup := by decide
  have h := sylCentOK_of_scan (n := 23) (w := 5) (k := 4) (by norm_num) hbs
    KernelSporSch.M23OC.chainC1 sylowAut zb_ne hs
  unfold m23CentQ1
  exact h

theorem facts : (sylowAutOK 23 (toTable m23PermA) (toTable m23PermB) m23Derivs
      m23SylowExprs (natTbl 23 m23SylowZ) 150 10200960 7 = true
    )
    ∧ (sylCentOK 23 (sylowGens 23 (toTable m23PermA) (toTable m23PermB) m23Derivs m23SylowExprs)
      (natTbl 23 m23SylowZ) (toTable m23PermB) (allTables m23CentQ1) = true
    )
    ∧ ((repsOK 23 (pairTables m23PermA m23PermB) (pairTables m23PermA⁻¹ m23PermB⁻¹)
        (cosetOrderTables m23Certificate 1 2) (m23InvReps.map toTable) 4000 = true ∧
      repSizes 23 (pairTables m23PermA m23PermB) (pairTables m23PermA⁻¹ m23PermB⁻¹)
        (m23InvReps.map toTable) 4000 = [3795] ∧
      (m23InvReps.map toTable).all (ordTest 23 2) = true
    )
    ∧ (m23CentQ1.check = true ∧ m23CentQ1.orderCertificate = 2688 ∧
      (m23CentWords1.map (evalCodes [m23PermA, m23PermB])).all
        (fun h => commT 23 (toTable h) (toTable ((m23InvReps).getD 0 1))) = true ∧
      oddWitnessOK 23 21 (allTables m23CentQ1) = true
    )
    ∧ (ordTest 23 2 (toTable m23PermA) = true ∧ ordTest 23 4 (toTable m23PermB) = true ∧
      wordsTest 23 2 4 m23AutWords (toTable m23PermA) (toTable m23PermB) = true ∧
      repsTotal 23 (pairTables m23PermA m23PermB) (pairTables m23PermA⁻¹ m23PermB⁻¹)
        (m23InvReps.map toTable) (orderTables m23Certificate 4) 4000 (wordsTest 23 2 4 m23AutWords) =
          10200960
    )) := by
  rw [natTbl_z0]
  exact ⟨sylowAut, centralizer, KernelSporSch.M23OC.facts2204⟩

end CertificateChecks.KernelSpor.M23Syl

end
