module

public import CFSG.Sporadic.Schreier.M12Data
public meta import CFSG.Sporadic.Schreier.M12Data
public import CFSG.Sporadic.Schreier.ClassSum
public import CFSG.Certificates.Kernel.Spor.PCountSound
import CFSG.Certificates.Kernel.Common.Harness
public import CFSG.Certificates.Kernel.Spor.Loops
public import CFSG.Certificates.Kernel.Spor.PK.Perm.Inv
public meta import CFSG.Sporadic.Schreier.ImagePairs

public section

namespace CertificateChecks.KernelSpor.M12Count

open CFSG.Sporadic.Schreier CFSG.Certificates CFSG.Sporadic.Mathieu CFSG.Sporadic.Schreier.Native
open CFSG.KC.Enum CFSG.KS CFSG.KS.PK CFSG.KS.PCnt

set_option maxRecDepth 100000

@[expose] def lv : List (List (Equiv.Perm (Fin 12))) :=
  (List.finRange m12Certificate.baseCount).map (levelTransversals m12Certificate)

@[expose] def slice (j : Nat) : List (List (Equiv.Perm (Fin 12))) :=
  (((lv.headD []).drop (3 * j)).take 3) :: lv.tail

@[expose] def r₂ : Equiv.Perm (Fin 12) := ((m12gA * m12gB) ^ 3 * m12gB) ^ 3

@[expose] def I : Nat := pk (1 : Equiv.Perm (Fin 12))

@[expose] noncomputable def cntS (j : Nat) : Nat :=
  pcnt 12 4 (mask 4) (cnt4 12 4 (mask 4) I (pk m12gA) (pk r₂)) ((slice j).map fun T => T.map pk)
    I 0

@[expose] noncomputable def cl₁ : BState :=
  conjBFS 12 4 (mask 4) (pk m12gA) (pk m12gA⁻¹) (pk m12gB) (pk m12gB⁻¹) (pk m12gA) 1000

@[expose] noncomputable def cl₂ : BState :=
  conjBFS 12 4 (mask 4) (pk m12gA) (pk m12gA⁻¹) (pk m12gB) (pk m12gB⁻¹) (pk r₂) 1000

theorem check : m12Certificate.check = true := by quickRfl

theorem lens : Nat.beq ((lv.map List.length).prod) 95040 = true := by quickRfl

theorem len₀ : Nat.ble (lv.headD []).length 12 = true := by quickRfl

theorem s0 : Nat.beq (cntS 0) 212137649207852925225 = true := by quickRfl

theorem s1 : Nat.beq (cntS 1) 119903955227500347590 = true := by quickRfl

theorem s2 : Nat.beq (cntS 2) 119903942033360814278 = true := by quickRfl

theorem s3 : Nat.beq (cntS 3) 101457197959651262662 = true := by quickRfl

theorem oA : Nat.beq (ordTwo 12 4 (mask 4) I (pk m12gA)) 1 = true := by quickRfl

theorem oR : Nat.beq (ordTwo 12 4 (mask 4) I (pk r₂)) 1 = true := by quickRfl

theorem pAB : Nat.beq (partner 12 4 (mask 4) I (pk m12gA) (pk m12gB)) 1 = true := by quickRfl

theorem t₁ : conjTreeP 12 4 (mask 4) (pk m12gA) (pk m12gA⁻¹) (pk m12gB) (pk m12gB⁻¹) (pk m12gA)
    cl₁.1 cl₁.2.1 cl₁.2.2 = true := by quickRfl

theorem t₂ : conjTreeP 12 4 (mask 4) (pk m12gA) (pk m12gA⁻¹) (pk m12gB) (pk m12gB⁻¹) (pk r₂)
    cl₂.1 cl₂.2.1 cl₂.2.2 = true := by quickRfl

theorem n₁ : Nat.beq cl₁.1.length 495 = true := by quickRfl

theorem n₂ : Nat.beq cl₂.1.length 396 = true := by quickRfl

theorem dist : distB (cl₁.1 ++ cl₂.1) = true := by quickRfl

end CertificateChecks.KernelSpor.M12Count

end
