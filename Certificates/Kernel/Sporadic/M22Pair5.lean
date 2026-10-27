module

public import CFSG.Sporadic.Schreier.M22Data
public import CFSG.Certificates.Kernel.Spor.PCountWSound
import CFSG.Certificates.Kernel.Common.Harness
import CFSG.Certificates.Kernel.Common.EachUnfold
public import CFSG.Certificates.Kernel.Common.JsonGz
import CFSG.Certificates.Kernel.Common.Repo
public import CFSG.Certificates.Kernel.Spor.Loops
public import CFSG.Certificates.Kernel.Spor.PK.Perm.Inv
public import CFSG.Sporadic.Schreier.ImagePairs

public section

namespace CertificateChecks.KernelSpor.M22Pair5

open CFSG.Sporadic.Schreier CFSG.Certificates CFSG.Sporadic.Mathieu
open CFSG.KC.Enum CFSG.KS CFSG.KS.PK CFSG.KS.PCnt

set_option maxRecDepth 100000
set_option Elab.async false

#kc_repo #kc_json_gz CertificateChecks.KernelSpor.M22Pair5.D
  "Certificates/Kernel/Sporadic/data/m22pair5.json.gz" 202 4134620516214442394 (cnt : List Nat)

@[expose] def lv : List (List (Equiv.Perm (Fin 22))) :=
  (List.finRange m22Certificate.baseCount).map (levelTransversals m22Certificate)

@[expose] def slice (j : Nat) : List (List (Equiv.Perm (Fin 22))) :=
  (((lv.headD []).drop (1 * j)).take 1) :: lv.tail

@[expose] def I : Nat := pkw 5 (1 : Equiv.Perm (Fin 22))

@[expose] noncomputable def cntS (j : Nat) : Nat :=
  pcnt 22 5 (mask 5) (cntW 22 5 (mask 5) I (pkw 5 m22gA)) ((slice j).map fun T => T.map (pkw 5))
    I 0

@[expose] noncomputable def cl : List Nat :=
  conjDFS 22 5 (mask 5) (pkw 5 m22gA) (pkw 5 m22gA⁻¹) (pkw 5 m22gB) (pkw 5 m22gB⁻¹) (pkw 5 m22gA)
    1200

theorem lens : Nat.beq ((lv.map List.length).prod) 443520 = true := by quickRfl

theorem len₀ : Nat.ble (lv.headD []).length 22 = true := by quickRfl

theorem base : baseOK lv m22Certificate.base.toList = true := by quickRfl

theorem oA : Nat.beq (ordTwo 22 5 (mask 5) I (pkw 5 m22gA)) 1 = true := by quickRfl

theorem wAB : Nat.beq (ordPr 22 5 (mask 5) I (pkw 5 (m22gA * m22gB * m22gB)) 4) 1 = true := by
  quickRfl

theorem ncl : Nat.beq cl.length 1155 = true := by quickRfl

@[expose] noncomputable def cntV (j : Nat) : Nat := D.cnt.getD j 0

@[expose] noncomputable def sF (j : Nat) : Bool := Nat.beq (cntS j) (cntV j)

#kc_each_unfold sF 0 22 as CertificateChecks.KernelSpor.M22Pair5.s eval cntV

end CertificateChecks.KernelSpor.M22Pair5

end
