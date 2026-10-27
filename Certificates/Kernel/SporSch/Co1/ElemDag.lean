module

public import Certificates.Kernel.SporSch.Co1.Packed
public import CFSG.Certificates.Kernel.SporSch.Co1ElemSound
public import CFSG.Sporadic.Schreier.Co1ElemThreeCheckInputs
public meta import Certificates.Kernel.SporSch.Co1.GenDag
public meta import CFSG.Sporadic.Schreier.Co1ElemThreeCheckInputs
import Init.Data.Nat.Fold
import Init.Data.Range.Basic
import Init.Data.Array.Basic
import CFSG.Certificates.Kernel.Common.Harness
public import Certificates.Kernel.SporSch.Co1.GenDag

public section

set_option maxRecDepth 400000

#kss_co1dag CertificateChecks.KernelSporSch.Co1Elem.E CFSG.Sporadic.Co1Schreier.Native.elemDag

namespace CertificateChecks.KernelSporSch.Co1Elem

open CFSG.KC.Enum CFSG.KS.Raw CFSG.KS.SporSch CFSG.KS.SporSch.M24 CFSG.KS.Mathieu
open CFSG.Sporadic.Co1Schreier CFSG.Sporadic.Co1Schreier.Native
open CertificateChecks.KernelSporSch.Co1ThreeLocal CertificateChecks.KernelSporSch.Co1Packed

@[expose] noncomputable def AF (i : Nat) : Nat := E.M (nget Data.elemIdx i)

@[expose] def ZZ : Rows := pow (mul (mul (mul T Y) TI) YI) 7

theorem b0 : bindListK 24 24 (E.M 0) Y.toList = true := by quickRfl
theorem b1 : bindListK 24 24 (E.M 1) T.toList = true := by quickRfl
theorem b2 : bindListK 24 24 (E.M 2) ZZ.toList = true := by quickRfl

theorem kD : dagK E.M E.MI 3 E.N Data.dagWords = true := by quickRfl
theorem kN : Nat.blt 56 E.N = true := by quickRfl

theorem arr {A : Rows} {P : Nat} (h : bindListK 24 24 P A.toList = true) : A = unpack 24 24 P := by
  have e := rows_of h
  rwa [Array.toArray_toList] at e

theorem zR_eq : zR = unpack 24 24 (E.M 2) := by
  unfold zR
  rw [tR_eq, yR_eq, inv_eq_of_mul kt, inv_eq_of_mul ky]
  exact arr b2

theorem dag_eq : elemDag = ((List.range E.N).map fun i => unpack 24 24 (E.M i),
    (List.range E.N).map fun i => unpack 24 24 (E.MI i), true) := by
  unfold elemDag
  refine dagK_sound ?_ kD
  rw [yR_eq, tR_eq, zR_eq, arr b0, arr b1]
  rfl

theorem nget_eq : ∀ (l : List Nat) (i : Nat), nget l i = l.getD i 0
  | [], _ => rfl
  | _ :: _, 0 => rfl
  | _ :: l, i + 1 => nget_eq l i

theorem idx_lt (i : Nat) : Data.elemIdx.getD i 0 < E.N := by
  have hN : 56 < E.N := Nat.blt_eq.mp kN
  have : Data.elemIdx.getD i 0 ≤ 56 := by
    rcases i with _ | _ | _ | _ | _ | _ | i <;> simp [Data.elemIdx]
  omega

theorem aRows_eq : aRows = fun i => unpack 24 24 (AF i) := by
  funext i
  unfold aRows AF
  rw [dag_eq, nget_eq, List.getD_eq_getElem?_getD, List.getElem?_map,
    List.getElem?_range (idx_lt i)]
  rfl

end CertificateChecks.KernelSporSch.Co1Elem

end
