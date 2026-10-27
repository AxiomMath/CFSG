module

public import Certificates.Kernel.StdOdd.ThreeBlow
public import CFSG.Monster.Existence.StdOdd.P5
public import CFSG.Fischer.F4
public import CFSG.Monster.Existence.StdOdd.Cert.SylowThreeTorusInputs
public import CFSG.Monster.Existence.StdOdd.Cert.SylowThreeData
public import CFSG.Monster.B.Classical.E6AdjointTable
public import Certificates.Data.CFSGNative.Chevalley.C2E6CertSylowThree
import CFSG.Fischer.F4
import CFSG.Certificates.Kernel.Common.Harness

public section

namespace CFSG.KD.StdOdd.SylowThreeTorus

open CFSG.KC.Misc CFSG.KC.Ord CFSG.KC.LQT.P CFSG.KC.Misc.E6Std
  CFSG.LieType.Chevalley.C2E6Std.MatrixModel CFSG.Monster.B.Classical.E6Adjoint
  CFSG.Monster.Existence.StdOdd CFSG.Monster.Existence.StdOdd.Cert

set_option maxRecDepth 100000

theorem codes : codesOK bracketCodes = true := by quickRfl
theorem gam : allN 72 (fun j => Nat.blt (nthV gamTable j) 72) = true := by quickRfl
theorem eLt : allN 5 (fun j => ltW (eWord j)) = true := by quickRfl
theorem hLt : allN 5 (fun j => ltW (hWord j)) = true := by quickRfl
theorem fixedE : allN 5 (fun j => Nat.beq (wordTB bracketCodes formBits gamTable (eWord j))
    (wordLB bracketCodes formBits (eWord j))) = true := by quickRfl
theorem torus : allN 5 (fun j => Nat.beq (wordLB bracketCodes formBits (hWord j))
    (diagB (nthLL torusExps j))) = true := by quickRfl

theorem eWord_lt : ∀ j < 5, ∀ l ∈ eWord j, l.1 < 72 := fun j hj => ltW_true (allN_true eLt j hj)

theorem hWord_lt : ∀ j < 5, ∀ l ∈ hWord j, l.1 < 72 := fun j hj => ltW_true (allN_true hLt j hj)

theorem fixed_e_ok :
    CertNative.fixedOK bracketCodes formBits gamTable ((List.range 5).map eWord) = true := by
  refine fixedOK_of codes formBits gam (fun w hw => ?_) fun w hw => ?_
  · obtain ⟨j, hj, rfl⟩ := List.mem_map.1 hw
    exact eWord_lt j (List.mem_range.1 hj)
  · obtain ⟨j, hj, rfl⟩ := List.mem_map.1 hw
    exact allN_true fixedE j (List.mem_range.1 hj)

theorem torus_ok :
    CertNative.torusOK bracketCodes formBits ((List.range 5).map hWord) torusExps = true := by
  refine torusOK_of codes formBits (fun w hw => ?_) fun j hj => ?_
  · obtain ⟨j, hj, rfl⟩ := List.mem_map.1 hw
    exact hWord_lt j (List.mem_range.1 hj)
  · simp only [List.length_map, List.length_range] at hj
    have e : ((List.range 5).map hWord).getD j [] = hWord j := by
      simp [List.getD_eq_getElem?_getD, hj]
    rw [e, ← nthLL_eq_getD]
    exact allN_true torus j hj

open Certificates in
open CFSG CFSG.Monster CFSG.Monster.Existence CFSG.Monster.Existence.StdOdd in
open CFSG.Monster.Existence.StdOdd.Cert CFSG.Blueprint.Chevalley in
open CFSG.LieType.Chevalley.C2E6Std CFSG.LieType.Chevalley.C2E6Std.MatrixModel in
open CFSG.Monster.B.Classical.E6Adjoint in
open CFSG.Monster.Existence.StdOdd.P5 (E5 rk) in
theorem facts : (CertNative.fixedOK bracketCodes formBits gamTable
      ((List.range 5).map eWord) = true)
    ∧ (CertNative.torusOK bracketCodes formBits ((List.range 5).map hWord)
      torusExps = true)
    ∧ (∀ j < 5, ∀ l ∈ hWord j, l.1 < 72)
    ∧ (∀ j < 5, ∀ l ∈ eWord j, l.1 < 72)
    ∧ (∀ v : E5, (∀ p : Fin 78, exN v p % 3 = 0) → v = 0)
    ∧ (∀ v : E5,
      (Finset.univ.filter fun p : Fin 78 => exN v p % 3 ≠ 0).card + rk v = 72) :=
  ⟨fixed_e_ok, torus_ok, hWord_lt, eWord_lt, by decide +kernel, by decide +kernel⟩

end CFSG.KD.StdOdd.SylowThreeTorus

end
