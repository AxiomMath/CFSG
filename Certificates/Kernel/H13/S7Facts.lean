module

import Certificates.Kernel.H13.S7
public import Certificates.Kernel.H13.S7OvS
import Certificates.Kernel.H13.ElemsS7
import CFSG.Certificates.Kernel.Mat8SSound
import CFSG.Certificates.Kernel.Census.CatFacts.PkEnum

public section

namespace CertificateChecks.KernelH13

open CFSG.Quasithin.H13.Mat8Cert CFSG.Quasithin.H13.S7Cert CFSG.KC.Mat8P

@[expose] def ovHead : Bool :=
  mReps.length == 3 && mReps.all (Std.HashSet.ofList s7E).contains &&
    ([0, 1, 2].all fun i => (mE i).length == 48 && subB (pG ++ [mReps.getD i one8]) (mE i))

@[expose] def ovY (y : List ℕ) : Bool :=
  (Std.HashSet.ofList (elemsOf pG)).contains y ||
    (let B := elemsOf (pG ++ [y]) 49
     (49 ≤ B.length && nodupB B) ||
       (B.length == 48 && nodupB B &&
         ([0, 1, 2].map fun i => Std.HashSet.ofList (mE i)).any fun h => B.all h.contains))

theorem ovB_split : CFSG.Quasithin.H13.S7Cert.ovB = (ovHead && s7E.all ovY) := rfl

theorem ovY_eq (y : List ℕ) (hy : validB y = true) : ovY y = s7OvYS y := by
  have hg : (pG ++ [y]).all validB = true := by
    rw [List.all_append, List.all_cons, List.all_nil, hy, Bool.true_and, Bool.and_true]
    decide
  simp only [ovY, s7OvYS, s7OvYBS, mE, nodupB_toP, elemsOf_toF, List.any_map, Function.comp_def,
    hs_contains_toLR', hs_contains_toLR, CFSG.KC.Mat8R.elemsFR_eq, CFSG.KC.Mat8S.elemsFS_eq,
    CFSG.KC.Mat8S.nodupP_elemsF _ hg, Bool.and_true]

set_option maxRecDepth 100000 in
theorem ovHead_true : ovHead = true := by
  simp only [ovHead, mE, s7E, subB, closedB, nodupB_toP, elemsOf_toF, hs_contains_toLR',
    contains_toLR, mul8_toF]
  decide +kernel

theorem s7E_length : s7E.length = 5040 := by
  have h := s7_basicB_true
  simp only [s7BasicB, Bool.and_eq_true, beq_iff_eq] at h
  exact h.2

theorem s7_ovB_true : CFSG.Quasithin.H13.S7Cert.ovB = true := by
  rw [ovB_split, ovHead_true, Bool.true_and]
  have hf : ovY ∘ unpackM = s7OvYS ∘ unpackM := funext fun X => ovY_eq _ (validB_unpackM X)
  rw [CertificateChecks.KernelH13.s7E_eq, List.all_map, hf, ← List.all_map]
  apply CFSG.Certificates.Kernel.PkEnum.all_of_chunks _ _ 48 105
    (by rw [← CertificateChecks.KernelH13.s7E_eq, s7E_length])
  intro j hj
  have h : s7OvChunkS j = true := by
    interval_cases j
    exacts [s7OvChunkS0, s7OvChunkS1, s7OvChunkS2, s7OvChunkS3, s7OvChunkS4, s7OvChunkS5, s7OvChunkS6,
      s7OvChunkS7, s7OvChunkS8, s7OvChunkS9, s7OvChunkS10, s7OvChunkS11, s7OvChunkS12, s7OvChunkS13,
      s7OvChunkS14, s7OvChunkS15, s7OvChunkS16, s7OvChunkS17, s7OvChunkS18, s7OvChunkS19, s7OvChunkS20,
      s7OvChunkS21, s7OvChunkS22, s7OvChunkS23, s7OvChunkS24, s7OvChunkS25, s7OvChunkS26, s7OvChunkS27,
      s7OvChunkS28, s7OvChunkS29, s7OvChunkS30, s7OvChunkS31, s7OvChunkS32, s7OvChunkS33, s7OvChunkS34,
      s7OvChunkS35, s7OvChunkS36, s7OvChunkS37, s7OvChunkS38, s7OvChunkS39, s7OvChunkS40, s7OvChunkS41,
      s7OvChunkS42, s7OvChunkS43, s7OvChunkS44, s7OvChunkS45, s7OvChunkS46, s7OvChunkS47, s7OvChunkS48,
      s7OvChunkS49, s7OvChunkS50, s7OvChunkS51, s7OvChunkS52, s7OvChunkS53, s7OvChunkS54, s7OvChunkS55,
      s7OvChunkS56, s7OvChunkS57, s7OvChunkS58, s7OvChunkS59, s7OvChunkS60, s7OvChunkS61, s7OvChunkS62,
      s7OvChunkS63, s7OvChunkS64, s7OvChunkS65, s7OvChunkS66, s7OvChunkS67, s7OvChunkS68, s7OvChunkS69,
      s7OvChunkS70, s7OvChunkS71, s7OvChunkS72, s7OvChunkS73, s7OvChunkS74, s7OvChunkS75, s7OvChunkS76,
      s7OvChunkS77, s7OvChunkS78, s7OvChunkS79, s7OvChunkS80, s7OvChunkS81, s7OvChunkS82, s7OvChunkS83,
      s7OvChunkS84, s7OvChunkS85, s7OvChunkS86, s7OvChunkS87, s7OvChunkS88, s7OvChunkS89, s7OvChunkS90,
      s7OvChunkS91, s7OvChunkS92, s7OvChunkS93, s7OvChunkS94, s7OvChunkS95, s7OvChunkS96, s7OvChunkS97,
      s7OvChunkS98, s7OvChunkS99, s7OvChunkS100, s7OvChunkS101, s7OvChunkS102, s7OvChunkS103, s7OvChunkS104]
  rw [s7OvChunkS] at h
  exact h

theorem s7Check_true : s7Check = true := by
  rw [s7Check, s7_basicB_true, s7_pB_true, s7_cvB_true, s7_eWB_true, s7_ovB_true, s7_oB_true,
    s7_m12B_true]
  rfl

end CertificateChecks.KernelH13

end
