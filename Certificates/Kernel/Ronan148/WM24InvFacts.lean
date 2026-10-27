module

public import Certificates.Kernel.Ronan148.WM24Inv
public import Certificates.Kernel.Tc.M24Facts
public import CFSG.Certificates.Kernel.Misc.ArrEnumSound

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelRonan148.WM24Inv

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KC.Misc.ArrEnum CertificateChecks.KernelTc.M24
open CFSG.RankThree.PartTwo.Sec14.Ronan148W CFSG.RankThree.Native CFSG.Monster.B.Co2.Native
open CFSG.AGLEmbeddingD2.Wilson.Census219
open CFSG.KC.BfsPin (PP eqA_PP compA_PP invCand_PP idA_eq)

theorem anyN_ex {m : Nat} {f : Nat → Bool} (h : CFSG.KC.LQT.P.anyN m f = true) :
    ∃ i < m, f i = true := by
  rw [anyNP_eq, List.any_eq_true] at h
  obtain ⟨i, hi, h⟩ := h
  exact ⟨i, List.mem_range.1 hi, h⟩

theorem invCheck_true : invCheck () = true := by
  have hk := kInv
  unfold invK at hk
  simp only [Bool.and_eq_true, allNP_iff] at hk
  obtain ⟨⟨pX, hQ⟩, hC⟩ := hk
  have PX := pp_of_permB hw pX
  have hQs : (invArrs ()).size = 6 := by decide +kernel
  have eQ : ∀ l < 6, (invArrs ())[l]! = unpack 24 5 (QP l) := fun l hl => arrBind_sound (bQ l hl)
  have hE := eC
  simp only [invCheck, Bool.and_eq_true]
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · rw [hx]
    exact CFSG.KC.Misc.ArrEnum.validA_unpack pX
  · rw [CFSG.Monster.B.Co2.allLt_iff, hQs]
    intro l hl
    obtain ⟨pQ, hcj⟩ := hQ l hl
    have PQ := pp_of_permB hw pQ
    rw [eQ l hl, hx, Bool.and_eq_true, conj_unpack hw pQ pX, inv_unpack hw pX,
      eqA_PP (PQ.mul (PX.mul PQ.inv)) PX.inv]
    exact ⟨CFSG.KC.Misc.ArrEnum.validA_unpack pQ, hcj⟩
  · rw [CFSG.Monster.B.Co2.allLt_iff]
    intro k hk
    have hk' : k < EC.N := by
      have h2 := hE.2.1
      change k < (enumBfs 24 m24caA (List.range 24) 1200).pts.size at hk
      rwa [h2] at hk
    have ePt : (m24CC ()).pts[k]! = unpack 24 5 (EC.T k) := hE.2.2 k hk'
    have pT : permB 24 5 (EC.T k) = true := allN_spec EC.perm k hk'
    have PT := pp_of_permB hw pT
    rw [ePt, pow_unpack hw pT 3, idA_eq hw, eqA_PP (pp_ppow hw PT 3) (CFSG.KC.BfsPin.PP.id hw),
      Bool.or_eq_true]
    have h0 := hC k hk'
    rw [Bool.or_eq_true] at h0
    rcases h0 with h | h
    · exact Or.inl h
    · right
      obtain ⟨l, hl, h⟩ := anyN_ex h
      obtain ⟨i, hi, h⟩ := anyN_ex h
      obtain ⟨j, hj, hb⟩ := anyN_ex h
      have PQ := pp_of_permB hw (hQ l hl).1
      rw [List.any_eq_true]
      refine ⟨(invArrs ())[l]!, ?_, ?_⟩
      · rw [getElem!_pos (invArrs ()) l (by rw [hQs]; exact hl)]
        exact Array.getElem_mem_toList _
      · rw [List.any_eq_true]
        refine ⟨compA 24 (CFSG.Monster.B.Mathieu.powArr 24 m24xA i)
          (CFSG.Monster.B.Mathieu.powArr 24 (unpack 24 5 (EC.T k)) j), ?_, ?_⟩
        · simp only [pairArrs, List.mem_flatMap, List.mem_map, List.mem_range]
          exact ⟨i, hi, j, hj, rfl⟩
        · rw [eQ l hl, hx, conj_unpack hw (hQ l hl).1 pT, pow_unpack hw pX i, pow_unpack hw pT j,
            compA_PP (pp_ppow hw PX i) (pp_ppow hw PT j),
            eqA_PP (PQ.mul (PT.mul PQ.inv)) ((pp_ppow hw PX i).mul (pp_ppow hw PT j))]
          exact hb

end CertificateChecks.KernelRonan148.WM24Inv

end
