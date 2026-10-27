module

public import Certificates.Kernel.GFR3.M24
public import CFSG.Certificates.Kernel.GFR3KSound
public import CFSG.Certificates.Kernel.Misc.ArrBind

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelGFR3.M24

open CFSG.HardMathSupport.Solomon.Coordinator CFSG.KC.Enum CFSG.KS CFSG.KS.Raw
open CFSG.KC.Misc.ArrEnum CFSG.KC.Misc.ChainTail CFSG.KC.B3S3K CFSG.KC.GFR3K
open CFSG.Certificates.Native CFSG.Monster.B.Co2.Native CFSG.RankThree.Native
  CFSG.RankThree.PartOne CFSG.Monster.B.Mathieu

theorem binds : Binds 24 5 C.S 12 9 C.BP m24ThreeArrs m24ThreeBaseArr :=
  ⟨by norm_num, by norm_num, by norm_num, by decide +kernel, fun j hj => arrBind_sound (bS j hj),
    by decide +kernel, bget⟩

theorem hN : E.N = 1080 := Nat.eq_of_beq_eq_true n0.1

theorem hng : E.ng = 3 := Nat.eq_of_beq_eq_true n0.2

theorem bindG : BindA 24 5 m24ThreeGens E.ng E.G := by
  refine ⟨by rw [hng]; decide +kernel, fun j hj => ?_⟩
  rw [hng] at hj
  exact arrBind_sound (bG j hj)

theorem pG : ∀ k < E.ng, permB 24 5 (E.G k) = true := fun k hk => by
  have h := allN_spec comm k hk
  rw [Bool.and_eq_true] at h
  exact h.1

theorem hkeys : m24ThreeKeys = m24ThreeBaseArr.toList := by decide +kernel

theorem enumC : enumOK 24 m24ThreeGens m24ThreeBaseArr.toList
      (enumBfs 24 m24ThreeGens m24ThreeBaseArr.toList 1100) = true ∧
    (enumBfs 24 m24ThreeGens m24ThreeBaseArr.toList 1100).pts.size = E.N ∧
    ∀ i < E.N, (enumBfs 24 m24ThreeGens m24ThreeBaseArr.toList 1100).pts[i]! =
      unpack 24 5 (E.T i) :=
  enum_of bindG pG E.ok (mem_base_lt binds C.hl) E.keys (by rw [hN]; omega)

theorem cert_eq : m24ThreeCert () = enumBfs 24 m24ThreeGens m24ThreeBaseArr.toList 1100 := by
  rw [m24ThreeCert, hkeys]

theorem hNS : 24 ≤ C.NS * 24 := by decide +kernel

theorem hW : CFSG.Sporadic.Schreier.Co3.Native.wordsArr 2 12 d = m24ThreeWords := by
  decide +kernel

theorem m24_ok : m24ThreeCheck () = true := by
  have hA : m24ThreeA = unpack 24 5 (AB 0) := arrBind_sound bA
  have hB : m24ThreeB = unpack 24 5 (AB 1) := arrBind_sound bB
  have hx : m24ThreeGens[0]! = unpack 24 5 (E.G 0) := bindG.2 0 (by rw [hng]; norm_num)
  have hx1 : Nat.beq (E.G 0) (pidn 24 5) = false := by
    have := x0.2.2
    rwa [Bool.not_eq_true'] at this
  have hPS : ∀ j < 12, permB 24 5 (C.S j) = true := fun j hj =>
    permB_of_pp (pp_of_permOK szOK' (allN_spec perm j hj))
  have hchain := rawChainK_sound (chunks := 1) binds C.head C.hl hNS C.hs
  rw [hW] at hchain
  have hS0 : m24ThreeArrs[0]! = unpack 24 5 (C.S 0) := binds.2.2.2.2.1 0 (by norm_num)
  have hS1 : m24ThreeArrs[1]! = unpack 24 5 (C.S 1) := binds.2.2.2.2.1 1 (by norm_num)
  obtain ⟨he1, he2, he3⟩ := enumC
  have hTp : ∀ i < E.N, permB 24 5 (E.T i) = true := allN_spec E.perm
  have hcent := centOKP_of (p := 3) szOK' binds perm C.hl x0.1 rels bindG comm
    (fun j hj => siftA_of binds perm C.hl (siftG j (by rw [hng] at hj; exact hj))) he1 he2 he3 hTp
    (by norm_num) (by rw [Nat.eq_of_beq_eq_true rc]; exact tail)
  rw [hN] at hcent
  have hcls := gfr3ClassOK_of szOK' he2 he3 hTp (Nc := 1080) (e := 3) (f := 1)
    (fun i hi => allN_spec cls i (by rw [← hN]; exact hi))
  have horb := rawOrbitSizesK_sound binds perm C.hl
  rw [orb] at horb
  unfold m24ThreeCheck
  rw [cert_eq, hkeys, hx, hA, hB, validA_of pAB.1, validA_of pAB.2, caseChainOK2P, hchain, hS0, hS1,
    eqA_unpack' szOK' (hPS 0 (by norm_num)) pAB.1, eqA_unpack' szOK' (hPS 1 (by norm_num)) pAB.2,
    head.1, head.2, horb, hcent, powEq_id szOK' x0.1, x0.2.1, eqA_id szOK' x0.1, hx1, hcls]
  rfl

end CertificateChecks.KernelGFR3.M24

end
