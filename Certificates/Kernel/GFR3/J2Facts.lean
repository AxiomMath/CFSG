module

public import Certificates.Kernel.GFR3.J2
public import Certificates.Kernel.GFR3.J2Orb
public import CFSG.Certificates.Kernel.Misc.ChainTailOrbSound
public import Certificates.Kernel.GFR3.J2Cls0
public import Certificates.Kernel.GFR3.J2Cls1
public import Certificates.Kernel.GFR3.J2Cls2
public import Certificates.Kernel.GFR3.J2Cls3
public import Certificates.Kernel.GFR3.J2Cls4
public import Certificates.Kernel.GFR3.J2Cls5
public import CFSG.Certificates.Kernel.B3S3KSound
public import CFSG.Certificates.Kernel.GFR3KSound
public import CFSG.Certificates.Kernel.Misc.ArrBind
public import CFSG.Certificates.Kernel.Misc.HexFlatSound
public import CFSG.Certificates.Kernel.Common.ForallChunks
import CFSG.Certificates.Kernel.Spor.Loops
import Mathlib.Tactic.IntervalCases
public import CFSG.Certificates.Kernel.BfsPinSound

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelGFR3.J2

open CFSG.HardMathSupport.Solomon.Coordinator CFSG.KC.Enum CFSG.KS CFSG.KS.Raw
open CFSG.KC.Misc.ArrEnum CFSG.KC.Misc.ChainTail CFSG.KC.B3S3K CFSG.KC.GFR3K CFSG.KC.Misc.HexFlat
open CFSG.Certificates.Native CFSG.Monster.B.Co2.Native CFSG.RankThree.Native
  CFSG.RankThree.PartOne CFSG.Monster.B.Mathieu

theorem hA : j2ThreeA = unpack 315 9 (JS.F 0) := by
  have e : j2ThreeA = hexTable 4 315 (315 * 0) CFSG.Sporadic.Schreier.PairNative.j2StrongHex := by
    simp [j2ThreeA, CFSG.Sporadic.Schreier.PairNative.j2StrongArrs,
      CFSG.Sporadic.Schreier.PairNative.j2Strong]
  rw [e, JS.eq]
  exact hexTable_sound JS.all 0 (by norm_num)

theorem hB : j2ThreeB = unpack 315 9 (JS.F 1) := by
  have e : j2ThreeB = hexTable 4 315 (315 * 1) CFSG.Sporadic.Schreier.PairNative.j2StrongHex := by
    simp [j2ThreeB, CFSG.Sporadic.Schreier.PairNative.j2StrongArrs,
      CFSG.Sporadic.Schreier.PairNative.j2Strong]
  rw [e, JS.eq]
  exact hexTable_sound JS.all 1 (by norm_num)

theorem hS : ∀ j < 9, j2ThreeArrs[j]! = unpack 315 9 (C.S j) := by
  intro j hj
  rcases (by omega : j = 0 ∨ j = 1 ∨ 2 ≤ j) with rfl | rfl | h2
  · rw [show j2ThreeArrs[0]! = j2ThreeA by simp [j2ThreeArrs], hA,
      Nat.eq_of_beq_eq_true head.1]
  · rw [show j2ThreeArrs[1]! = j2ThreeB by simp [j2ThreeArrs], hB,
      Nat.eq_of_beq_eq_true head.2]
  · obtain ⟨k, rfl⟩ : ∃ k, j = k + 2 := ⟨j - 2, by omega⟩
    have hk : k < 7 := by omega
    have e : j2ThreeArrs[k + 2]! = CFSG.Monster.B.Fischer.hexTable3 315 (315 * k) j2ThreeHex := by
      rw [getElem!_pos _ (k + 2) (by simp [j2ThreeArrs]; omega)]
      simp [j2ThreeArrs, Array.getElem_append]
    rw [e, JH.eq, hexTable3_sound JH.all k hk, Nat.eq_of_beq_eq_true (sS k hk)]

theorem binds : Binds 315 9 C.S 9 7 C.BP j2ThreeArrs j2ThreeBaseArr :=
  ⟨by norm_num, by norm_num, by norm_num, by simp [j2ThreeArrs], hS,
    by simp [j2ThreeBaseArr, j2ThreeBase], bget⟩

theorem hN : E.N = 1080 := Nat.eq_of_beq_eq_true n0.1

theorem hng : E.ng = 4 := Nat.eq_of_beq_eq_true n0.2

theorem bindG : BindA 315 9 j2ThreeGens E.ng E.G := by
  refine ⟨by rw [hng]; decide +kernel, fun j hj => ?_⟩
  rw [hng] at hj
  exact arrBind_sound (bG j hj)

theorem pG : ∀ k < E.ng, permB 315 9 (E.G k) = true := fun k hk => by
  have h := allN_spec comm k hk
  rw [Bool.and_eq_true] at h
  exact h.1

theorem hkeys : j2ThreeKeys = j2ThreeBaseArr.toList := by decide +kernel

theorem enumC : enumOK 315 j2ThreeGens j2ThreeBaseArr.toList
      (enumBfs 315 j2ThreeGens j2ThreeBaseArr.toList 1100) = true ∧
    (enumBfs 315 j2ThreeGens j2ThreeBaseArr.toList 1100).pts.size = E.N ∧
    ∀ i < E.N, (enumBfs 315 j2ThreeGens j2ThreeBaseArr.toList 1100).pts[i]! =
      unpack 315 9 (E.T i) :=
  enum_of bindG pG E.ok (mem_base_lt binds C.hl) E.keys (by rw [hN]; omega)

theorem cert_eq : j2ThreeCert () = enumBfs 315 j2ThreeGens j2ThreeBaseArr.toList 1100 := by
  rw [j2ThreeCert, hkeys]

theorem hNS : 315 ≤ C.NS * 63 := by decide +kernel

theorem hW : CFSG.Sporadic.Schreier.Co3.Native.wordsArr 2 9 d = j2ThreeWords := by
  decide +kernel

#kc_forall_chunks clsAll (fun b => clsBlock b = true) 18
  CertificateChecks.KernelGFR3.J2.clsBlock 1

theorem cls : ∀ i < 1080, gfr3AtK 315 9 1080 E.T 1080 3 1 i = true := by
  intro i hi
  have hr : i % 60 < 60 := Nat.mod_lt _ (by norm_num)
  have hb : i / 60 < 18 := by omega
  have e : i = Nat.add (Nat.mul 60 (i / 60)) (i % 60) := by
    change i = 60 * (i / 60) + i % 60
    omega
  have h := clsAll (i / 60) hb
  unfold clsBlock at h
  rw [e]
  exact allN_spec h _ hr

theorem j2_ok : j2ThreeCheck () = true := by
  have hx : j2ThreeGens[0]! = unpack 315 9 (E.G 0) := bindG.2 0 (by rw [hng]; norm_num)
  have hx1 : Nat.beq (E.G 0) (pidn 315 9) = false := by
    have := x0.2.2
    rwa [Bool.not_eq_true'] at this
  have hPS : ∀ j < 9, permB 315 9 (C.S j) = true := fun j hj =>
    permB_of_pp (pp_of_permOK szOK' (allN_spec perm j hj))
  have hchain := rawChainK_sound (chunks := 1) binds C.head C.hl hNS C.hs
  rw [hW] at hchain
  have hS0 : j2ThreeArrs[0]! = unpack 315 9 (C.S 0) := binds.2.2.2.2.1 0 (by norm_num)
  have hS1 : j2ThreeArrs[1]! = unpack 315 9 (C.S 1) := binds.2.2.2.2.1 1 (by norm_num)
  obtain ⟨he1, he2, he3⟩ := enumC
  have hTp : ∀ i < E.N, permB 315 9 (E.T i) = true := allN_spec E.perm
  have hcent := centOKP_of_orbS (p := 3) szOK' binds perm C.hl (k := 2)
    (by simp [j2ThreeArrs]) (by decide +kernel) (by norm_num) hchain x0.1 rels bindG comm
    (fun j hj => siftA_of binds perm C.hl (siftG j (by rw [hng] at hj; exact hj)))
    (mem_base_lt binds C.hl) he1 he2 he3 hTp (by norm_num) (NR := 1) (RB := RB) (RI := RI)
    (EK := EK) (fun j hj => by
      obtain rfl : j = 0 := by omega
      exact rep0) (by rw [Nat.eq_of_beq_eq_true rc]; exact allN_spec kOrb)
  rw [hN] at hcent
  have hcls := gfr3ClassOK_of szOK' he2 he3 hTp (Nc := 1080) (e := 3) (f := 1)
    (fun i hi => cls i (by rw [← hN]; exact hi))
  have horb := rawOrbitSizesK_sound binds perm C.hl
  rw [orb] at horb
  unfold j2ThreeCheck
  rw [cert_eq, hkeys, hx, hA, hB, validA_of pAB.1, validA_of pAB.2, caseChainOK2P, hchain, hS0, hS1,
    eqA_unpack' szOK' (hPS 0 (by norm_num)) pAB.1, eqA_unpack' szOK' (hPS 1 (by norm_num)) pAB.2,
    head.1, head.2, horb, hcent, powEq_id szOK' x0.1, x0.2.1, eqA_id szOK' x0.1, hx1, hcls]
  rfl

end CertificateChecks.KernelGFR3.J2

end
