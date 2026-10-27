module

public import Certificates.Kernel.HS100.CubeData
public import Certificates.Kernel.HS100.Chain
public import Certificates.Kernel.HS100.Five
public import CFSG.Certificates.Kernel.WordArrSound
public import CFSG.Certificates.Kernel.BfsPinAlg
public import CFSG.Certificates.Kernel.BfsPinBaseSound
public import CFSG.Certificates.Kernel.Misc.ArrBind
public import CFSG.Certificates.Kernel.Misc.ArrEnumUnpack
public import CFSG.Certificates.Kernel.BfsPinSetSound
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelHS100

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KC.BfsPin CFSG.KC.WordArr
open CFSG.KC.Misc.ArrEnum (arrBind_sound)
open CFSG.RankThree.Native CFSG.Monster.B.Co2.Native
open CFSG.ComponentClassification.GrSLit.L34Facts.FourCube
open CFSG.Monster.B.Co2 (allLt_iff)

theorem hw32 : szOK 32 6 = true := by quickRfl

theorem qW {i : ℕ} (hi : i < 5) : hsWit[i]! = unpack 100 7 (QW i) ∧ PP 100 7 (QW i) :=
  ⟨arrBind_sound (allN_spec Cube.bW i hi), PP_of_permOK hw (allN_spec Cube.permW i hi)⟩

theorem qT {i : ℕ} (hi : i < 6) : t32Gens[i]! = unpack 32 6 (QT i) ∧ PP 32 6 (QT i) :=
  ⟨arrBind_sound (allN_spec Cube.bT i hi), PP_of_permOK hw32 (allN_spec Cube.permT i hi)⟩

theorem qO {i : ℕ} (hi : i < 5) : onWit[i]! = unpack 32 6 (QO.G i) ∧ PP 32 6 (QO.G i) := by
  have hwd := wordArr_unpack hw32 (fun j hj => qT hj) (onWitWords.getD i [])
  rw [← Nat.eq_of_beq_eq_true (allN_spec Cube.gensO i hi)] at hwd
  refine ⟨?_, hwd.2⟩
  rw [← hwd.1]
  have hl : i < onWitWords.length := by simpa [onWitWords] using hi
  rw [getElem!_pos onWit i (by simpa [onWit] using hl)]
  simp only [onWit, List.getElem_toArray, List.getElem_map]
  rw [List.getD_eq_getElem _ _ hl]

theorem relsH : (qRels 0).all (fun w => eqA 100 (wordArr 100 hsWit w) (idA 100)) = true := by
  have e : (fun w : List (Fin 5 × Bool) => eqA 100 (wordArr 100 hsWit w) (idA 100)) =
      fun w => Nat.beq (wordFK 100 7 QW w) (pidn 100 7) := by
    funext w
    have h := wordArr_unpack hw (fun j hj => qW hj) w
    rw [h.1, idA_eq hw, eqA_PP h.2 (PP.id hw)]
  rw [e]
  exact Cube.relsH

theorem relsO : (qRels d1).all (fun w => eqA 32 (wordArr 32 onWit w) (idA 32)) = true := by
  have e : (fun w : List (Fin 5 × Bool) => eqA 32 (wordArr 32 onWit w) (idA 32)) =
      fun w => Nat.beq (wordFK 32 6 QO.G w) (pidn 32 6) := by
    funext w
    have h := wordArr_unpack hw32 (fun j hj => qO hj) w
    rw [h.1, idA_eq hw32, eqA_PP h.2 (PP.id hw32)]
  rw [e]
  exact Cube.relsO

theorem qh_gens : hsWit.size = QH.ng ∧ ∀ k < QH.ng, hsWit[k]! = unpack 100 7 (QH.G k) := by
  refine ⟨rfl, fun k hk => ?_⟩
  have hk5 : k < 5 := hk
  rw [Nat.eq_of_beq_eq_true (allN_spec Cube.gensH k hk5)]
  exact (qW hk5).1

theorem qh_perm : ∀ k < QH.ng, permOK 100 7 (mask 7) (100 * 7) (QH.G k)
    (pinvS 100 7 (mask 7) (QH.G k)) = true := by
  intro k hk
  have hk5 : k < 5 := hk
  rw [Nat.eq_of_beq_eq_true (allN_spec Cube.gensH k hk5)]
  exact allN_spec Cube.permW k hk5

theorem qo_gens : onWit.size = QO.ng ∧ ∀ k < QO.ng, onWit[k]! = unpack 32 6 (QO.G k) :=
  ⟨by simp [onWit, onWitWords, QO.ng], fun k hk => (qO hk).1⟩

theorem qo_perm : ∀ k < QO.ng, permOK 32 6 (mask 6) (32 * 6) (QO.G k)
    (pinvS 32 6 (mask 6) (QO.G k)) = true :=
  fun k hk => CFSG.KC.Misc.ArrEnum.permB_of_pp (qO hk).2

theorem hsK : CFSG.ComponentClassification.GrSLit.L34Facts.FourCube.hsKeys = [0, 1, 2, 3, 4] := rfl

theorem hsWit_ok : hsWitOK = true := by
  have hs := Cube.sizes
  rw [Bool.and_eq_true] at hs
  unfold hsWitOK
  dsimp only
  have hv : allLt 5 (fun i => validA 100 hsWit[i]!) = true := allLt_iff.2 fun i hi => by
    rw [(qW hi).1]
    exact validA_unpack (allN_spec Cube.permW i hi)
  have hsf : allLt 5 (fun i => siftA 100 hs100PLevels hs100BaseArr 0 hsWit[i]!) = true :=
    allLt_iff.2 fun i hi => siftP (qW hi).1 (allN_spec Cube.sift i hi)
  rw [hv, hsf, relsH, hsK,
    enumOK_of_bfsK_base qh_gens.1 qh_gens.2 qh_perm QH.ok (by decide) QH.keys (by decide),
    enumBfs_pts_base qh_gens.1 qh_gens.2 QH.ok (by decide) QH.keys (by decide), Array.size_ofFn,
    Nat.eq_of_beq_eq_true hs.1]
  rfl

theorem onWit_ok : onWitOK = true := by
  have hs := Cube.sizes
  rw [Bool.and_eq_true] at hs
  unfold onWitOK
  dsimp only
  have hv : allLt 6 (fun j => validA 32 t32Gens[j]!) = true := allLt_iff.2 fun j hj => by
    rw [(qT hj).1]
    exact validA_unpack (allN_spec Cube.permT j hj)
  have hv' : allLt 5 (fun i => validA 32 onWit[i]!) = true := allLt_iff.2 fun i hi => by
    rw [(qO hi).1]
    exact validA_unpack (CFSG.KC.Misc.ArrEnum.permB_of_pp (qO hi).2)
  have hk : onKeys = [0, 5, 1] := rfl
  rw [hv, hv', relsO, hk,
    enumOK_of_bfsK_base qo_gens.1 qo_gens.2 qo_perm QO.ok (by decide) QO.keys (by decide),
    enumBfs_pts_base qo_gens.1 qo_gens.2 QO.ok (by decide) QO.keys (by decide), Array.size_ofFn,
    Nat.eq_of_beq_eq_true hs.2, qo_gens.1]
  rfl

theorem fourCube : fourCubeWitOK = true := by
  unfold fourCubeWitOK
  rw [hsWit_ok, onWit_ok]
  rfl

end CertificateChecks.KernelHS100

end
