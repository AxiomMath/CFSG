module

public import Certificates.Kernel.OmegaEight.SB3871C4
public import Certificates.Kernel.OmegaEight.SB3872Data
public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.SpBranchT1Data

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelO8.SB3872

open CFSG.KC.Enum CFSG.KC.SB CFSG.EvenSmallLie.OmegaEight.SpBranch CertificateChecks.KernelO8.SB3871

@[expose] def oLit : List ℕ :=
  oRowsN.flatMap fun r => (List.range 128).map fun k => r / 2 ^ (16 * k) % 2 ^ 16

theorem ys_fun (D : AutData) (mul : ℕ → ℕ → ℕ) (k : ℕ) (ds : List ℕ) :
    D.ys mul k ds = fun l => mul (D.h k l) (D.K.lin (ds.getD l 0)) := rfl

theorem chiS_size (N : ℕ) : (chiS N).size = N := Array.size_ofFn

theorem chiS_get (N x : ℕ) : (chiS N)[x]! = (decide (x < N) && (nfEK (x % 65536)).testBit 1) := by
  by_cases hx : x < N
  · rw [getElem!_pos (chiS N) x (by simpa [chiS] using hx)]
    simp [chiS, sAutData, sNfTab_get, hx]
  · rw [getElem!_neg (chiS N) x (by simpa [chiS] using hx)]
    simp [hx]

theorem fpArr_get (x : ℕ) : fpArr[x]! = (decide (x < 65536) && fpList.contains x) := by
  by_cases hx : x < 65536
  · rw [getElem!_pos fpArr x (by simpa [fpArr] using hx)]
    simp [fpArr, hx]
  · rw [getElem!_neg fpArr x (by simpa [fpArr] using hx)]
    simp [hx]

set_option maxHeartbeats 0 in
theorem fpList_eq : fpList = fpLit := by
  unfold fpList sFm sLeaves
  simp only [sMul_eqK, sAutData, sNfTab_get]
  decide +kernel

theorem kInv_eq : kInv mulK 65536 = sInvListLit := by
  rw [← sMul_eqK]
  exact sInvList_eq

set_option maxHeartbeats 0 in
theorem kOrd4_eq : kOrd4 mulK 65536 = oLit := by
  decide +kernel

@[expose] def zListW (F : ℕ → ℕ) (FF : List ℕ) : List ℕ :=
  (List.range 65536).filter fun z =>
    ((List.range sGens.length).all fun j => sMul z (sGens.getD j 0) == sMul (FF.getD j 0) z) &&
      F z == z

@[expose] def ffL (k m : ℕ) : List ℕ := (ffLit.getD k []).getD m []

@[expose] def zL (k m : ℕ) : List ℕ := (zLit.getD k []).getD m []

@[expose] def zAt (k m : ℕ) : Bool :=
  if sFixE (sFm k m) then zL k m == [] else
    (sGens.map fun g => sFm k m (sFm k m g)) == ffL k m && zListW (sFm k m) (ffL k m) == zL k m

@[expose] def zOK (k : ℕ) : Bool := (List.range (sLeaves k).length).all (zAt k)

@[expose] def candsL : List (ℕ × ℕ × ℕ) :=
  (List.range 8).flatMap fun k => (List.range (sLeaves k).length).flatMap fun m =>
    (zL k m).map fun z => (k, m, z)

theorem t1Cands_eq (h : ∀ k < 8, zOK k = true) : t1Cands = candsL := by
  unfold t1Cands candsL
  refine List.flatMap_congr fun k hk => List.flatMap_congr fun m hm => ?_
  have hz := List.all_eq_true.1 (h k (List.mem_range.1 hk)) m hm
  unfold zAt at hz
  split
  · next hf =>
    rw [ite_eq_left hf, beq_iff_eq] at hz
    rw [hz, List.map_nil]
  · next hf =>
    rw [ite_eq_right hf, Bool.and_eq_true, beq_iff_eq, beq_iff_eq] at hz
    change (zListW (sFm k m) (sGens.map fun g => sFm k m (sFm k m g))).map _ = _
    rw [hz.1, hz.2]

end CertificateChecks.KernelO8.SB3872

end
