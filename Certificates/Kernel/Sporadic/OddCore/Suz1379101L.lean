module

public import Certificates.Kernel.Sporadic.OddCore.Suz1379101I
import CFSG.Certificates.Kernel.Spor.RawOrbEval
public import Certificates.Kernel.Sporadic.OddCore.Suz1379101H

public section

namespace CertificateChecks.KernelSpor.S1379101

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KS.PEnum
open CFSG.Sporadic.SuzOddCore.SylowFacts CFSG.PSL3Four.Native CFSG.Monster.B.Co2.Native
open CFSG.Certificates.Native

theorem filt_ofFn {α : Type} (n : Nat) (f : Nat → α) (p : α → Bool) (q : Nat → Bool)
    (h : ∀ x < n, p (f x) = q x) :
    (Array.ofFn (n := n) fun i => f i.val).filter p = (((List.range n).filter q).map f).toArray := by
  apply Array.toList_inj.1
  rw [Array.toList_filter, Array.toList_ofFn, ofFn_range n f, List.filter_map, List.toList_toArray]
  congr 1
  apply List.filter_congr
  intro x hx
  exact h x (List.mem_range.1 hx)

theorem tabs_rec (cnt : Nat) (T PL : Nat → Nat) :
    (penumRec 1782 11 cnt T PL).tabs = Array.ofFn (n := cnt) fun i => unpack 1782 11 (T i.val) :=
  rfl

theorem zIdx_def : zIdx = (List.range 64).filter fun i => zc (N3T i) := rfl

theorem zTabs_eq : zTabs () = (zIdx.map fun x => unpack 1782 11 (N3T x)).toArray := by
  unfold zTabs zFilter
  rw [enc3.1, tabs_rec, zIdx_def]
  exact filt_ofFn 64 (fun x => unpack 1782 11 (N3T x)) (n3Commutes (n3Arrs ()))
    (fun x => zc (N3T x)) fun x hx => comm_eq hx

theorem zCheck_ok : zCheck (zTabs ()) = true := by
  obtain ⟨hl, hz⟩ := kz_parts
  have hs : (zIdx.map fun x => unpack 1782 11 (N3T x)).toArray.size = 16 := by
    rw [List.size_toArray, List.length_map, hl]
  unfold zCheck
  rw [zTabs_eq, hs, Bool.and_eq_true]
  refine ⟨beq_self_eq_true _, allB fun k hk => ?_⟩
  have hk' : k < zIdx.length := by rw [hl]; exact hk
  have hm : zIdx[k] ∈ zIdx := List.getElem_mem hk'
  have hr : ∀ i ∈ zIdx, i < 64 := by
    intro i hi
    rw [zIdx_def] at hi
    exact List.mem_range.1 (List.mem_filter.1 hi).1
  have h64 : zIdx[k] < 64 := hr _ hm
  have cx : Cn (N3T zIdx[k]) := CFSG.KS.Raw.Orb.allN_iff.1 c3T _ h64
  rw [getElem!_pos _ k (by rw [hs]; exact hk), List.getElem_toArray, List.getElem_map,
    comp_u cx cx, hz _ hm, ← idT]
  exact beq_self_eq_true _

theorem check1379101 : sylowFactsCheck () = true := by
  unfold sylowFactsCheck
  dsimp only
  rw [rCheck_ok, n2Check_ok, n3Check_ok, zCheck_ok, qCheck_ok, genCheck_ok]
  simp only [Bool.and_true]
  exact wordOK_all

end CertificateChecks.KernelSpor.S1379101

end
