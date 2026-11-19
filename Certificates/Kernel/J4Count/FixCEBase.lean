
module

public import CFSG.Certificates.Kernel.J4FixCESound
public import Certificates.Kernel.J4Count.FixCEChecks
public import Certificates.Kernel.J4Count.FixCEEltBase
public import Certificates.Kernel.J4Count.SuborbBase

@[expose] public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelJ4Count.FixCE

open CFSG.Sporadic.J4 CFSG.Sporadic.J4Schreier CFSG.Sporadic.J4Schreier.NoComp MulAction
open CFSG.Sporadic.SmallF2 (toVecD)
open CFSG.Sporadic.GLQ CFSG.KC.J4FixCE CFSG.KD.J4FixCE
open CFSG.KC.J4FixC (nth codeL toI walkK letM sN)
open CFSG.KC.J4Q (vecJ mulJ)
open CFSG.KD.J4Q (c rm one A B Bi)
open CertificateChecks.KernelSporSch CertificateChecks.KernelJ4Count
open CFSG.Quasithin.J4M2 (cE)

section Sizes

set_option synthInstance.maxSize 4096 in
theorem sizes_rest : ∀ b ∈ L7, ∀ d ∈ L7, b ≠ 1 → b ≠ 32643072 → b ≠ 3400320 → b ≠ 15180 →
    b ≠ 28336 → d ≠ 1 → d ≠ 32643072 → d ≠ 3400320 → d ≠ 15180 → d ≠ 28336 → b ≠ d →
    d ≠ 82575360 → b = 82575360 ∧ d = 54405120 := by decide

end Sizes

section Fix

end Fix

section Points

noncomputable def ptR (i : ℕ) : Row := toRow (toVecD 112 (nth 0 PTS i))

theorem len_PTS : PTS.length = 737 := Nat.eq_of_beq_eq_true len_ok

theorem pt_spec {i : ℕ} (hi : i < 737) :
    nth 0 PTS i < 2 ^ 112 ∧ vecJ rm (nth 0 PTS i) CMD = nth 0 PTS i :=
  fixAllJ_spec pts_fix _ (by
    rw [CFSG.KC.J4FixC.nth_eq, List.getD_eq_getElem _ _ (by rw [len_PTS]; exact hi)]
    exact List.getElem_mem _)

theorem pt_lt {i : ℕ} (hi : i < 737) : nth 0 PTS i < 2 ^ 112 := (pt_spec hi).1

theorem ptR_zero : ptR 0 = v := by
  rw [ptR, v, Nat.eq_of_beq_eq_true root_pt]

theorem ptR_inj
    {i j : ℕ}
    (hi : i < 737) (hj : j < 737) (h : ptR i = ptR j) : i = j := by
  have e : toVecD 112 (nth 0 PTS i) = toVecD 112 (nth 0 PTS j) := h
  rw [toVecD_eq_iff, Nat.mod_eq_of_lt (pt_lt hi), Nat.mod_eq_of_lt (pt_lt hj)] at e
  have hnd := nodupK_spec pts_nodup
  have hi' : i < PTS.length := by rw [len_PTS]; exact hi
  have hj' : j < PTS.length := by rw [len_PTS]; exact hj
  rw [CFSG.KC.J4FixC.nth_eq, CFSG.KC.J4FixC.nth_eq, List.getD_eq_getElem _ _ hi',
    List.getD_eq_getElem _ _ hj'] at e
  exact (List.Nodup.getElem_inj_iff hnd).1 e

section W77

theorem letM_eq' (k : ℕ) : letM A A B Bi k = if k = 0 then A else if k = 1 then A else if k = 2 then B
    else Bi := by
  rcases k with _ | _ | _ | k <;> rfl

noncomputable abbrev m77 : J := signedWord a b (toI W77)

end W77

section Tree

noncomputable def cg (g : ℕ) : J := gw (nth [] CGW g)

def ptRoot (i : ℕ) : ℕ := if i < 77 then 0 else 77

end Tree

section All

open scoped Classical

noncomputable def ptSet : Finset Row := (Finset.range 737).image ptR

theorem card_ptSet : ptSet.card = 737 := by
  rw [ptSet, Finset.card_image_of_injOn, Finset.card_range]
  intro i hi j hj h
  exact ptR_inj (Finset.mem_range.1 hi) (Finset.mem_range.1 hj) h

theorem card_eq_orbit_mul_stab' :
    Nat.card ↥(Subgroup.centralizer ({cE} : Set J)) =
      (orbit ↥(Subgroup.centralizer ({cE} : Set J)) v).ncard *
        Nat.card ↥(stabilizer ↥(Subgroup.centralizer ({cE} : Set J)) v) := by
  have h := Subgroup.card_mul_index (stabilizer ↥(Subgroup.centralizer ({cE} : Set J)) v)
  rw [index_stabilizer] at h
  rw [← h, mul_comm]

end All

end Points

end CertificateChecks.KernelJ4Count.FixCE

end
