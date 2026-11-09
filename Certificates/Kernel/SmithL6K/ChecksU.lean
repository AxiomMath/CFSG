module

public import Certificates.Data.Kernel.SmithL6KU
public import Certificates.Kernel.SmithL6K.Data
public import Certificates.Kernel.SmithL6K.DataO

public section

namespace CertificateChecks.KernelSmithL6K

open CFSG.SmithL6 CFSG.SmithL6.K

theorem ua_gens_ok : ugens.toList.all (fun g => decide (g < 1953) && p0.contains g) = true := by
  decide +kernel

theorem ua_uco_ok : ((List.range 49).all fun k => decide (0 < uco[k]!) && decide (uco[k]! < 512) &&
    (List.range k).all fun l => uco[l]! != uco[k]!) = true := by
  decide +kernel

theorem ua_slices_ok : ∀ k < 49, (((uaRC tvc p0).drop (7 * (k / 7))).take 7).contains
    (uco[k]!, tvc.getD (p0.getD k 0) 0) = true := by
  decide +kernel

theorem ua_fix_ok : uaFixC tvc p0 = true := by decide +kernel

theorem ua_move_ok : uaMoveC (ugC tvc) tvc = true := by decide +kernel

theorem ua_comm_ok : uaCommC tvc p0 = true := by decide +kernel

theorem all_range_getD_of_drop {W : List Nat} {n : Nat} (hn : n ≤ W.length) {h : Nat → Bool}
    (hW : (W.drop 1).all h = true) :
    ((List.range n).all fun j => j == 0 || h (W.getD j 0)) = true := by
  rw [List.all_eq_true]
  intro j hj
  rw [List.mem_range] at hj
  cases j with
  | zero => rfl
  | succ k =>
    have hk : k < (W.drop 1).length := by rw [List.length_drop]; omega
    have hm := List.all_eq_true.1 hW _ (List.getElem_mem hk)
    rw [List.getElem_drop] at hm
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by omega : k + 1 < W.length)]
    simp only [Nat.add_comm 1 k] at hm
    simp [hm]

theorem ua_wtd_len : 1395 ≤ wtd.length := by decide +kernel

open CFSG.SmithL6.CollK in
theorem ua_planes_w :
    (wtd.drop 1).all (fun x => (p0.map (tcl.getD · [])).any fun L => apK L x != x) = true := by
  decide +kernel

open CFSG.SmithL6.CollK in
theorem ua_planes_ok : uaPlanesK (p0.map (tcl.getD · [])) wtd = true := by
  unfold uaPlanesK
  exact all_range_getD_of_drop (h := fun x => (p0.map (tcl.getD · [])).any fun L => apK L x != x)
    ua_wtd_len ua_planes_w

end CertificateChecks.KernelSmithL6K
