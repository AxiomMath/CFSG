module

public import Certificates.Kernel.J4M4.Defs
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelJ4M4

open CFSG.KC.J4M4 CFSG.KC.J4Tree CFSG.KC.F2W CFSG.J4Tree.Native CFSG.J4Tree.Native.Node
open CFSG.J4Tree.M4

theorem x_wf : xCode.toList.all Code.wf = true := by quickRfl
theorem xi_wf : xiCode.toList.all Code.wf = true := by quickRfl
theorem u_wf : uCode.toList.all Code.wf = true := by quickRfl
theorem k_wf : kCode.toList.all Code.wf = true := by quickRfl

theorem inv_k : ((kGens.map cc).zip KGI).all
    (fun p => eqL p.1.inv.rows.toList (fieldsL p.2)) = true := by
  simp only [Code.inv, Id.run, Std.Legacy.Range.forIn_eq_forIn_range',
    List.forIn_pure_yield_eq_foldl, Std.Legacy.Range.size, Nat.sub_zero, Nat.add_sub_cancel,
    Nat.div_one]
  decide +kernel

theorem inv_g : eqL (codeOfWord gWord).inv.rows.toList (fieldsL GCI) = true := by
  simp only [Code.inv, Id.run, Std.Legacy.Range.forIn_eq_forIn_range',
    List.forIn_pure_yield_eq_foldl, Std.Legacy.Range.size, Nat.sub_zero, Nat.add_sub_cancel,
    Nat.div_one]
  decide +kernel

theorem len_k : KGI.length = 10 ∧ kGens.length = 10 := by decide +kernel

theorem len_ky : KY.length = 11 := by decide +kernel

theorem len_ir : IR.length ≤ 256 * 12 ∧ CL.length ≤ 64 * 7 := by decide +kernel

theorem pairs_k : (List.range 10).all
    (fun s => eqC (mulW 12 (KG.getD s 0) (KGI.getD s 0)) oneK) = true := by decide +kernel

theorem coords_k : (treeOrd 539 == 16384 && coordsOK kGens && coordsOK fBasis &&
    coordsOK (treeWv 539) && coordsOK (treeBasis 539) && coordsOK y136 && coordsOK y266 &&
    coordsOK [h136, h266] && coordsOK (treeWv 136) && coordsOK (treeWv 266)) = true := by
  decide +kernel

theorem lens_k : (treeWv 539).length = 4 ∧ (treeBasis 539).length = 4 ∧ y136.length = 4 ∧
    y266.length = 4 := by decide +kernel

@[expose] noncomputable def gcK : Nat := wordCK (tblC xCode) (tblC xiCode) gWord

theorem node_k : ((treeBasis 539).all (fun ce => WL.contains (ccK ce)) &&
    (treeWv 539).all (fun ce => RL.contains (ccK ce)) &&
    kGens.all (fun k => (treeWv 539).all fun w =>
      eqC (mulW 12 (ccK k) (ccK w)) (mulW 12 (ccK w) (ccK k))) &&
    fBasis.all (fun f => KL.contains (ccK f)) &&
    fBasis.all (fun f => !eqC (ccK f) oneK) &&
    fBasis.all (fun f => eqC (mulW 12 (ccK f) (ccK f)) oneK &&
      IR.any (fun r => Nat.beq r.1 (ccK f) && Nat.beq (CL.getD r.2.1 []).length 4)) &&
    eqC (mulW 12 gcK GCI) oneK &&
    fBasis.all (fun b => FL.contains (mulW 12 (mulW 12 gcK (ccK b)) GCI)) &&
    (treeWv 539).any (fun w => WL.all fun k => !eqC k (mulW 12 (mulW 12 gcK (ccK w)) GCI)) &&
    sextMasks.all (fun c => WL.contains (etaCK (tblC uCode) c))) = true := by
  decide +kernel

theorem h_k : (y136.all (fun y => eqC (mulW 12 (ccK h136) (ccK y)) (mulW 12 (ccK y) (ccK h136))) &&
    (treeWv 136).any (fun w => !eqC (mulW 12 (ccK h136) (ccK w)) (mulW 12 (ccK w) (ccK h136))) &&
    y266.all (fun y => eqC (mulW 12 (ccK h266) (ccK y)) (mulW 12 (ccK y) (ccK h266))) &&
    (treeWv 266).any (fun w => !eqC (mulW 12 (ccK h266) (ccK w)) (mulW 12 (ccK w) (ccK h266)))) =
    true := by
  decide +kernel

theorem y_k : (Nat.beq y136.length yin136.length &&
    (List.range y136.length).all (fun i =>
      eqC (ccK (y136.getD i (0, 0))) (maskK (treeWv 136) (yin136.getD i 0)) &&
        o136.contains (yin136.getD i 0)) &&
    o136.all (fun o => Y1L.contains (maskK (treeWv 136) o)) &&
    Nat.beq y266.length yin266.length &&
    (List.range y266.length).all (fun i =>
      eqC (ccK (y266.getD i (0, 0))) (maskK (treeWv 266) (yin266.getD i 0)) &&
        o266.contains (yin266.getD i 0)) &&
    o266.all (fun o => Y2L.contains (maskK (treeWv 266) o))) = true := by
  decide +kernel

end CertificateChecks.KernelJ4M4
