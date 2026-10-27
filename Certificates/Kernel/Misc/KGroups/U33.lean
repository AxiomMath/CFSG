module

public import Certificates.Kernel.Misc.KGroups.U33AFacts
public import Certificates.Kernel.Misc.KGroups.U33Valid
public import Mathlib
public import CFSG.GH74.KGroups.Generic
public import CFSG.GH74.KGroups.PermCheck
public import CFSG.GH74.KGroups.Checks
public import CFSG.GH74.KGroups.ClassCount
public import CFSG.Blueprint.Catalog
public import CFSG.Quasithin.Recognition.CertU33Psu
public import CFSG.Quasithin.Recognition.CertU33Perm
public import CFSG.Timmesfeld.Final.PSU33
public import CFSG.GH74.KGroups.U33Inputs

public section

namespace CertificateChecks.KernelMisc.U33K

open Certificates in
open CFSG in
open CFSG.GH74 in
open CFSG.GH74.KGroups in
open CFSG.GH74.KGroups.U33 in
open CFSG.Certificates CFSG.Sporadic.Schreier CFSG.Blueprint in
theorem facts : (QP.check = true ∧ QP.orderCertificate = 6048)
    ∧ (QA.check = true ∧ QA.orderCertificate = 12096)
    ∧ (orderOf pu = 2 ∧ orderOf pv = 7 ∧ PairInv wsU pu pv)
    ∧ (pu ∈ Subgroup.closure {pa, pb} ∧ pv ∈ Subgroup.closure {pa, pb} ∧
        pa ∈ Subgroup.closure {pu, pv} ∧ pb ∈ Subgroup.closure {pu, pv})
    ∧ (sg0 * pu * sg0⁻¹ ∈ Subgroup.closure {pa, pb} ∧
        sg0 * pv * sg0⁻¹ ∈ Subgroup.closure {pa, pb})
    ∧ (∀ k : Fin 5, CFSG.Quasithin.u33Img k ∈ Subgroup.closure {pa, pb})
    ∧ Nat.card {x // x ∈ Subgroup.closure {pa, pb} ∧ orderOf x = 2} = 63
    ∧ Nat.card {y // y ∈ Subgroup.closure {pa, pb} ∧ orderOf y = 7 ∧ PairInv wsU pu y} = 192
    ∧ centCard (Subgroup.closure {pa, pb}) pu = 96
    ∧ centCard (Subgroup.closure {pa, pb}) pt2 = 24
    ∧ (pt2 ∈ Subgroup.closure {pa, pb, sg0} ∧ orderOf pt2 = 2)
    ∧ Nat.card {x // x ∈ Subgroup.closure {pa, pb, sg0} ∧ orderOf x = 2} = 315
    ∧ centCard (Subgroup.closure {pa, pb, sg0}) pu = 192
    ∧ centCard (Subgroup.closure {pa, pb, sg0}) pt2 = 48
    ∧ (∀ σ ∈ Subgroup.closure {pa, pb, sg0}, σ * pu = pu * σ → σ * pv = pv * σ → σ = 1)
    ∧ E9At (Subgroup.closure {pa, pb, sg0}) pu
    ∧ E9At (Subgroup.closure {pa, pb, sg0}) pt2
    ∧ (px1 ∈ Subgroup.closure {pa, pb, sg0} ∧ orderOf px1 = 3)
    ∧ (px2 ∈ Subgroup.closure {pa, pb, sg0} ∧ orderOf px2 = 3)
    ∧ Nat.card {x // x ∈ Subgroup.closure {pa, pb, sg0} ∧ orderOf x = 3} = 728
    ∧ centCard (Subgroup.closure {pa, pb, sg0}) px1 = 216
    ∧ centCard (Subgroup.closure {pa, pb, sg0}) px2 = 18
    ∧ E27At (Subgroup.closure {pa, pb, sg0}) px1
    ∧ E27At (Subgroup.closure {pa, pb, sg0}) px2 :=
  ⟨⟨U33PC.valid, U33PC.order⟩, ⟨U33AC.valid, U33AC.order⟩,
    ordUV, ⟨memF.1, memF.2.1, wordF.1, wordF.2⟩, ⟨memF.2.2.1, memF.2.2.2⟩, imgF, c2PF,
    fibPF, cPuF, cPtF, repF.1, c2AF, cAuF, cAtF, centAF, e9uF, e9tF, repF.2.1, repF.2.2, c3AF,
    cA1F, cA2F, e27aF, e27bF⟩

end CertificateChecks.KernelMisc.U33K

end
