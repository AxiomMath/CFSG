module

public import Certificates.Data.Kernel.Local3K
public import Certificates.Kernel.LocalComp.M1Gen
public import Certificates.Kernel.Local3.Masks
import all CFSG.Blueprint.NativeSporadic
meta import Certificates.Kernel.Local3.Masks
public import CFSG.Certificates.CosetTableShort
public import CFSG.Certificates.NativeSchreierCard
public import CFSG.GroupTheory.LocalCores.Fitting
public import CFSG.Open.Defs
meta import CFSG.Certificates.CosetTableShort
meta import CFSG.Certificates.NativeSchreierCard
meta import CFSG.GroupTheory.LocalCores.Fitting
meta import CFSG.Open.Defs

set_option maxRecDepth 400000

public section

namespace CertificateChecks.KernelLocal3.Co3

@[expose] def masks₁ : String :=
  "7777777375777676673736276037075767775217411172274275253561640105337162675364727075444700\
    3431061206040032713021200311250025000022040252022000200002040000600401112014040040213022\
    1410000000002040000400000000000000004"

@[expose] def masks₂ : String :=
  "7777777767677777567676627646776566766327746665667646576462663226254005454474432746274463\
    5004304702625442046446643022540044547402222260354304050004600274200601000042110400210000\
    0000002000020444060005020202142044000007400201000140000000020000200000000000000000000000\
    040004"

@[expose] def kw : List (List (Fin 3 × Bool)) := [
  [(0, true), (1, true), (2, true), (2, true)],
  [(1, true), (2, true), (0, true), (2, true), (2, true), (1, false)],
  [(1, true), (2, true), (2, true), (0, true), (1, false)]]

@[expose] def v₁ : Nat := 1190199

@[expose] def gens : List Nat := [
  29914186884674230873606570237869280402264907976859524417586227859192533910166415440126553244074225736304577685522611991691944315981109638261740993,
  46539416337871675786920294329120894228224292291486383539479202075428218038122181071262578693999765409806806673955242728709774013793881664692180331,
  39441406696568573602611759831397509424420401566550125174260717113544795747356511394231082980907821051061988712532018530440690324271242729318701546]

end CertificateChecks.KernelLocal3.Co3

#ks_chars CertificateChecks.KernelLocal3.Co3.SA CFSG.Blueprint.NativeSporadic.Co3Seed1
#lc_m1 CertificateChecks.KernelLocal3.Co3.SA CFSG.Blueprint.NativeSporadic.Co3Seed1 22
#ks_chars CertificateChecks.KernelLocal3.Co3.SB CFSG.Blueprint.NativeSporadic.Co3Seed2
#lc_m1 CertificateChecks.KernelLocal3.Co3.SB CFSG.Blueprint.NativeSporadic.Co3Seed2 22
#ks_chars CertificateChecks.KernelLocal3.Co3.M1 CertificateChecks.KernelLocal3.Co3.masks₁
#ks_chars CertificateChecks.KernelLocal3.Co3.M2 CertificateChecks.KernelLocal3.Co3.masks₂
#ks_chars CertificateChecks.KernelLocal3.Co3.MS CertificateChecks.KernelLocal3.co3Masks

namespace CertificateChecks.KernelLocal3.Co3

open CFSG.KC.Local3K CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.Coordinator

theorem gens_eq : gensK 22 SA.M SB.M co3Local3 = gens := by
  decide +kernel

theorem local3_K :
    local3K3 22 SA.M SB.M co3Local3 gens M1.chars M2.chars v₁ co3Root 243 288 kw = true := by
  decide +kernel

theorem local3_neg :
    (!local3K 22 SA.M SB.M MS.chars { co3Local3 with ords := [4, 4, 4] } co3Root) = true := by
  decide +kernel

end CertificateChecks.KernelLocal3.Co3

end
