
module

public import Certificates.Kernel.HN3166.Ord
public import CFSG.Sporadic.Presentation.HNInputs
public import CFSG.Sporadic.HNBase
public import CFSG.Sporadic.Bridge.TableSurj
public import CFSG.Sporadic.Presentation.HN
public import Certificates.Data.CFSGNative.Bridge.HNGPL
public import TauCeti.GroupTheory.SpecificGroups.CFSG.Sporadic.Presentation
import all TauCeti.GroupTheory.SpecificGroups.CFSG.Sporadic.Presentation
public import CFSG.Assembly.OrderReductions.InvertedSubgroup
public import CFSG.Assembly.OrderReductions.OddInversion
public import CFSG.Certificates.CosetTableShort
public import CFSG.Certificates.NativeSchreierCard
public import CFSG.GroupTheory.LocalCores.Fitting
public import CFSG.Sporadic.HN.CertificateBase
public import CFSG.Sporadic.HN.F5Chain
public import CFSG.Sporadic.Presentation.Common
public import CFSG.Sporadic.Recognition.CoverChainSub

@[expose] public section

namespace CertificateChecks.KernelHN

open CFSG.Sporadic.F5

local notation "Dt" => CFSG.Sporadic.HN.Native.hnData

private theorem presentation_eq :
    TauCeti.SporadicName.HN.presentation = TauCeti.Sporadic.hnPresentation := rfl

end CertificateChecks.KernelHN

end
