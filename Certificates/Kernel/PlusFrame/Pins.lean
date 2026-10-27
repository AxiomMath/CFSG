module

public import CFSG.OddTranspositions.PartThree.Eleven.Plus.FrameCheck
public import Certificates.Kernel.LocalComp.BfsGenSl
public import Certificates.Kernel.SporSch.Th.GenV4
public import Certificates.Kernel.Sporadic.RawGen
public meta import CFSG.OddTranspositions.PartThree.Eleven.Plus.FrameCheck
public meta import Certificates.Kernel.PlusFactors.Data
meta import Certificates.Kernel.Sporadic.RawGen
public import Certificates.Kernel.PlusFactors.Data

public section

namespace CertificateChecks.KernelPlusFr

open CFSG.OddTranspositions.PartThree.PlusFrame

meta def t0L : List (Array Nat) := t0Gens.toList

meta def oL0 : List (Array Nat) := (otherRows 0).toList
meta def oL1 : List (Array Nat) := (otherRows 1).toList
meta def oL2 : List (Array Nat) := (otherRows 2).toList
meta def oL3 : List (Array Nat) := (otherRows 3).toList

meta def kt : List Nat := CertificateChecks.KernelPlusF.keyOrder t0L
meta def kc0 : List Nat := CertificateChecks.KernelPlusF.keyOrder oL0
meta def kc1 : List Nat := CertificateChecks.KernelPlusF.keyOrder oL1
meta def kc2 : List Nat := CertificateChecks.KernelPlusF.keyOrder oL2
meta def kc3 : List Nat := CertificateChecks.KernelPlusF.keyOrder oL3

end CertificateChecks.KernelPlusFr

end

set_option maxRecDepth 400000

#lc_bfs CertificateChecks.KernelPlusFr.PT CertificateChecks.KernelPlusFr.t0L 60 6
#lc_bfs CertificateChecks.KernelPlusFr.PC0 CertificateChecks.KernelPlusFr.oL0 60 6
#lc_bfs CertificateChecks.KernelPlusFr.PC1 CertificateChecks.KernelPlusFr.oL1 60 6
#lc_bfs CertificateChecks.KernelPlusFr.PC2 CertificateChecks.KernelPlusFr.oL2 60 6
#lc_bfs CertificateChecks.KernelPlusFr.PC3 CertificateChecks.KernelPlusFr.oL3 60 6

#kss_natlist CertificateChecks.KernelPlusFr.KT CertificateChecks.KernelPlusFr.kt
#kss_natlist CertificateChecks.KernelPlusFr.KC0 CertificateChecks.KernelPlusFr.kc0
#kss_natlist CertificateChecks.KernelPlusFr.KC1 CertificateChecks.KernelPlusFr.kc1
#kss_natlist CertificateChecks.KernelPlusFr.KC2 CertificateChecks.KernelPlusFr.kc2
#kss_natlist CertificateChecks.KernelPlusFr.KC3 CertificateChecks.KernelPlusFr.kc3
